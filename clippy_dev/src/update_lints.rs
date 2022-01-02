use itertools::Itertools;
use regex::Regex;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs;
use std::lazy::SyncLazy;
use std::path::Path;
use walkdir::WalkDir;

use crate::clippy_project_root;

const GENERATED_FILE_COMMENT: &str = "// This file was generated by `cargo dev update_lints`.\n\
     // Use that command to update this file and do not edit by hand.\n\
     // Manual edits will be overwritten.\n\n";

static DEC_CLIPPY_LINT_RE: SyncLazy<Regex> = SyncLazy::new(|| {
    Regex::new(
        r#"(?x)
    declare_clippy_lint!\s*[\{(]
    (?:\s+///.*)*
    (?:\s*\#\[clippy::version\s*=\s*"[^"]*"\])?
    \s+pub\s+(?P<name>[A-Z_][A-Z_0-9]*)\s*,\s*
    (?P<cat>[a-z_]+)\s*,\s*
    "(?P<desc>(?:[^"\\]+|\\(?s).(?-s))*)"\s*[})]
"#,
    )
    .unwrap()
});

static DEC_DEPRECATED_LINT_RE: SyncLazy<Regex> = SyncLazy::new(|| {
    Regex::new(
        r#"(?x)
    declare_deprecated_lint!\s*[{(]\s*
    (?:\s+///.*)*
    (?:\s*\#\[clippy::version\s*=\s*"[^"]*"\])?
    \s+pub\s+(?P<name>[A-Z_][A-Z_0-9]*)\s*,\s*
    "(?P<desc>(?:[^"\\]+|\\(?s).(?-s))*)"\s*[})]
"#,
    )
    .unwrap()
});
static NL_ESCAPE_RE: SyncLazy<Regex> = SyncLazy::new(|| Regex::new(r#"\\\n\s*"#).unwrap());

static DOCS_LINK: &str = "https://rust-lang.github.io/rust-clippy/master/index.html";

#[derive(Clone, Copy, PartialEq)]
pub enum UpdateMode {
    Check,
    Change,
}

/// Runs the `update_lints` command.
///
/// This updates various generated values from the lint source code.
///
/// `update_mode` indicates if the files should be updated or if updates should be checked for.
///
/// # Panics
///
/// Panics if a file path could not read from or then written to
#[allow(clippy::too_many_lines)]
pub fn run(update_mode: UpdateMode) {
    let lint_list: Vec<Lint> = gather_all().collect();

    let internal_lints = Lint::internal_lints(&lint_list);
    let deprecated_lints = Lint::deprecated_lints(&lint_list);
    let usable_lints = Lint::usable_lints(&lint_list);
    let mut sorted_usable_lints = usable_lints.clone();
    sorted_usable_lints.sort_by_key(|lint| lint.name.clone());

    let usable_lint_count = round_to_fifty(usable_lints.len());

    let mut file_change = false;

    file_change |= replace_region_in_file(
        Path::new("README.md"),
        &format!(
            r#"\[There are over \d+ lints included in this crate!\]\({}\)"#,
            DOCS_LINK
        ),
        "",
        true,
        update_mode == UpdateMode::Change,
        || {
            vec![format!(
                "[There are over {} lints included in this crate!]({})",
                usable_lint_count, DOCS_LINK
            )]
        },
    )
    .changed;

    file_change |= replace_region_in_file(
        Path::new("CHANGELOG.md"),
        "<!-- begin autogenerated links to lint list -->",
        "<!-- end autogenerated links to lint list -->",
        false,
        update_mode == UpdateMode::Change,
        || gen_changelog_lint_list(usable_lints.iter().chain(deprecated_lints.iter())),
    )
    .changed;

    // This has to be in lib.rs, otherwise rustfmt doesn't work
    file_change |= replace_region_in_file(
        Path::new("clippy_lints/src/lib.rs"),
        "begin lints modules",
        "end lints modules",
        false,
        update_mode == UpdateMode::Change,
        || gen_modules_list(usable_lints.iter()),
    )
    .changed;

    if file_change && update_mode == UpdateMode::Check {
        exit_with_failure();
    }

    process_file(
        "clippy_lints/src/lib.register_lints.rs",
        update_mode,
        &gen_register_lint_list(internal_lints.iter(), usable_lints.iter()),
    );
    process_file(
        "clippy_lints/src/lib.deprecated.rs",
        update_mode,
        &gen_deprecated(deprecated_lints.iter()),
    );

    let all_group_lints = usable_lints.iter().filter(|l| {
        matches!(
            &*l.group,
            "correctness" | "suspicious" | "style" | "complexity" | "perf"
        )
    });
    let content = gen_lint_group_list("all", all_group_lints);
    process_file("clippy_lints/src/lib.register_all.rs", update_mode, &content);

    for (lint_group, lints) in Lint::by_lint_group(usable_lints.into_iter().chain(internal_lints)) {
        let content = gen_lint_group_list(&lint_group, lints.iter());
        process_file(
            &format!("clippy_lints/src/lib.register_{}.rs", lint_group),
            update_mode,
            &content,
        );
    }
}

pub fn print_lints() {
    let lint_list: Vec<Lint> = gather_all().collect();
    let usable_lints = Lint::usable_lints(&lint_list);
    let usable_lint_count = usable_lints.len();
    let grouped_by_lint_group = Lint::by_lint_group(usable_lints.into_iter());

    for (lint_group, mut lints) in grouped_by_lint_group {
        if lint_group == "Deprecated" {
            continue;
        }
        println!("\n## {}", lint_group);

        lints.sort_by_key(|l| l.name.clone());

        for lint in lints {
            println!("* [{}]({}#{}) ({})", lint.name, DOCS_LINK, lint.name, lint.desc);
        }
    }

    println!("there are {} lints", usable_lint_count);
}

fn round_to_fifty(count: usize) -> usize {
    count / 50 * 50
}

fn process_file(path: impl AsRef<Path>, update_mode: UpdateMode, content: &str) {
    if update_mode == UpdateMode::Check {
        let old_content =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("Cannot read from {}: {}", path.as_ref().display(), e));
        if content != old_content {
            exit_with_failure();
        }
    } else {
        fs::write(&path, content.as_bytes())
            .unwrap_or_else(|e| panic!("Cannot write to {}: {}", path.as_ref().display(), e));
    }
}

fn exit_with_failure() {
    println!(
        "Not all lints defined properly. \
                 Please run `cargo dev update_lints` to make sure all lints are defined properly."
    );
    std::process::exit(1);
}

/// Lint data parsed from the Clippy source code.
#[derive(Clone, PartialEq, Debug)]
struct Lint {
    name: String,
    group: String,
    desc: String,
    deprecation: Option<String>,
    module: String,
}

impl Lint {
    #[must_use]
    fn new(name: &str, group: &str, desc: &str, deprecation: Option<&str>, module: &str) -> Self {
        Self {
            name: name.to_lowercase(),
            group: group.to_string(),
            desc: NL_ESCAPE_RE.replace(&desc.replace("\\\"", "\""), "").to_string(),
            deprecation: deprecation.map(ToString::to_string),
            module: module.to_string(),
        }
    }

    /// Returns all non-deprecated lints and non-internal lints
    #[must_use]
    fn usable_lints(lints: &[Self]) -> Vec<Self> {
        lints
            .iter()
            .filter(|l| l.deprecation.is_none() && !l.group.starts_with("internal"))
            .cloned()
            .collect()
    }

    /// Returns all internal lints (not `internal_warn` lints)
    #[must_use]
    fn internal_lints(lints: &[Self]) -> Vec<Self> {
        lints.iter().filter(|l| l.group == "internal").cloned().collect()
    }

    /// Returns all deprecated lints
    #[must_use]
    fn deprecated_lints(lints: &[Self]) -> Vec<Self> {
        lints.iter().filter(|l| l.deprecation.is_some()).cloned().collect()
    }

    /// Returns the lints in a `HashMap`, grouped by the different lint groups
    #[must_use]
    fn by_lint_group(lints: impl Iterator<Item = Self>) -> HashMap<String, Vec<Self>> {
        lints.map(|lint| (lint.group.to_string(), lint)).into_group_map()
    }
}

/// Generates the code for registering a group
fn gen_lint_group_list<'a>(group_name: &str, lints: impl Iterator<Item = &'a Lint>) -> String {
    let mut details: Vec<_> = lints.map(|l| (&l.module, l.name.to_uppercase())).collect();
    details.sort_unstable();

    let mut output = GENERATED_FILE_COMMENT.to_string();

    output.push_str(&format!(
        "store.register_group(true, \"clippy::{0}\", Some(\"clippy_{0}\"), vec![\n",
        group_name
    ));
    for (module, name) in details {
        output.push_str(&format!("    LintId::of({}::{}),\n", module, name));
    }
    output.push_str("])\n");

    output
}

/// Generates the module declarations for `lints`
#[must_use]
fn gen_modules_list<'a>(lints: impl Iterator<Item = &'a Lint>) -> Vec<String> {
    lints
        .map(|l| &l.module)
        .unique()
        .map(|module| format!("mod {};", module))
        .sorted()
        .collect::<Vec<String>>()
}

/// Generates the list of lint links at the bottom of the CHANGELOG
#[must_use]
fn gen_changelog_lint_list<'a>(lints: impl Iterator<Item = &'a Lint>) -> Vec<String> {
    lints
        .sorted_by_key(|l| &l.name)
        .map(|l| format!("[`{}`]: {}#{}", l.name, DOCS_LINK, l.name))
        .collect()
}

/// Generates the `register_removed` code
#[must_use]
fn gen_deprecated<'a>(lints: impl Iterator<Item = &'a Lint>) -> String {
    let mut output = GENERATED_FILE_COMMENT.to_string();
    output.push_str("{\n");
    for Lint { name, deprecation, .. } in lints {
        output.push_str(&format!(
            concat!(
                "    store.register_removed(\n",
                "        \"clippy::{}\",\n",
                "        \"{}\",\n",
                "    );\n"
            ),
            name,
            deprecation.as_ref().expect("`lints` are deprecated")
        ));
    }
    output.push_str("}\n");

    output
}

/// Generates the code for registering lints
#[must_use]
fn gen_register_lint_list<'a>(
    internal_lints: impl Iterator<Item = &'a Lint>,
    usable_lints: impl Iterator<Item = &'a Lint>,
) -> String {
    let mut details: Vec<_> = internal_lints
        .map(|l| (false, l.module.to_string(), l.name.to_uppercase()))
        .chain(usable_lints.map(|l| {
            let name = l.name.to_uppercase();
            let module = format!("{}::{}", &l.module, name);
            (true, module, name)
        }))
        .collect();
    details.sort_unstable();

    let mut output = GENERATED_FILE_COMMENT.to_string();
    output.push_str("store.register_lints(&[\n");

    for (is_public, module_name, lint_name) in details {
        if !is_public {
            output.push_str("    #[cfg(feature = \"internal-lints\")]\n");
        }
        output.push_str(&format!("    {}::{},\n", module_name, lint_name));
    }
    output.push_str("])\n");

    output
}

/// Gathers all files in `src/clippy_lints` and gathers all lints inside
fn gather_all() -> impl Iterator<Item = Lint> {
    lint_files().flat_map(|f| gather_from_file(&f))
}

fn gather_from_file(dir_entry: &walkdir::DirEntry) -> impl Iterator<Item = Lint> {
    let content = fs::read_to_string(dir_entry.path()).unwrap();
    let path = dir_entry.path();
    let filename = path.file_stem().unwrap();
    let path_buf = path.with_file_name(filename);
    let mut rel_path = path_buf
        .strip_prefix(clippy_project_root().join("clippy_lints/src"))
        .expect("only files in `clippy_lints/src` should be looked at");
    // If the lints are stored in mod.rs, we get the module name from
    // the containing directory:
    if filename == "mod" {
        rel_path = rel_path.parent().unwrap();
    }

    let module = rel_path
        .components()
        .map(|c| c.as_os_str().to_str().unwrap())
        .collect::<Vec<_>>()
        .join("::");

    parse_contents(&content, &module)
}

fn parse_contents(content: &str, module: &str) -> impl Iterator<Item = Lint> {
    let lints = DEC_CLIPPY_LINT_RE
        .captures_iter(content)
        .map(|m| Lint::new(&m["name"], &m["cat"], &m["desc"], None, module));
    let deprecated = DEC_DEPRECATED_LINT_RE
        .captures_iter(content)
        .map(|m| Lint::new(&m["name"], "Deprecated", &m["desc"], Some(&m["desc"]), module));
    // Removing the `.collect::<Vec<Lint>>().into_iter()` causes some lifetime issues due to the map
    lints.chain(deprecated).collect::<Vec<Lint>>().into_iter()
}

/// Collects all .rs files in the `clippy_lints/src` directory
fn lint_files() -> impl Iterator<Item = walkdir::DirEntry> {
    // We use `WalkDir` instead of `fs::read_dir` here in order to recurse into subdirectories.
    // Otherwise we would not collect all the lints, for example in `clippy_lints/src/methods/`.
    let path = clippy_project_root().join("clippy_lints/src");
    WalkDir::new(path)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|f| f.path().extension() == Some(OsStr::new("rs")))
}

/// Whether a file has had its text changed or not
#[derive(PartialEq, Debug)]
struct FileChange {
    changed: bool,
    new_lines: String,
}

/// Replaces a region in a file delimited by two lines matching regexes.
///
/// `path` is the relative path to the file on which you want to perform the replacement.
///
/// See `replace_region_in_text` for documentation of the other options.
///
/// # Panics
///
/// Panics if the path could not read or then written
fn replace_region_in_file<F>(
    path: &Path,
    start: &str,
    end: &str,
    replace_start: bool,
    write_back: bool,
    replacements: F,
) -> FileChange
where
    F: FnOnce() -> Vec<String>,
{
    let contents = fs::read_to_string(path).unwrap_or_else(|e| panic!("Cannot read from {}: {}", path.display(), e));
    let file_change = replace_region_in_text(&contents, start, end, replace_start, replacements);

    if write_back {
        if let Err(e) = fs::write(path, file_change.new_lines.as_bytes()) {
            panic!("Cannot write to {}: {}", path.display(), e);
        }
    }
    file_change
}

/// Replaces a region in a text delimited by two lines matching regexes.
///
/// * `text` is the input text on which you want to perform the replacement
/// * `start` is a `&str` that describes the delimiter line before the region you want to replace.
///   As the `&str` will be converted to a `Regex`, this can contain regex syntax, too.
/// * `end` is a `&str` that describes the delimiter line until where the replacement should happen.
///   As the `&str` will be converted to a `Regex`, this can contain regex syntax, too.
/// * If `replace_start` is true, the `start` delimiter line is replaced as well. The `end`
///   delimiter line is never replaced.
/// * `replacements` is a closure that has to return a `Vec<String>` which contains the new text.
///
/// If you want to perform the replacement on files instead of already parsed text,
/// use `replace_region_in_file`.
///
/// # Example
///
/// ```ignore
/// let the_text = "replace_start\nsome text\nthat will be replaced\nreplace_end";
/// let result =
///     replace_region_in_text(the_text, "replace_start", "replace_end", false, || {
///         vec!["a different".to_string(), "text".to_string()]
///     })
///     .new_lines;
/// assert_eq!("replace_start\na different\ntext\nreplace_end", result);
/// ```
///
/// # Panics
///
/// Panics if start or end is not valid regex
fn replace_region_in_text<F>(text: &str, start: &str, end: &str, replace_start: bool, replacements: F) -> FileChange
where
    F: FnOnce() -> Vec<String>,
{
    let replace_it = replacements();
    let mut in_old_region = false;
    let mut found = false;
    let mut new_lines = vec![];
    let start = Regex::new(start).unwrap();
    let end = Regex::new(end).unwrap();

    for line in text.lines() {
        if in_old_region {
            if end.is_match(line) {
                in_old_region = false;
                new_lines.extend(replace_it.clone());
                new_lines.push(line.to_string());
            }
        } else if start.is_match(line) {
            if !replace_start {
                new_lines.push(line.to_string());
            }
            in_old_region = true;
            found = true;
        } else {
            new_lines.push(line.to_string());
        }
    }

    if !found {
        // This happens if the provided regex in `clippy_dev/src/main.rs` does not match in the
        // given text or file. Most likely this is an error on the programmer's side and the Regex
        // is incorrect.
        eprintln!("error: regex \n{:?}\ndoesn't match. You may have to update it.", start);
        std::process::exit(1);
    }

    let mut new_lines = new_lines.join("\n");
    if text.ends_with('\n') {
        new_lines.push('\n');
    }
    let changed = new_lines != text;
    FileChange { changed, new_lines }
}

#[test]
fn test_parse_contents() {
    let result: Vec<Lint> = parse_contents(
        r#"
declare_clippy_lint! {
    #[clippy::version = "Hello Clippy!"]
    pub PTR_ARG,
    style,
    "really long \
     text"
}

declare_clippy_lint!{
    #[clippy::version = "Test version"]
    pub DOC_MARKDOWN,
    pedantic,
    "single line"
}

/// some doc comment
declare_deprecated_lint! {
    #[clippy::version = "I'm a version"]
    pub SHOULD_ASSERT_EQ,
    "`assert!()` will be more flexible with RFC 2011"
}
    "#,
        "module_name",
    )
    .collect();

    let expected = vec![
        Lint::new("ptr_arg", "style", "really long text", None, "module_name"),
        Lint::new("doc_markdown", "pedantic", "single line", None, "module_name"),
        Lint::new(
            "should_assert_eq",
            "Deprecated",
            "`assert!()` will be more flexible with RFC 2011",
            Some("`assert!()` will be more flexible with RFC 2011"),
            "module_name",
        ),
    ];
    assert_eq!(expected, result);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_replace_region() {
        let text = "\nabc\n123\n789\ndef\nghi";
        let expected = FileChange {
            changed: true,
            new_lines: "\nabc\nhello world\ndef\nghi".to_string(),
        };
        let result = replace_region_in_text(text, r#"^\s*abc$"#, r#"^\s*def"#, false, || {
            vec!["hello world".to_string()]
        });
        assert_eq!(expected, result);
    }

    #[test]
    fn test_replace_region_with_start() {
        let text = "\nabc\n123\n789\ndef\nghi";
        let expected = FileChange {
            changed: true,
            new_lines: "\nhello world\ndef\nghi".to_string(),
        };
        let result = replace_region_in_text(text, r#"^\s*abc$"#, r#"^\s*def"#, true, || {
            vec!["hello world".to_string()]
        });
        assert_eq!(expected, result);
    }

    #[test]
    fn test_replace_region_no_changes() {
        let text = "123\n456\n789";
        let expected = FileChange {
            changed: false,
            new_lines: "123\n456\n789".to_string(),
        };
        let result = replace_region_in_text(text, r#"^\s*123$"#, r#"^\s*456"#, false, Vec::new);
        assert_eq!(expected, result);
    }

    #[test]
    fn test_usable_lints() {
        let lints = vec![
            Lint::new("should_assert_eq", "Deprecated", "abc", Some("Reason"), "module_name"),
            Lint::new("should_assert_eq2", "Not Deprecated", "abc", None, "module_name"),
            Lint::new("should_assert_eq2", "internal", "abc", None, "module_name"),
            Lint::new("should_assert_eq2", "internal_style", "abc", None, "module_name"),
        ];
        let expected = vec![Lint::new(
            "should_assert_eq2",
            "Not Deprecated",
            "abc",
            None,
            "module_name",
        )];
        assert_eq!(expected, Lint::usable_lints(&lints));
    }

    #[test]
    fn test_by_lint_group() {
        let lints = vec![
            Lint::new("should_assert_eq", "group1", "abc", None, "module_name"),
            Lint::new("should_assert_eq2", "group2", "abc", None, "module_name"),
            Lint::new("incorrect_match", "group1", "abc", None, "module_name"),
        ];
        let mut expected: HashMap<String, Vec<Lint>> = HashMap::new();
        expected.insert(
            "group1".to_string(),
            vec![
                Lint::new("should_assert_eq", "group1", "abc", None, "module_name"),
                Lint::new("incorrect_match", "group1", "abc", None, "module_name"),
            ],
        );
        expected.insert(
            "group2".to_string(),
            vec![Lint::new("should_assert_eq2", "group2", "abc", None, "module_name")],
        );
        assert_eq!(expected, Lint::by_lint_group(lints.into_iter()));
    }

    #[test]
    fn test_gen_changelog_lint_list() {
        let lints = vec![
            Lint::new("should_assert_eq", "group1", "abc", None, "module_name"),
            Lint::new("should_assert_eq2", "group2", "abc", None, "module_name"),
        ];
        let expected = vec![
            format!("[`should_assert_eq`]: {}#should_assert_eq", DOCS_LINK),
            format!("[`should_assert_eq2`]: {}#should_assert_eq2", DOCS_LINK),
        ];
        assert_eq!(expected, gen_changelog_lint_list(lints.iter()));
    }

    #[test]
    fn test_gen_deprecated() {
        let lints = vec![
            Lint::new(
                "should_assert_eq",
                "group1",
                "abc",
                Some("has been superseded by should_assert_eq2"),
                "module_name",
            ),
            Lint::new(
                "another_deprecated",
                "group2",
                "abc",
                Some("will be removed"),
                "module_name",
            ),
        ];

        let expected = GENERATED_FILE_COMMENT.to_string()
            + &[
                "{",
                "    store.register_removed(",
                "        \"clippy::should_assert_eq\",",
                "        \"has been superseded by should_assert_eq2\",",
                "    );",
                "    store.register_removed(",
                "        \"clippy::another_deprecated\",",
                "        \"will be removed\",",
                "    );",
                "}",
            ]
            .join("\n")
            + "\n";

        assert_eq!(expected, gen_deprecated(lints.iter()));
    }

    #[test]
    #[should_panic]
    fn test_gen_deprecated_fail() {
        let lints = vec![Lint::new("should_assert_eq2", "group2", "abc", None, "module_name")];
        let _deprecated_lints = gen_deprecated(lints.iter());
    }

    #[test]
    fn test_gen_modules_list() {
        let lints = vec![
            Lint::new("should_assert_eq", "group1", "abc", None, "module_name"),
            Lint::new("incorrect_stuff", "group3", "abc", None, "another_module"),
        ];
        let expected = vec!["mod another_module;".to_string(), "mod module_name;".to_string()];
        assert_eq!(expected, gen_modules_list(lints.iter()));
    }

    #[test]
    fn test_gen_lint_group_list() {
        let lints = vec![
            Lint::new("abc", "group1", "abc", None, "module_name"),
            Lint::new("should_assert_eq", "group1", "abc", None, "module_name"),
            Lint::new("internal", "internal_style", "abc", None, "module_name"),
        ];
        let expected = GENERATED_FILE_COMMENT.to_string()
            + &[
                "store.register_group(true, \"clippy::group1\", Some(\"clippy_group1\"), vec![",
                "    LintId::of(module_name::ABC),",
                "    LintId::of(module_name::INTERNAL),",
                "    LintId::of(module_name::SHOULD_ASSERT_EQ),",
                "])",
            ]
            .join("\n")
            + "\n";

        let result = gen_lint_group_list("group1", lints.iter());

        assert_eq!(expected, result);
    }
}
