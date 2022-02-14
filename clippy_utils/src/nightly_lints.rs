//! This module is intended to hold most implementations related to Clippy's
//! nightly lints.

#![allow(clippy::module_name_repetitions)]

use std::lazy::SyncOnceCell;

use rustc_data_structures::stable_set::FxHashSet;
use rustc_lint::{EarlyContext, LateContext, Level, Lint, LintId};
use rustc_middle::lint::{LevelAndSource, LintLevelSource};
use rustc_session::Session;

static ENABLE_NIGHTLY_LINTS: SyncOnceCell<bool> = SyncOnceCell::new();
static NIGHTLY_LINTS: SyncOnceCell<FxHashSet<LintId>> = SyncOnceCell::new();

/// This function is used to determine if nightly lints should be enabled or disabled
/// in this Clippy run.
///
/// It's only allowed to call this once. This is done by [`clippy_lints::lib`]
#[doc(hidden)]
pub fn eval_enable_nightly_lints(sess: &Session) {
    // This allows users to disable nightly lints on nightly
    let disable_nightly = std::env::var("CLIPPY_NIGHTLY_LINTS").map(|s| s == "0").unwrap_or(false);
    // This allows users to enable nightly lints on stable
    let enable_nightly = std::env::var("CLIPPY_NIGHTLY_LINTS").map(|s| s == "1").unwrap_or(false);

    let enable_lint = enable_nightly || (sess.is_nightly_build() && !disable_nightly);

    ENABLE_NIGHTLY_LINTS
        .set(enable_lint)
        .expect("`ENABLE_NIGHTLY_LINTS` should only be set once.");
}

/// This function returns true if nightly lints should be enabled as usuall or suppressed.
#[inline]
pub fn is_enable_nightly_lint() -> bool {
    *ENABLE_NIGHTLY_LINTS.get().unwrap_or(&false)
}

/// This function takes a list of all nightly lints that will be surpressed before
/// the emission if nightly lints are disabled.
///
/// It's only allowed to call this once. This is done by [`clippy_lints::lib`]
#[doc(hidden)]
pub fn set_nightly_lints<const N: usize>(lints: [LintId; N]) {
    // The from trait for HashMaps is only implemented for the normal hasher. Here we have to add each
    // item individually
    let mut nightly_lints = FxHashSet::default();
    lints.iter().copied().for_each(|lint| {
        nightly_lints.insert(lint);
    });
    NIGHTLY_LINTS
        .set(nightly_lints)
        .expect("`NIGHTLY_LINTS` should only be set once.");
}

/// Returns true if the lint is a registered nightly lint. Note that a lint will still be a
/// registered nightly lint if nightly lints are enabled as usual.
///
/// Please use [`is_enable_nightly_lint`] to determine if Clippy's nightly features
/// should be enabled.
#[inline]
pub fn is_nightly_lint(lint: &'static Lint) -> bool {
    NIGHTLY_LINTS
        .get()
        .map_or(false, |lints| lints.contains(&LintId::of(lint)))
}

/// This function checks if the given lint is a nightly lint and should be suppressed in the current
/// context.
pub fn suppress_lint<T: LintLevelProvider>(cx: &T, lint: &'static Lint) -> bool {
    if !crate::nightly_lints::is_enable_nightly_lint() && crate::nightly_lints::is_nightly_lint(lint) {
        let (_, level_src) = cx.get_lint_level(lint);
        if level_src == LintLevelSource::Default
            || level_src == LintLevelSource::CommandLine(sym!(warnings), Level::Deny)
        {
            return true;
        }
    }

    false
}

/// This trait is used to retrieve the lint level for the lint based on the
/// current linting context.
pub trait LintLevelProvider {
    fn get_lint_level(&self, lint: &'static Lint) -> LevelAndSource;
}

impl LintLevelProvider for LateContext<'_> {
    fn get_lint_level(&self, lint: &'static Lint) -> LevelAndSource {
        self.tcx.lint_level_at_node(lint, self.last_node_with_lint_attrs)
    }
}

impl LintLevelProvider for EarlyContext<'_> {
    fn get_lint_level(&self, lint: &'static Lint) -> LevelAndSource {
        self.builder.lint_level(lint)
    }
}
