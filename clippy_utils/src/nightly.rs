//! This module is intended to hold most implementations related to Clippy's
//! nightly lints.

use std::lazy::{SyncLazy, SyncOnceCell};

use rustc_data_structures::stable_set::FxHashSet;
use rustc_feature::UnstableFeatures;
use rustc_lint::{EarlyContext, LateContext, Level, Lint, LintId};
use rustc_middle::lint::{LevelAndSource, LintLevelSource};

pub static IS_NIGHTLY_RUN: SyncLazy<bool> = SyncLazy::new(|| {
    match std::env::var("CLIPPY_NIGHTLY").as_ref().map(String::as_str) {
        // This allows users to disable nightly lints on nightly
        Ok("0") => false,
        // This allows users to enable nightly lints on stable
        Ok("1") => true,
        // This uses rustc to determine if this is currently a nightly run
        _ => UnstableFeatures::from_environment(None).is_nightly_build(),
    }
});
static NIGHTLY_LINTS: SyncOnceCell<FxHashSet<LintId>> = SyncOnceCell::new();

/// This function checks if the current run is a nightly run with Clippy's nightly lints. This is
/// destinct from rustc's as a nightly build can disable Clippy's nightly features.
///
/// See [`Session::is_nightly_build(&self)`] if you want to check if the current build is a nightly
/// build.
#[inline]
pub fn is_nightly_run() -> bool {
    *IS_NIGHTLY_RUN
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
/// Please use [`is_nightly_run`] to determine if Clippy's nightly features
/// should be enabled.
#[inline]
pub fn is_nightly_lint(lint: &'static Lint) -> bool {
    NIGHTLY_LINTS
        .get()
        .map_or(false, |lints| lints.contains(&LintId::of(lint)))
}

/// This function checks if the given lint is a nightly lint and should be suppressed in the current
/// context.
#[inline]
pub fn suppress_lint<T: LintLevelProvider>(cx: &T, lint: &'static Lint) -> bool {
    if !is_nightly_run() && is_nightly_lint(lint) {
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
