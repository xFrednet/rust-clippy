//! This module is intended to hold most implementations related to Clippy's
//! nightly lints.

#![allow(clippy::module_name_repetitions)]

use std::lazy::SyncOnceCell;

use rustc_session::Session;

static ENABLE_NIGHTLY_LINTS: SyncOnceCell<bool> = SyncOnceCell::new();

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

pub fn is_enable_nightly_lint() -> bool {
    *ENABLE_NIGHTLY_LINTS.get().unwrap_or(&false)
}
