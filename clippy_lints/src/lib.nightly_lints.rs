// This file was generated by `cargo dev update_lints`.
// Use that command to update this file and do not edit by hand.
// Manual edits will be overwritten.

clippy_utils::nightly::set_nightly_lints([
    #[cfg(feature = "internal")]
    LintId::of(&utils::internal_lints::FOREVER_NIGHTLY_LINT),
    LintId::of(&borrow_as_ptr::BORROW_AS_PTR),
    LintId::of(&default_union_representation::DEFAULT_UNION_REPRESENTATION),
    LintId::of(&manual_bits::MANUAL_BITS),
    LintId::of(&transmute::TRANSMUTE_UNDEFINED_REPR),
])
