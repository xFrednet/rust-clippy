/// Most of these statistics need to be filled by the individual analysis passed.
/// Every value should document which pass might modify/fill it.
///
/// Without more context and tracking the data flow, it's impossible to know what
/// certain instructions are.
///
/// For example, a named borrow can have different shapes. Assuming `_1` is the
/// owned value and `_2` is the named references, they could have the following
/// shapes:
///
/// ```
/// // Direct
/// _2 = &_1
///
/// // Indirect
/// _3 = &_1
/// _2 = &(*_3)
///
/// // Indirect + Copy
/// _3 = &_1
/// _4 = &(*_3)
/// _2 = move _4
/// ```
#[derive(Debug, Clone, Default)]
pub struct BodyStats {
    /// Number of relations between the arguments and the return value accoring
    /// to the function signature
    ///
    /// Filled by `BodyAnalysis`
    pub return_relations_signature: usize,
    /// Number of relations between the arguments and the return value that have
    /// been found inside the body
    ///
    /// Filled by `BodyAnalysis`
    pub return_relations_found: usize,
    /// Number of relations between arguments according to the signature
    ///
    /// Filled by `BodyAnalysis`
    pub arg_relations_signature: usize,
    /// Number of relations between arguments that have been found in the body
    ///
    /// Filled by `BodyAnalysis`
    pub arg_relations_found: usize,

    /// Stats about named owned values
    pub owned: OwnedStats,
}

/// Stats for owned variables
///
/// All of these are collected by the `OwnedAnalysis`
#[derive(Debug, Clone, Default)]
pub struct OwnedStats {
    /// Temp borrows are used for function calls.
    ///
    /// The MIR commonly looks like this:
    /// ```
    /// _3 = &_1
    /// _4 = &(*_3)
    /// _2 = function(move _4)
    /// ```
    pub temp_borrow_count: usize,
    pub temp_borrow_mut_count: usize,
    /// Temporary borrows might be extended if the returned value depends on the input.
    ///
    /// The temporary borrows are also added to the trackers above.
    pub temp_borrow_extended_count: usize,
    pub temp_borrow_mut_extended_count: usize,
    /// A loan was created and stored to a named place.
    ///
    /// See comment of [`BodyStats`] for ways this might be expressed in MIR.
    pub named_borrow_count: usize,
    pub named_borrow_mut_count: usize,
    /// These are collected by the `OwnedAnalysis`
    ///
    /// Note:
    /// - This only counts the confirmed two phased borrows.
    /// - The borrows that produce the two phased borrow are also counted above.
    pub two_phased_borrows: usize,
}
