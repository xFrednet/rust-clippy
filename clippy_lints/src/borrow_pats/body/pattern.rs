use rustc_hir::FnSig;

use crate::borrow_pats::SimpleTyKind;

use super::{AnalysisInfo, RETURN_LOCAL};

#[expect(unused)]
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum BodyPat {
    /// This function doesn't take any arguments
    NoArguments,
    /// Indicates that a body contained an anonymous loan. These are usually
    /// only used for temp borrows.
    HasAnonBorrow,
    /// Indicates that a body contained a named loan. So cases like
    /// `_2 = &_1`, where `_2` is a named variable.
    HasNamedBorrow,
    /// This function uses a two phased borrow. This is different from rustc's
    /// value tracked in `BorrowKind` as this this pattern is only added if a two
    /// phase borrow actually happened (i.e. the code would be rejected without)
    HasTwoPhaseBorrow,
    ReturnedStaticLoanForNonStatic,
}

#[derive(Clone)]
pub struct BodyInfo {
    pub(super) return_ty: SimpleTyKind,
    pub(super) is_const: bool,
    pub(super) is_safe: bool,
    pub(super) is_sync: bool,
    pub(super) context: BodyContext,
}

impl BodyInfo {
    pub fn from_sig(hir_sig: &FnSig<'_>, info: &AnalysisInfo<'_>, context: BodyContext) -> Self {
        Self {
            return_ty: SimpleTyKind::from_ty(info.body.local_decls[RETURN_LOCAL].ty),
            is_const: hir_sig.header.is_const(),
            is_safe: !hir_sig.header.is_unsafe(),
            is_sync: !hir_sig.header.is_async(),
            context,
        }
    }
}

impl std::fmt::Debug for BodyInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BodyInfo({self})")
    }
}

impl std::fmt::Display for BodyInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let return_ty = format!("Output({:?})", self.return_ty);
        let constness = if self.is_const { "Const" } else { "NotConst" };
        let safety = if self.is_safe { "Safe" } else { "Unsafe" };
        let sync = if self.is_sync { "Sync" } else { "Async" };
        let context = format!("{:?}", self.context);
        write!(
            f,
            "{return_ty:<17}, {constness:<9}, {safety:<6}, {sync:<5}, {context:<10}"
        )
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum BodyContext {
    /// The function is simple and free.
    Free,
    /// The function is inside an `impl` block.
    Impl,
    /// The function is inside an `impl Trait` block.
    TraitImpl,
    /// The function is inside a trait definition.
    TraitDef,
}

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

    /// The number of borrows into anonymous values.
    ///
    /// These are collected by the BodyAnalysis
    pub anon_borrow_count: usize,
    pub anon_borrow_count_mut: usize,
    /// The number of borrows into named values.
    ///
    /// These are collected by the BodyAnalysis
    pub named_borrow_count: usize,
    pub named_borrow_count_mut: usize,
    /// These are collected by the OnwedAnalysis and LoanAnalysis respectivly
    ///
    /// Note:
    /// - This only counts the confirmed two phased borrows.
    /// - The borrows that produce the two phased borrow are also counted above.
    pub two_phase_borrows: usize,
}
