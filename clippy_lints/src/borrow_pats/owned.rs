use super::AnalysisInfo;

use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};
use hir::Mutability;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};

pub struct OwnedAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    local: Local,
    borrows: FxHashMap<Place<'tcx>, (Place<'tcx>, Mutability)>
}
