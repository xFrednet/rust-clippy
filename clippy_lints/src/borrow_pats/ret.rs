use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{BasicBlock, Local};

use super::AnalysisInfo;

#[derive(Debug)]
pub struct ReturnAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    inputs: FxHashSet<Local>,
    pats: FxHashSet<Pets>,
    visited: BitSet<BasicBlock>,
}

impl<'a, 'tcx> std::fmt::Display for ReturnAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Return: {:?}", self.pats)
    }
}

#[derive(Debug)]
enum Pets {
    /// Just the unit type is returned, nothing interesting
    Unit,
    /// A constant value is returned. `Unit` implies this
    Const,
    /// The return depends on some kind of condition
    ConditionalReturn,
    /// An argument is included in the return
    Argument,
}
