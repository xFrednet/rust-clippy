use super::AnalysisInfo;

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{VarDebugInfo, VarDebugInfoContents};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use rustc_span::Symbol;
use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

#[derive(Debug)]
pub struct OwnedAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    local: Local,
    name: Symbol,
    state: State,
    /// A list of all invalidation.
    invals: Vec<mir::Location>,
    borrows: FxHashMap<(Place<'tcx>, mir::Location), (Place<'tcx>, Mutability, mir::Location)>,
    pats: FxHashSet<Pets>,
}

impl<'a, 'tcx> std::fmt::Display for OwnedAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}: [State: {:?}] Patterns: {:?}",
            self.name, self.state, self.pats
        )
    }
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>, local: Local) -> Self {
        Self {
            info,
            local,
            name: rustc_span::symbol::kw::Empty,
            state: State::Empty,
            invals: vec![],
            borrows: FxHashMap::default(),
            pats: FxHashSet::default(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum State {
    Empty,
    Filled,
    Moved,
}

#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq)]
enum Pets {
    Arg,
    Return,
}

impl<'a, 'tcx> Visitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    fn visit_var_debug_info(&mut self, info: &VarDebugInfo<'tcx>) {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.local == self.local
            && let Some(arg_idx) = info.argument_index
        {
            self.name = info.name;
            self.state = State::Filled;
            self.pats.insert(Pets::Arg);
        }
    }

    // Note: visit_place sounds perfect, with the mild inconvinience, that it doesn't
    // provice any information about the result of the usage. Knowing that X was moved
    // is nice but context is better. Imagine `_0 = move X`. So at last, I need
    // to write these things with other visitors.

    fn visit_assign(&mut self, target: &Place<'tcx>, rvalue: &Rvalue<'tcx>, loc: mir::Location) {
        // TODO Ensure that moves always invalidate all borrows. IE. that the current
        // borrow check is really CFG insensitive.

        if target.local == self.local {
            todo!("Assign to this: {self:#?}");
        }

        if let Rvalue::Use(op) = &rvalue
            && let Some(place) = op.place()
            && place.local == self.local
        {
            if op.is_move() {
                self.invals.push(loc);
            }

            if target.local.as_u32() == 0 {
                self.pats.insert(Pets::Return);
            } else {
                todo!();
            }
        }
    }
}
