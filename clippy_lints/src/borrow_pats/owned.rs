use super::ret::ReturnPat;
use super::{AnalysisInfo, PatternEnum, PatternStorage};

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
    /// The kind can diviate from the kind in info, in cases where we determine
    /// that this is most likely a deconstructed argument.
    //owned_kind: LocalKind,
    /// A list of all invalidation.
    invals: Vec<mir::Location>,
    borrows: FxHashMap<(Place<'tcx>, mir::Location), (Place<'tcx>, Mutability, mir::Location)>,
    pats: OwnedPats,
}

impl<'a, 'tcx> std::fmt::Display for OwnedAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} <State: {:?}>", self.pats, self.state)
    }
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>, local: Local) -> Self {
        let name = info.locals[&local].kind.name().unwrap();

        // Safety: Is this unsafe? Theoretically yes practically no. I was actually
        // surprized that they changed the changed the return type, as it used
        // to be `&'static str`
        let name_str = unsafe { std::mem::transmute::<&str, &'static str>(name.as_str()) };

        Self {
            info,
            local,
            name,
            state: State::Empty,
            invals: vec![],
            borrows: FxHashMap::default(),
            pats: OwnedPats::new(name_str),
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>, local: Local) -> OwnedPats {
        let mut anly = Self::new(info, local);
        anly.visit_body(&info.body);
        anly.pats
    }
}

#[derive(Debug, Copy, Clone)]
enum State {
    Empty,
    Filled,
    Moved,
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, PartialOrd)]
pub enum OwnedPat {
    /// The owned value is a function argument
    Arg,
    /// The owned value might be returned
    ///
    /// The return pattern collection should also be informed of this. White box *tesing*
    Return,
}

impl PatternEnum for OwnedPat {}
pub type OwnedPats = PatternStorage<OwnedPat>;

impl<'a, 'tcx> Visitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    fn visit_var_debug_info(&mut self, info: &VarDebugInfo<'tcx>) {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.local == self.local
            && let Some(arg_idx) = info.argument_index
        {
            self.name = info.name;
            self.state = State::Filled;
            self.pats.push(OwnedPat::Arg);
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
                self.pats.push(OwnedPat::Return);
                self.info.return_pats.push(ReturnPat::Argument);
            } else {
                todo!();
            }
        }
    }
}
