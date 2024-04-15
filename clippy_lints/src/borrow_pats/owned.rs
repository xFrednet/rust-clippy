use super::ret::ReturnPat;
use super::{visit_body_in_order, AnalysisInfo, LocalKind, PatternEnum, PatternStorage, Validity};

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{VarDebugInfo, VarDebugInfoContents, START_BLOCK};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
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
    states: IndexVec<BasicBlock, State>,
    /// The kind can diviate from the kind in info, in cases where we determine
    /// that this is most likely a deconstructed argument.
    local_kind: LocalKind,
    /// A list of all invalidation.
    invals: Vec<mir::Location>,
    borrows: FxHashMap<(Place<'tcx>, mir::Location), (Place<'tcx>, Mutability, mir::Location)>,
    pats: OwnedPats,
    /// Counts how many times a value was used. This starts at 1 for arguments otherwise 0.
    use_count: u32,
}

impl<'a, 'tcx> std::fmt::Display for OwnedAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "- Owned: {} <State: {:?}>", self.pats, self.state)
    }
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>, local: Local) -> Self {
        let local_kind = info.locals[&local].kind;
        let name = local_kind.name().unwrap();

        // Safety: Is this unsafe? Theoretically yes practically no. I was actually
        // surprized that they changed the changed the return type, as it used
        // to be `&'static str`
        let name_str = unsafe { std::mem::transmute::<&str, &'static str>(name.as_str()) };

        /// Arguments are assigned outside and therefore have at least a use of 1
        let use_count = u32::from(matches!(local_kind, LocalKind::Arg(_)));

        let mut states = IndexVec::new();
        states.resize(info.body.basic_blocks.len(), State::None);

        Self {
            info,
            local,
            name,
            state: State::Empty,
            states,
            local_kind,
            invals: vec![],
            borrows: FxHashMap::default(),
            pats: OwnedPats::new(name_str),
            use_count,
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>, local: Local) -> OwnedPats {
        let mut anly = Self::new(info, local);
        visit_body_in_order(&mut anly, info);

        if anly.use_count == 1 {
            anly.pats.push(OwnedPat::Unused);
        }

        anly.pats
    }

    fn init_state(&mut self, bb: BasicBlock) {
        if bb == START_BLOCK {
            if matches!(self.local_kind, LocalKind::Arg(_)) {
                self.states[bb] = State::Filled;
            } else {
                self.states[bb] = State::Empty;
            }

            return;
        }

        let preds = &self.info.preds[&bb];
        self.states[bb] = preds.iter().map(|bb| self.states[bb]).reduce(|a, b| a.join(b)).unwrap();
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
enum State {
    None,
    Empty,
    Filled,
    Moved,
    Dropped,
    MaybeFilled,
}

impl State {
    /// Retruns true if this state contains valid data, which can be dropped or moved.
    fn validity(self) -> Validity {
        match self {
            State::None => unreachable!(),
            State::Filled => Validity::Valid,
            State::MaybeFilled => Validity::Maybe,
            State::Empty | State::Moved | State::Dropped => Validity::Not,
        }
    }

    fn join(self, other: State) -> State {
        assert_ne!(self, State::None);
        assert_ne!(other, State::None);

        if self == other {
            self
        } else {
            // For now, all others result in it being maybe filled.
            State::MaybeFilled
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum OwnedPat {
    /// The owned value is a function argument
    Arg,
    /// The owned value might be returned
    ///
    /// The return pattern collection should also be informed of this. White box *tesing*
    Returned,
    /// The value is only assigned once and never read afterwards.
    Unused,
    /// The value is dynamically dropped, meaning if it's still valid at a given location.
    /// See RFC: #320
    DynamicDrop,
}

impl PatternEnum for OwnedPat {}
pub type OwnedPats = PatternStorage<OwnedPat>;

impl<'a, 'tcx> Visitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    fn visit_var_debug_info(&mut self, info: &VarDebugInfo<'tcx>) {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.local == self.local
        {
            if let Some(arg_idx) = info.argument_index {
                self.state = State::Filled;
                self.pats.push(OwnedPat::Arg);
            }
        }
    }

    fn visit_basic_block_data(&mut self, bb: BasicBlock, bbd: &mir::BasicBlockData<'tcx>) {
        self.init_state(bb);
        self.super_basic_block_data(bb, bbd);
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
                self.states[loc.block] = State::Moved;
            }

            if target.local.as_u32() == 0 {
                self.pats.push(OwnedPat::Returned);
                if matches!(self.local_kind, LocalKind::Arg(_)) {
                    self.info.return_pats.push(ReturnPat::Argument);
                }
            } else {
                todo!();
            }
        }

        self.super_assign(target, rvalue, loc);
    }

    fn visit_terminator(&mut self, term: &mir::Terminator<'tcx>, loc: mir::Location) {
        match &term.kind {
            mir::TerminatorKind::Drop { place, .. } => {
                if place.local == self.local {
                    match self.states[loc.block].validity() {
                        Validity::Valid => {
                            self.states[loc.block] = State::Dropped;
                        },
                        Validity::Maybe => {
                            self.pats.push(OwnedPat::DynamicDrop);
                            self.states[loc.block] = State::Dropped;
                        },
                        Validity::Not => {
                            // // It can happen that drop is called on a moved value like in this
                            // code: ```
                            // if !a.is_empty() {
                            //     return a;
                            // }
                            // ```
                            // // In that case we just ignore the action. (MIR WHY??????)
                        },
                    }
                }
            },
            mir::TerminatorKind::SwitchInt { discr: op, .. } | mir::TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && place.local == self.local
                {
                    todo!();
                }
            },
            mir::TerminatorKind::Call {
                func,
                args,
                destination: dest,
                ..
            } => {
                if let Some(place) = func.place()
                    && place.local == self.local
                {
                    todo!();
                }

                for arg in args {
                    if let Some(place) = arg.node.place()
                        && place.local == self.local
                    {
                        todo!();
                    }
                }

                if dest.local == self.local {
                    todo!()
                }
            },

            // Controll flow or unstable features. Uninteresting for values
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. }
            | mir::TerminatorKind::InlineAsm { .. } => {},
        }
        self.super_terminator(term, loc)
    }

    fn visit_local(&mut self, local: Local, _context: mir::visit::PlaceContext, _location: mir::Location) {
        if local == self.local {
            self.use_count += 1;
        }
    }
}
