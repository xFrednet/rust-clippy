use std::collections::{BTreeMap, BTreeSet};

use super::ret::ReturnPat;
use super::{visit_body_in_order, AnalysisInfo, LocalKind, PatternEnum, PatternStorage, Validity};

use hir::Mutability;
use mid::mir::visit::{MutatingUseContext, Visitor};
use mid::mir::{Operand, VarDebugInfo, VarDebugInfoContents, START_BLOCK};
use mid::ty::TypeVisitableExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use rustc_span::{sym, Symbol};
use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

#[derive(Debug)]
pub struct OwnedAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    local: Local,
    name: Symbol,
    states: IndexVec<BasicBlock, StateInfo>,
    /// The kind can diviate from the kind in info, in cases where we determine
    /// that this is most likely a deconstructed argument.
    local_kind: LocalKind,
    pats: OwnedPats,
    /// Counts how many times a value was used. This starts at 1 for arguments otherwise 0.
    use_count: u32,
}

impl<'a, 'tcx> std::fmt::Display for OwnedAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "- Owned: {} <State: {:?}>",
            self.pats, self.states[self.info.return_block]
        )
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
        states.resize(info.body.basic_blocks.len(), StateInfo::default());

        Self {
            info,
            local,
            name,
            states,
            local_kind,
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
                self.states[bb].state = State::Filled;
            } else {
                self.states[bb].state = State::Empty;
            }

            return;
        }

        let preds = &self.info.preds[&bb];
        self.states[bb] = preds
            .iter()
            .map(|bb| &self.states[bb])
            .fold(StateInfo::default(), |mut acc, b| acc.join(b));
    }
}

#[derive(Clone, Debug, Default)]
struct StateInfo {
    state: State,
    /// This is a set of values that *might* contain the owned value.
    /// MIR has this *beautiful* habit of moving stuff into anonymous
    /// locals first before using it further.
    anons: BTreeSet<Local>,
    /// This set contains anonymous borrows, these are AFAIK always used
    /// for temporary borrows.
    ///
    /// Note: If I can confirm that these borrows are always used for
    /// temporary borrows, it might be possible to prevent tracking them
    /// to safe some performance.
    temp_bros: BTreeMap<Local, Mutability>,
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd, Default)]
enum State {
    #[default]
    None,
    Empty,
    Filled,
    Moved,
    Dropped,
    MaybeFilled,
}

impl StateInfo {
    /// Retruns true if this state contains valid data, which can be dropped or moved.
    fn validity(&self) -> Validity {
        match self.state {
            State::None => unreachable!(),
            State::Filled => Validity::Valid,
            State::MaybeFilled => Validity::Maybe,
            State::Empty | State::Moved | State::Dropped => Validity::Not,
        }
    }

    fn join(mut self, other: &StateInfo) -> StateInfo {
        assert_ne!(other.state, State::None);
        if self.state == State::None {
            return other.clone();
        }

        self.state = match (self.validity(), other.validity()) {
            (Validity::Valid, Validity::Valid) => State::Filled,
            (Validity::Not, Validity::Not) => State::Empty,
            (_, _) => State::MaybeFilled,
        };

        self.anons.extend(other.anons.iter());
        self.temp_bros.extend(other.temp_bros.iter());

        self
    }

    /// This tries to remove the given place from the known anons that hold this value.
    /// It will retrun `true`, if the removal was successfull.
    /// Places with projections will be ignored.
    fn remove_anon(&mut self, anon: &Place<'_>) -> bool {
        if anon.has_projections() {
            return false;
        }

        self.anons.remove(&anon.local)
    }

    fn remove_temp_bro(&mut self, anon: &Place<'_>) -> Option<Mutability> {
        if anon.has_projections() {
            return None;
        }

        self.temp_bros.remove(&anon.local)
    }

    /// This clears this state. The `state` field has to be set afterwards
    fn clear(&mut self) {
        self.anons.clear();
        self.temp_bros.clear();

        self.state = State::None;
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
    /// This value was moved into a different function. This also delegates the drop
    MovedToFn,
    /// This value was moved to a different local. `_other = _self`
    MovedToVar,
    /// This value was moved info a different local. `_other.field = _self`
    MovedToVarPart,
    /// This value was manually dropped by calling `std::mem::drop()`
    ManualDrop,
    TempBorrow,
    TempBorrowMut,
    /// The value has been overwritten
    Overwrite,
    /// The value will be overwritten in a loop
    OverwriteInLoop,
}

impl PatternEnum for OwnedPat {}
pub type OwnedPats = PatternStorage<OwnedPat>;

impl<'a, 'tcx> Visitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    fn visit_var_debug_info(&mut self, info: &VarDebugInfo<'tcx>) {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.local == self.local
        {
            if let Some(arg_idx) = info.argument_index {
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
        if let Rvalue::Ref(_region, mir::BorrowKind::Fake, _place) = &rvalue {
            return;
        }

        if target.local == self.local {
            self.visit_assign_to_self(target, rvalue, loc.block);
        }

        self.visit_assign_for_args(target, rvalue, loc.block);
        self.visit_assign_for_anon(target, rvalue, loc.block);

        self.super_assign(target, rvalue, loc);
    }

    fn visit_terminator(&mut self, term: &mir::Terminator<'tcx>, loc: mir::Location) {
        self.visit_terminator_for_args(term, loc.block);
        self.visit_terminator_for_anons(term, loc.block);
        self.super_terminator(term, loc);
    }

    fn visit_local(&mut self, local: Local, context: mir::visit::PlaceContext, loc: mir::Location) {
        // TODO: Check that this isn't called for StorageLife and StorageDead
        if local == self.local {
            self.use_count += 1;
        }
    }
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    fn visit_assign_for_args(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, bb: BasicBlock) {
        if let Rvalue::Use(op) = &rval
            && let Some(place) = op.place()
            && place.local == self.local
        {
            let is_move = op.is_move();
            if is_move {
                self.states[bb].state = State::Moved;
            }

            if target.local.as_u32() == 0 {
                self.pats.push(OwnedPat::Returned);
                if matches!(self.local_kind, LocalKind::Arg(_)) {
                    self.info.return_pats.push(ReturnPat::Argument);
                }
            } else if is_move {
                if self.info.locals[&target.local].kind == LocalKind::AnonVar {
                    assert!(!target.has_projections());
                    self.states[bb].anons.insert(target.local);
                } else {
                    todo!("{target:#?}\n{rval:#?}\n{self:#?}");
                }
            } else {
                // Copies are uninteresting to me
            }
        }

        if let Rvalue::Ref(_region, kind, place) = &rval
            && place.local == self.local
        {
            assert!(!place.has_projections());
            self.states[bb].temp_bros.insert(target.local, kind.mutability());
        }
    }
    fn visit_assign_to_self(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, bb: BasicBlock) {
        assert!(!target.has_projections());

        let is_override = match self.states[bb].state {
            // No-op the most normal and simple state
            State::Empty => false,

            // Filled should only ever be the case for !Drop types
            State::Filled | State::MaybeFilled => {
                // TODO: assert!(is_copy)
                true
            },

            State::Moved | State::Dropped => true,
            State::None => unreachable!(),
        };
        if is_override {
            let pat = if self.info.find_loop(bb).is_some() {
                OwnedPat::OverwriteInLoop
            } else {
                OwnedPat::OverwriteInLoop
            };
            self.pats.push(pat);
        }

        // Regardless of the original state, we clear everything else
        self.states[bb].clear();
        self.states[bb].state = State::Filled;
    }
    fn visit_assign_for_anon(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, bb: BasicBlock) {
        if let Rvalue::Use(op) = &rval
            && let Operand::Move(place) = op
            && self.states[bb].remove_anon(place)
        {
            match self.info.locals[&target.local].kind {
                LocalKind::Return => self.pats.push(OwnedPat::Returned),
                LocalKind::Arg(_) => {
                    // Check if this assignment can escape the function
                    todo!("{target:#?}\n{rval:#?}\n{bb:#?}\n{self}")
                },
                LocalKind::UserVar(_) => {
                    if place.has_projections() {
                        self.pats.push(OwnedPat::MovedToVarPart);
                    } else {
                        self.pats.push(OwnedPat::MovedToVar);
                    }
                },
                LocalKind::AnonVar => {
                    assert!(!place.has_projections());
                    self.states[bb].anons.insert(target.local);
                },
                LocalKind::Unused => unreachable!(),
            }
        }
    }

    fn visit_terminator_for_args(&mut self, term: &mir::Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            mir::TerminatorKind::Drop { place, .. } => {
                if place.local == self.local {
                    match self.states[bb].validity() {
                        Validity::Valid => {
                            self.states[bb].state = State::Dropped;
                        },
                        Validity::Maybe => {
                            self.pats.push(OwnedPat::DynamicDrop);
                            self.states[bb].state = State::Dropped;
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

            // Both of these operate on copy types. They are uninteresting for now.
            // They can still be important since these a reads which cancel mutable borrows and fields can be read
            mir::TerminatorKind::SwitchInt { discr: op, .. } | mir::TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && place.local == self.local
                {
                    todo!();
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
    }
    fn visit_terminator_for_anons(&mut self, term: &mir::Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            mir::TerminatorKind::Drop { place, .. } => {
                // TODO: Is this even interesting or can we just ignore this?
                // if let Some((index, _)) = find_anon(place.local) {
                //     self.states[bb].anons.swap_remove(index);
                // }
            },
            mir::TerminatorKind::Call {
                func,
                args,
                destination: dest,
                ..
            } => {
                if let Some(place) = func.place()
                    && self.states[bb].remove_anon(&place)
                {
                    todo!();
                }

                let args = args.iter().filter_map(|arg| {
                    if let Operand::Move(place) = arg.node {
                        Some(place)
                    } else {
                        None
                    }
                });
                for arg in args {
                    if self.states[bb].remove_anon(&arg) {
                        self.pats.push(OwnedPat::MovedToFn);

                        if let Some((did, _generic_args)) = func.const_fn_def()
                            && self.info.cx.tcx.is_diagnostic_item(sym::mem_drop, did)
                        {
                            self.pats.push(OwnedPat::ManualDrop);
                        }
                    } else if let Some(muta) = self.states[bb].remove_temp_bro(&arg) {
                        let pat = match muta {
                            Mutability::Not => OwnedPat::TempBorrow,
                            Mutability::Mut => OwnedPat::TempBorrowMut,
                        };
                        self.pats.push(pat);
                    }
                }

                if dest.local == self.local {
                    todo!()
                }
            },

            // Both of these operate on copy types. They are uninteresting for now.
            // They can still be important since these a reads which cancel mutable borrows and fields can be read
            mir::TerminatorKind::SwitchInt { discr: op, .. } | mir::TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && place.local == self.local
                {
                    todo!();
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
    }
}
