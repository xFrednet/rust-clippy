#![warn(unused)]

use super::prelude::*;
use super::{visit_body_in_order, MyVisitor};

use super::ret::ReturnPat;

mod state;
use state::*;

#[derive(Debug)]
pub struct OwnedAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    /// The name of the local, used for debugging
    _name: Symbol,
    local: Local,
    states: IndexVec<BasicBlock, StateInfo<'tcx>>,
    /// The kind can diviate from the kind in info, in cases where we determine
    /// that this is most likely a deconstructed argument.
    local_kind: &'a LocalKind,
    /// This should be a `BTreeSet` to have it ordered and consistent.
    pats: BTreeSet<OwnedPat>,
    /// Counts how many times a value was used. This starts at 1 for arguments otherwise 0.
    use_count: u32,
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>, local: Local) -> Self {
        let local_kind = &info.locals[&local].kind;
        let name = local_kind.name().unwrap();

        // Arguments are assigned outside and therefore have at least a use of 1
        let use_count = u32::from(local_kind.is_arg());

        let mut states = IndexVec::new();
        states.resize(info.body.basic_blocks.len(), StateInfo::default());

        Self {
            info,
            local,
            _name: name,
            states,
            local_kind,
            pats: Default::default(),
            use_count,
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>, local: Local) -> BTreeSet<OwnedPat> {
        let mut anly = Self::new(info, local);
        visit_body_in_order(&mut anly, info);

        if anly.use_count == 1 {
            anly.pats.insert(OwnedPat::Unused);
        }

        anly.pats
    }

    fn add_borrow(&mut self, bb: BasicBlock, borrow: Place<'tcx>, broker: Place<'tcx>, kind: BorrowKind) {
        self.states[bb].add_borrow(borrow, broker, kind, self.info, &mut self.pats);
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum OwnedPat {
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
    /// Two temp borrows might alias each other, for example like this:
    /// ```
    /// take_2(&self.field, &self.field);
    /// ```
    /// This also includes fields and sub fields
    /// ```
    /// take_2(&self.field, &self.field.sub_field);
    /// ```
    TempBorrowAliased,
    /// A function takes mutliple `&mut` references to different parts of the object
    /// ```
    /// take_2(&mut self.field_a, &mut self.field_b);
    /// ```
    /// Mutable borrows can't be aliased.
    MultipleMutBorrowsInArgs,
    /// A function takes both a mutable and an immutable loan as the function input.
    /// ```
    /// take_2(&self.field_a, &mut self.field_b);
    /// ```
    /// The places can not be aliased.
    MixedBorrowsInArgs,
    /// The value has been overwritten
    Overwrite,
    /// The value will be overwritten in a loop
    OverwriteInLoop,
    /// This value is involved in a two phased borrow. Meaning that an argument is calculated
    /// using the value itself. Example:
    ///
    /// ```
    /// fn two_phase_borrow_1(mut vec: Vec<usize>) {
    ///     vec.push(vec.len());
    /// }
    /// ```
    ///
    /// See: <https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html>
    ///
    /// This case is special, since MIR for some reason creates an aliased mut reference.
    ///
    /// ```text
    /// bb0:
    ///     _3 = &mut _1
    ///     _5 = &_1
    ///     _4 = std::vec::Vec::<usize>::len(move _5) -> [return: bb1, unwind: bb4]
    /// bb1:
    ///     _2 = std::vec::Vec::<usize>::push(move _3, move _4) -> [return: bb2, unwind: bb4]
    /// bb2:
    ///     drop(_1) -> [return: bb3, unwind: bb5]
    /// bb3:
    ///     return
    /// ```
    ///
    /// I really don't understand why. Creating the refernce later would be totally valid, at
    /// least in all cases I looked at. This just creates a complete mess, but at this point
    /// I'm giving up on asking questions. MIR is an inconsitent pain end of story.
    ///
    /// This pattern is only added, if the two phased borrows was actually used, so if the
    /// code wouldn't work without it.
    TwoPhasedBorrow,
}

impl<'a, 'tcx> MyVisitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    type State = StateInfo<'tcx>;

    fn init_start_block_state(&mut self) {
        if self.local_kind.is_arg() {
            self.states[START_BLOCK].state = State::Filled;
        } else {
            self.states[START_BLOCK].state = State::Empty;
        }
    }

    fn set_state(&mut self, bb: BasicBlock, state: Self::State) {
        self.states[bb] = state;
    }
}

impl<'a, 'tcx> Visitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    // Note: visit_place sounds perfect, with the mild inconvinience, that it doesn't
    // provice any information about the result of the usage. Knowing that X was moved
    // is nice but context is better. Imagine `_0 = move X`. So at last, I need
    // to write these things with other visitors.

    fn visit_statement(&mut self, stmt: &Statement<'tcx>, loc: Location) {
        if let StatementKind::StorageDead(local) = &stmt.kind {
            self.states[loc.block].remove_anon_bro(&local.as_place());
        }
        self.super_statement(stmt, loc);
    }

    fn visit_assign(&mut self, target: &Place<'tcx>, rvalue: &Rvalue<'tcx>, loc: Location) {
        // TODO Ensure that moves always invalidate all borrows. IE. that the current
        // borrow check is really CFG insensitive.
        if let Rvalue::Ref(_region, BorrowKind::Fake, _place) = &rvalue {
            return;
        }

        if target.local == self.local {
            self.visit_assign_to_self(target, rvalue, loc.block);
        }

        self.visit_assign_for_args(target, rvalue, loc.block);
        self.visit_assign_for_anon(target, rvalue, loc.block);

        self.super_assign(target, rvalue, loc);
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, loc: Location) {
        self.visit_terminator_for_args(term, loc.block);
        self.visit_terminator_for_anons(term, loc.block);
        self.super_terminator(term, loc);
    }

    fn visit_local(&mut self, local: Local, _context: mir::visit::PlaceContext, _loc: Location) {
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
                self.pats.insert(OwnedPat::Returned);
                if self.local_kind.is_arg() {
                    self.info.return_pats.push(ReturnPat::Argument);
                }
            } else if is_move {
                if matches!(self.info.locals[&target.local].kind, LocalKind::AnonVar) {
                    assert!(target.just_local());
                    self.states[bb].anons.insert(target.local);
                } else {
                    todo!("{target:#?} = {rval:#?} (at {bb:#?})\n{self:#?}");
                }
            } else {
                // Copies are uninteresting to me
            }
        }

        if let Rvalue::Ref(_region, kind, place) = &rval
            && place.local == self.local
        {
            if target.just_local() {
                self.add_borrow(bb, *target, *place, *kind)
            } else {
                todo!("{target:#?} = {rval:#?} (at {bb:#?})\n{self:#?}");
            }
        }
    }
    fn visit_assign_to_self(&mut self, target: &Place<'tcx>, _rval: &Rvalue<'tcx>, bb: BasicBlock) {
        assert!(target.just_local());

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
                OwnedPat::Overwrite
            };
            self.pats.insert(pat);
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
                LocalKind::Return => {
                    self.pats.insert(OwnedPat::Returned);
                },
                LocalKind::UserVar(_, _) => {
                    if self.info.locals[&target.local].kind.is_arg() {
                        // Check if this assignment can escape the function
                        todo!("{target:#?}\n{rval:#?}\n{bb:#?}\n{self:#?}")
                    }
                    if place.is_part() {
                        self.pats.insert(OwnedPat::MovedToVarPart);
                    } else if place.just_local() {
                        // TODO: Check for `let x = x`, where x was mut and x no longer is and assignment count = 0
                        self.pats.insert(OwnedPat::MovedToVar);
                    } else {
                        todo!("{target:#?}\n{rval:#?}\n{bb:#?}\n{self:#?}");
                    }
                },
                LocalKind::AnonVar => {
                    assert!(place.just_local());
                    self.states[bb].anons.insert(target.local);
                },
                LocalKind::Unused => unreachable!(),
            }
        }

        if let Rvalue::Ref(_reg, _kind, src) = &rval
            && self.states[bb].has_anon_ref(src.local)
        {
            match src.projection.as_slice() {
                [PlaceElem::Deref] => {
                    // &(*_1) = Copy
                    assert!(target.just_local());
                    self.states[bb].add_ref_copy(target.local, src.local)
                },
                _ => todo!("Handle ref of anon ref {target:#?} = {rval:#?} (at {bb:#?})\n{self:#?}"),
            }
        }
    }

    fn visit_terminator_for_args(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            TerminatorKind::Drop { place, .. } => {
                if place.local == self.local {
                    match self.states[bb].validity() {
                        Validity::Valid => {
                            self.states[bb].state = State::Dropped;
                        },
                        Validity::Maybe => {
                            self.pats.insert(OwnedPat::DynamicDrop);
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
            TerminatorKind::Call {
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
            TerminatorKind::SwitchInt { discr: op, .. } | TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && place.local == self.local
                {
                    todo!();
                }
            },
            // Controll flow or unstable features. Uninteresting for values
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. } => {},
        }
    }
    fn visit_terminator_for_anons(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            TerminatorKind::Call {
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
                    // AFAIK, anons are always moved into the function. This makes
                    // sense as an IR property as well. So I'll go with it.
                    if let Operand::Move(place) = arg.node {
                        Some(place)
                    } else {
                        None
                    }
                });

                let mut temp_bros = vec![];
                // Mutable borrows can't be aliased, therefore it's suffcient
                // to just count them
                let mut temp_bros_mut_ctn = 0;
                for arg in args {
                    if self.states[bb].remove_anon(&arg) {
                        self.pats.insert(OwnedPat::MovedToFn);

                        if let Some((did, _generic_args)) = func.const_fn_def()
                            && self.info.cx.tcx.is_diagnostic_item(sym::mem_drop, did)
                        {
                            self.pats.insert(OwnedPat::ManualDrop);
                        }
                    } else if let Some((place, muta)) = self.states[bb].remove_anon_bro(&arg) {
                        let pat = match muta {
                            Mutability::Not => {
                                temp_bros.push(place);
                                OwnedPat::TempBorrow
                            },
                            Mutability::Mut => {
                                temp_bros_mut_ctn += 1;
                                OwnedPat::TempBorrowMut
                            },
                        };

                        self.pats.insert(pat);
                    }
                }

                if temp_bros.len() > 1
                    && temp_bros
                        .iter()
                        .tuple_combinations()
                        .any(|(a, b)| self.info.places_conflict(*a, *b))
                {
                    self.pats.insert(OwnedPat::TempBorrowAliased);
                }
                if temp_bros_mut_ctn > 1 {
                    self.pats.insert(OwnedPat::MultipleMutBorrowsInArgs);
                }
                if !temp_bros.is_empty() && temp_bros_mut_ctn >= 1 {
                    self.pats.insert(OwnedPat::MixedBorrowsInArgs);
                }

                if dest.local == self.local {
                    todo!()
                }
            },

            // Both of these operate on copy types. They are uninteresting for now.
            // They can still be important since these a reads which cancel mutable borrows and fields can be read
            TerminatorKind::SwitchInt { discr: op, .. } | TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && self.states[bb].remove_anon(&place)
                {
                    todo!();
                }
            },
            TerminatorKind::Drop { place, .. } => {
                debug_assert!(
                    !self.states[bb].remove_anon(place),
                    "AFAIK, the field is always dropped directly"
                );
                // I believe this is uninteresting
            },
            // Controll flow or unstable features. Uninteresting for values
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. } => {},
        }
    }
}
