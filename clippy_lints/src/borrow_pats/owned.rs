#![warn(unused)]

use super::prelude::*;
use super::{visit_body_with_state, MyStateInfo, MyVisitor, VarInfo};

mod state;
use state::*;

#[derive(Debug)]
pub struct OwnedAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    /// The name of the local, used for debugging
    name: Symbol,
    local: Local,
    states: IndexVec<BasicBlock, StateInfo<'tcx>>,
    /// The kind can diviate from the kind in info, in cases where we determine
    /// that this is most likely a deconstructed argument.
    local_kind: &'a LocalKind,
    local_info: &'a VarInfo,
    /// This should be a `BTreeSet` to have it ordered and consistent.
    pats: BTreeSet<OwnedPat>,
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>, local: Local) -> Self {
        let local_kind = &info.locals[&local].kind;
        let LocalKind::UserVar(_name, local_info) = local_kind else {
            unreachable!();
        };
        let name = local_kind.name().unwrap();

        let bbs_ctn = info.body.basic_blocks.len();
        let mut states = IndexVec::with_capacity(bbs_ctn);
        for bb in 0..bbs_ctn {
            states.push(StateInfo::new(BasicBlock::from_usize(bb)));
        }

        Self {
            info,
            local,
            name,
            states,
            local_kind,
            local_info,
            pats: Default::default(),
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>, local: Local) -> BTreeSet<OwnedPat> {
        let mut anly = Self::new(info, local);
        visit_body_with_state(&mut anly, info);

        anly.pats
    }

    fn add_borrow(
        &mut self,
        bb: BasicBlock,
        borrow: Place<'tcx>,
        broker: Place<'tcx>,
        kind: BorrowKind,
        bro: Option<BroKind>,
    ) {
        self.states[bb].add_borrow(borrow, broker, kind, bro, self.info, &mut self.pats);
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum OwnedPat {
    /// The owned value might be returned
    ///
    /// The return pattern collection should also be informed of this. White box *tesing*
    #[expect(unused, reason = "Either this needs to be detected consistency or not at all")]
    Returned,
    /// The value is only assigned once and never read afterwards.
    #[expect(unused, reason = "This can't be reliably detected with MIR")]
    Unused,
    /// The value is dynamically dropped, meaning if it's still valid at a given location.
    /// See RFC: #320
    DynamicDrop,
    /// The value was moved
    Moved,
    /// This value was moved into a different function. This also delegates the drop
    MovedToFn,
    /// This value was moved to a different local. `_other = _self`
    MovedToVar,
    /// This value was moved to `_0`
    MovedToReturn,
    /// A part was moved.
    PartMoved,
    /// This value was moved info a different local. `_other.field = _self`
    PartMovedToVar,
    /// This value was moved info a different local. `_other.field = _self`
    PartMovedToFn,
    /// A part was mvoed to `_0`
    PartMovedToReturn,
    /// This value was moved to a different local. `_other = _self`
    CopiedToVar,
    /// This value was moved info a different local. `_other.field = _self`
    CopiedToVarPart,
    /// This value was manually dropped by calling `std::mem::drop()`
    ManualDrop,
    ManualDropPart,
    /// The entire local is being borrowed
    Borrow,
    ArgBorrow,
    ArgBorrowExtended,
    ArgBorrowMut,
    ArgBorrowMutExtended,
    /// A part of the local is being borrowed
    PartBorrow,
    PartArgBorrow,
    PartArgBorrowExtended,
    PartArgBorrowMut,
    PartArgBorrowMutExtended,
    /// Two temp borrows might alias each other, for example like this:
    /// ```
    /// take_2(&self.field, &self.field);
    /// ```
    /// This also includes fields and sub fields
    /// ```
    /// take_2(&self.field, &self.field.sub_field);
    /// ```
    AliasedBorrow,
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
    /// A part of the value is being overwritten
    OverwritePart,
    /// The value will be overwritten in a loop
    //
    // FIXME: Move this pattern detection into state loop merging thingy
    #[expect(unused, reason = "TODO, handle loops properly")]
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
    /// This value was constructed in a body, used and then deconstructed at the end, to take
    /// some data and return it.
    ///
    /// ```ignore
    /// fn collect_something() -> Patterns {
    ///     let mut cx = Context::new();
    ///     cx.scan(cyz);
    ///     cx.patterns
    /// }
    /// ```
    #[expect(unused)]
    ConstructedForCalc,
    /// A value is first mutably initilized and then moved into an unmut value.
    ///
    /// ```
    /// fn mut_and_shadow_immut() {
    ///     let mut x = "Hello World".to_string();
    ///     x.push('x');
    ///     x.clear();
    ///     let x2 = x;
    ///     let _ = x2.len();
    /// }
    /// ```
    ///
    /// For `Copy` types this is only tracked, if the values have the same name.
    /// as the value is otherwise still accessible.
    ModMutShadowUnmut,
    /// A loan of this value was assigned to a named place
    NamedBorrow,
    NamedBorrowMut,
    PartNamedBorrow,
    PartNamedBorrowMut,
    ConditionalInit,
    ConditionalOverwride,
    ConditionalMove,
    ConditionalDrop,
    /// This value is being dropped (by rustc) early to be replaced.
    ///
    /// ```
    /// let data = String::new();
    ///
    /// // Rustc will first drop the old value of `data`
    /// // This is a drop to replacement
    /// data = String::from("Example");
    /// ```
    DropForReplacement,
}

impl<'a, 'tcx> MyVisitor<'tcx> for OwnedAnalysis<'a, 'tcx> {
    type State = StateInfo<'tcx>;

    fn init_start_block_state(&mut self) {
        if self.local_kind.is_arg() {
            self.states[START_BLOCK].set_state(State::Filled);
        } else {
            self.states[START_BLOCK].set_state(State::Empty);
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
            self.states[loc.block].kill_local(*local);
        }
        self.super_statement(stmt, loc);
    }

    fn visit_assign(&mut self, target: &Place<'tcx>, rvalue: &Rvalue<'tcx>, loc: Location) {
        if let Rvalue::Ref(_region, BorrowKind::Fake, _place) = &rvalue {
            return;
        }

        if target.local == self.local {
            if target.is_part() {
                // It should be enough, to only track the pattern. Since the borrowck is already
                // happy, we know that any borrows of this part are never used again. Removing them
                // would just be extra work.
                self.pats.insert(OwnedPat::OverwritePart);
            } else {
                self.visit_assign_to_self(target, rvalue, loc.block);
            }
        }

        self.visit_assign_for_self_in_args(target, rvalue, loc.block);
        self.visit_assign_for_anon(target, rvalue, loc.block);

        self.super_assign(target, rvalue, loc);
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, loc: Location) {
        self.visit_terminator_for_args(term, loc.block);
        self.visit_terminator_for_anons(term, loc.block);
        self.super_terminator(term, loc);
    }
}

impl<'a, 'tcx> OwnedAnalysis<'a, 'tcx> {
    fn visit_assign_for_self_in_args(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, bb: BasicBlock) {
        if let Rvalue::Use(op) = &rval
            && let Some(place) = op.place()
            && place.local == self.local
        {
            let is_move = op.is_move();
            if is_move {
                if place.just_local() {
                    self.pats.insert(OwnedPat::Moved);
                    self.states[bb].clear(State::Moved);
                } else if place.is_part() {
                    self.pats.insert(OwnedPat::PartMoved);
                } else {
                    unreachable!("{target:#?} = {place:#?}");
                }
            }

            if target.local.as_u32() == 0 {
                if is_move {
                    if place.just_local() {
                        self.pats.insert(OwnedPat::MovedToReturn);
                    } else if place.is_part() {
                        self.pats.insert(OwnedPat::PartMovedToReturn);
                    } else {
                        unreachable!("{target:#?} = {place:#?}");
                    }
                }
            } else if is_move {
                match &self.info.locals[&target.local].kind {
                    LocalKind::AnonVar => {
                        assert!(target.just_local());
                        self.states[bb].add_anon(target.local, place);
                    },
                    LocalKind::UserVar(_name, other_info) => {
                        if self.local_info.mutable && !other_info.mutable && target.just_local() && place.just_local() {
                            self.pats.insert(OwnedPat::ModMutShadowUnmut);
                        }

                        if place.just_local() {
                            self.pats.insert(OwnedPat::MovedToVar);
                        } else {
                            self.pats.insert(OwnedPat::PartMovedToVar);
                        }
                    },
                    _ => {
                        unreachable!("{target:#?} = {rval:#?} (at {bb:#?})\n{self:#?}");
                    },
                }
            } else {
                match &self.info.locals[&target.local].kind {
                    LocalKind::AnonVar => {
                        // This is nothing really interesting
                    },
                    LocalKind::UserVar(other_name, other_info) => {
                        if self.local_info.mutable
                            && !other_info.mutable
                            && self.name == *other_name
                            && target.just_local()
                            && place.just_local()
                        {
                            self.pats.insert(OwnedPat::ModMutShadowUnmut);
                        }

                        if target.just_local() {
                            self.pats.insert(OwnedPat::CopiedToVar);
                        } else {
                            self.pats.insert(OwnedPat::CopiedToVarPart);
                        }
                    },
                    _ => {
                        // This is nothing really interesting
                    },
                }
                // Copies are uninteresting to me
            }
        }

        if let Rvalue::Ref(_region, kind, place) = &rval
            && place.local == self.local
        {
            if place.just_local() {
                self.pats.insert(OwnedPat::Borrow);
            } else if place.is_part() {
                self.pats.insert(OwnedPat::PartBorrow);
            } else {
                unreachable!();
            }

            if target.just_local() {
                self.add_borrow(bb, *target, *place, *kind, None)
            } else {
                // Example _5.1 = &(_1.8)
                todo!("{target:#?} = {rval:#?} (at {bb:#?})\n{self:#?}");
            }
        }
    }
    fn visit_assign_to_self(&mut self, target: &Place<'tcx>, _rval: &Rvalue<'tcx>, bb: BasicBlock) {
        assert!(target.just_local());

        self.states[bb].add_assign(&mut self.pats);
    }
    fn visit_assign_for_anon(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, bb: BasicBlock) {
        if let Rvalue::Use(op) = &rval
            && let Operand::Move(place) = op
        {
            if let Some(anon_places) = self.states[bb].remove_anon(place) {
                match self.info.locals[&target.local].kind {
                    LocalKind::Return => {
                        let (is_all, is_part) = anon_places.iter().fold((false, false), |(is_all, is_part), place| {
                            (is_all || place.just_local(), is_part || place.is_part())
                        });

                        if is_all {
                            self.pats.insert(OwnedPat::MovedToReturn);
                        }
                        if is_part {
                            self.pats.insert(OwnedPat::PartMovedToReturn);
                        }
                    },
                    LocalKind::UserVar(_, _) => {
                        if place.is_part() {
                            self.pats.insert(OwnedPat::PartMovedToVar);
                        } else {
                            self.pats.insert(OwnedPat::MovedToVar);
                        }
                    },
                    LocalKind::AnonVar => {
                        assert!(place.just_local());
                        self.states[bb].add_anon_places(target.local, anon_places);
                    },
                    LocalKind::Unused => unreachable!(),
                }
            }

            self.states[bb].add_ref_copy(*target, *place, self.info, &mut self.pats)
        }

        if let Rvalue::Ref(_, _, src) | Rvalue::CopyForDeref(src) = &rval {
            match src.projection.as_slice() {
                // &(*_1) = Copy
                [PlaceElem::Deref] => {
                    // This will surely fail at one point. It was correct while this was only
                    // for anon vars. But let's fail for now, to handle it later.
                    assert!(target.just_local());
                    self.states[bb].add_ref_copy(*target, *src, self.info, &mut self.pats);
                },
                [PlaceElem::Deref, ..] | [] => {
                    self.states[bb].add_ref_ref(*target, *src, self.info, &mut self.pats);
                },
                _ => {
                    if self.states[bb].has_bro(src).is_some() {
                        unreachable!(
                            "Handle {:?} for {target:#?} = {rval:#?} (at {bb:#?})",
                            src.projection.as_slice()
                        );
                    }
                },
            }
        }
    }

    fn visit_terminator_for_args(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            // The `replace` flag of this place is super inconsistent. It lies don't trust it!!!
            TerminatorKind::Drop { place, .. } => {
                if place.local == self.local {
                    match self.states[bb].validity() {
                        Validity::Valid => {
                            if place.just_local() {
                                self.states[bb].clear(State::Dropped);
                            }
                        },
                        Validity::Maybe => {
                            if place.just_local() {
                                self.pats.insert(OwnedPat::DynamicDrop);
                                self.states[bb].clear(State::Dropped);
                            }
                        },
                        Validity::Not => {
                            // It can happen that drop is called on a moved value:
                            // ```
                            // if !a.is_empty() {
                            //     return a;
                            // }
                            // ```
                            // In that case we just ignore the action. (MIR WHY??????)
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
                        unreachable!();
                    }
                }

                if dest.local == self.local {
                    self.states[bb].add_assign(&mut self.pats);
                }
            },

            // Both of these operate on copy types. They are uninteresting for now.
            // They can still be important since these a reads which cancel mutable borrows and fields can be read
            TerminatorKind::SwitchInt { discr: op, .. } | TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && place.local == self.local
                {
                    // I'm 70% sure this can't happen
                    unreachable!("{term:?}");
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
            TerminatorKind::Call { func, args, .. } => {
                if let Some(place) = func.place()
                    && self.states[bb].remove_anon(&place).is_some()
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

                let mut immut_bros = vec![];
                // Mutable borrows can't be aliased, therefore it's suffcient
                // to just count them
                let mut mut_bro_ctn = 0;
                let mut dep_loans: Vec<(Local, Place<'tcx>, Mutability)> = vec![];
                for arg in args {
                    if let Some(anon_places) = self.states[bb].remove_anon(&arg) {
                        // These are not mutually exclusive. A rare cupple for sure, but now unseen
                        let (is_all, is_part) = anon_places.iter().fold((false, false), |(is_all, is_part), place| {
                            (is_all || place.just_local(), is_part || place.is_part())
                        });

                        if is_all {
                            self.pats.insert(OwnedPat::MovedToFn);
                        }
                        if is_part {
                            self.pats.insert(OwnedPat::PartMovedToFn);
                        }

                        if let Some((did, _generic_args)) = func.const_fn_def()
                            && self.info.cx.tcx.is_diagnostic_item(sym::mem_drop, did)
                        {
                            if is_all {
                                self.pats.insert(OwnedPat::ManualDrop);
                            }
                            if is_part {
                                self.pats.insert(OwnedPat::ManualDropPart);
                            }
                        }
                    } else if let Some(bro_info) = self.states[bb].has_bro(&arg) {
                        // Regardless of bro, we're interested in extentions
                        let loan_extended = {
                            let dep_loans_len = dep_loans.len();
                            dep_loans.extend(self.info.terms[&bb].iter().filter_map(|(local, deps)| {
                                deps.contains(&arg.local)
                                    .then_some((*local, bro_info.broker, bro_info.muta))
                            }));
                            dep_loans_len != dep_loans.len()
                        };

                        let (is_all, is_part) = bro_info.borrowed_props();
                        match bro_info.muta {
                            Mutability::Not => {
                                immut_bros.push(bro_info.broker);

                                if matches!(bro_info.kind, BroKind::Anon) {
                                    let stats = &mut self.info.stats.borrow_mut().owned;
                                    stats.arg_borrow_count += 1;
                                    if is_all {
                                        self.pats.insert(OwnedPat::ArgBorrow);
                                    }
                                    if is_part {
                                        self.pats.insert(OwnedPat::PartArgBorrow);
                                    }
                                    if loan_extended {
                                        stats.arg_borrow_extended_count += 1;
                                        if is_all {
                                            self.pats.insert(OwnedPat::ArgBorrowExtended);
                                        }
                                        if is_part {
                                            self.pats.insert(OwnedPat::PartArgBorrowExtended);
                                        }
                                    }
                                }
                            },
                            Mutability::Mut => {
                                mut_bro_ctn += 1;
                                if matches!(bro_info.kind, BroKind::Anon) {
                                    let stats = &mut self.info.stats.borrow_mut().owned;
                                    stats.arg_borrow_mut_count += 1;
                                    if is_all {
                                        self.pats.insert(OwnedPat::ArgBorrowMut);
                                    }
                                    if is_part {
                                        self.pats.insert(OwnedPat::PartArgBorrowMut);
                                    }
                                    if loan_extended {
                                        stats.arg_borrow_mut_extended_count += 1;
                                        if is_all {
                                            self.pats.insert(OwnedPat::ArgBorrowMutExtended);
                                        }
                                        if is_part {
                                            self.pats.insert(OwnedPat::PartArgBorrowMutExtended);
                                        }
                                    }
                                }
                            },
                        };
                    }
                }

                if immut_bros.len() > 1
                    && immut_bros
                        .iter()
                        .tuple_combinations()
                        .any(|(a, b)| self.info.places_conflict(*a, *b))
                {
                    self.pats.insert(OwnedPat::AliasedBorrow);
                }

                if mut_bro_ctn > 1 {
                    self.pats.insert(OwnedPat::MultipleMutBorrowsInArgs);
                }

                if !immut_bros.is_empty() && mut_bro_ctn >= 1 {
                    self.pats.insert(OwnedPat::MixedBorrowsInArgs);
                }

                for (borrower, broker, muta) in dep_loans {
                    let kind = match muta {
                        Mutability::Not => BorrowKind::Shared,
                        Mutability::Mut => BorrowKind::Mut {
                            kind: mir::MutBorrowKind::Default,
                        },
                    };
                    let borrow = unsafe { std::mem::transmute::<Place<'static>, Place<'tcx>>(borrower.as_place()) };
                    self.add_borrow(bb, borrow, broker, kind, Some(BroKind::Dep));
                }
            },

            // Both of these operate on copy types. They are uninteresting for now.
            // They can still be important since these a reads which cancel mutable borrows and fields can be read
            TerminatorKind::SwitchInt { discr: op, .. } | TerminatorKind::Assert { cond: op, .. } => {
                if let Some(place) = op.place()
                    && self.states[bb].remove_anon_place(&place).is_some()
                {
                    // FIXME: I believe this can never be true, since int is
                    // copy and therefore never tracked in anons
                    unreachable!();
                }
            },
            TerminatorKind::Drop { place, .. } => {
                debug_assert!(
                    self.states[bb].remove_anon(place).is_none(),
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
