#![expect(unused)]
//! # TODOs
//! - Refactor patterns to be made up of:
//!     - Init
//!     - Use
//!     - Death
//! - Add more patterns and states to the automata
//! - Add basic support for testing in uitests
//! - Handle or abort on feature use
//! - Insight: Loans are basically just special dependent typed
//!     - Rename some `Loan` to `Dep`
//!     - Handle Deps like loans
//! - Checkout: `rvalue_locals`
//! - The output states need to be sorted... OH NO
//!
//! # Done
//! - [x] Refactor events to have places instead of locals.
//! - [x] Consider HIR based visitor `rustc_hir_typeck::expr_use_visitor::Delegate`
//!
//! # Optional and good todos:
//! - Investigate the `explicit_outlives_requirements` lint

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ops::ControlFlow;

use borrowck::borrow_set::BorrowSet;
use borrowck::consumers::calculate_borrows_out_of_scope_at_location;
use clippy_utils::ty::{for_each_ref_region, for_each_region, for_each_top_level_late_bound_region};
use clippy_utils::{fn_has_unsatisfiable_preds, is_lint_allowed};
use hir::def_id::LocalDefId;
use hir::{HirId, Mutability};
use mid::mir::visit::Visitor;
use mid::mir::Location;
use rustc_borrowck::consumers::{get_body_with_borrowck_facts, ConsumerOptions};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_lint::{LateContext, LateLintPass, Level};
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use rustc_middle::ty::{Clause, List, TyCtxt};
use rustc_session::declare_lint_pass;
use rustc_span::source_map::Spanned;
use rustc_span::Symbol;
use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

mod owned;
mod ret;

mod info;
mod rustc_extention;
mod util;
pub use info::*;
pub use rustc_extention::*;
pub use util::*;

const RETURN: Local = Local::from_u32(0);

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```no_run
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```no_run
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.78.0"]
    pub BORROW_PATS,
    nursery,
    "default lint description"
}

declare_lint_pass!(BorrowPats => [BORROW_PATS]);

// ===========================================================
// Old Analysis
// ===========================================================

#[derive(Debug)]
struct BorrowAnalysis<'a, 'tcx> {
    cx: PrintPrevent<&'a LateContext<'tcx>>,
    tcx: PrintPrevent<TyCtxt<'tcx>>,
    body: &'a mir::Body<'tcx>,
    current_bb: BasicBlock,
    edges: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
    autos: IndexVec<mir::Local, Automata<'a, 'tcx>>,
    ret_ctn: u32,
}

impl<'a, 'tcx> BorrowAnalysis<'a, 'tcx> {
    fn cx(&self) -> &'a LateContext<'tcx> {
        self.cx.0
    }
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx.0
    }

    fn new(cx: &'a LateContext<'tcx>, tcx: TyCtxt<'tcx>, body: &'a mir::Body<'tcx>) -> Self {
        // Create Automatas
        let mut autos: IndexVec<_, _> = body
            .local_decls
            .iter_enumerated()
            .map(|(mir_name, _decl)| Automata::new(mir_name, body))
            .collect();

        autos[mir::Local::from_u32(0)].local_kind = LocalKind::Return;
        body.var_debug_info.iter().for_each(|info| {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                let local = place.local;
                // +1, since `_0` is used for the return
                autos.get_mut(local).unwrap().local_kind = if local < (body.arg_count + 1).into() {
                    LocalKind::Arg(info.name)
                } else {
                    LocalKind::UserVar(info.name)
                };
            } else {
                todo!("How should this be handled? {info:#?}");
            }
        });
        autos
            .iter_mut()
            .filter(|x| matches!(x.local_kind, LocalKind::Unknown))
            .for_each(|x| x.local_kind = LocalKind::AnonVar);

        autos.iter_mut().for_each(|x| x.init_state());

        Self {
            cx: PrintPrevent(cx),
            tcx: PrintPrevent(tcx),
            body,
            current_bb: BasicBlock::from_u32(0),
            edges: Default::default(),
            autos,
            ret_ctn: 0,
        }
    }

    fn do_body(&mut self) {
        for (bbi, bbd) in self
            .body
            .basic_blocks
            .iter_enumerated()
            .filter(|(_, bbd)| !bbd.is_cleanup)
        {
            self.current_bb = bbi;
            bbd.statements.iter().for_each(|stmt| self.do_stmt(stmt));
            let next = self.do_term(bbd.terminator());
            self.edges.insert(bbi, next);
        }
    }

    fn do_stmt(&mut self, stmt: &'a mir::Statement<'tcx>) {
        match &stmt.kind {
            // Handle first
            mir::StatementKind::Assign(box (lval, rval)) => {
                self.do_assign(lval, rval)
            },

            // Accept with TODO prints
            mir::StatementKind::Assign(_)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::Deinit(_)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::Intrinsic(_)
            | mir::StatementKind::ConstEvalCounter => eprintln!("TODO Handle STMT: {stmt:?}"),

            // NOOP or basically noop (For now)
            mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_)
            // Needed for coverage, and should never be constructed for us
            | mir::StatementKind::Coverage(_)
            // Only used by MIRI
            | mir::StatementKind::Retag(_, _)
            // Needed for type checking
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Nop => return,
        }
    }

    fn do_assign(&mut self, lval: &'a mir::Place<'tcx>, rval: &'a mir::Rvalue<'tcx>) {
        match rval {
            mir::Rvalue::Ref(_reg, kind, src) => {
                let mutability = match kind {
                    mir::BorrowKind::Shared => Mutability::Not,
                    mir::BorrowKind::Mut { .. } => Mutability::Mut,
                    mir::BorrowKind::Fake => return,
                };

                // _0 should be handled in the automata
                if lval.projection.len() != 0 {
                    eprintln!("TODO: Handle lval projections {lval:?} (mir::Rvalue::Ref 1)");
                }

                let lval_kind = self.autos[lval.local].local_kind;
                match src.projection.as_slice() {
                    [mir::PlaceElem::Deref] => {
                        // &(*_1) = Copy
                        self.post_event(lval, EventKind::Assign(AssignSourceKind::Copy(src)));
                        self.post_event(
                            src,
                            EventKind::Copy(AccessReason::Assign {
                                // TODO: This place has to be corrected to remove the deref projection
                                target: lval,
                                target_kind: lval_kind,
                            }),
                        );
                    },
                    _ => {
                        self.post_event(lval, EventKind::Assign(AssignSourceKind::Lone(src, mutability)));
                        self.post_event(
                            src,
                            EventKind::Loan(
                                lval.local,
                                LoanEventKind::Created {
                                    borrower: lval,
                                    borrower_kind: lval_kind,
                                    mutability,
                                },
                            ),
                        );
                    },
                    _ => eprintln!("TODO: Handle src projections {src:?} (mir::Rvalue::Ref 2)"),
                }

                // self.do_rvalue(*place, rval);
            },
            mir::Rvalue::Use(op) => {
                if lval.projection.len() != 0 {
                    eprintln!("TODO: Handle lval projections {lval:?} (mir::Rvalue::Use)");
                }

                // Inform accessed placed
                let reason = AccessReason::Assign {
                    target: lval,
                    target_kind: self.autos[lval.local].local_kind.clone(),
                };
                let (assign_src, rval_event) = match op {
                    mir::Operand::Copy(place) => {
                        (AssignSourceKind::Copy(place), Some((place, EventKind::Copy(reason))))
                    },
                    mir::Operand::Move(place) => {
                        (AssignSourceKind::Move(place), Some((place, EventKind::Move(reason))))
                    },
                    mir::Operand::Constant(_) => (AssignSourceKind::Const, None),
                };
                if let Some((place, event)) = rval_event {
                    self.post_event(place, event);
                }

                // Assigned place
                self.post_event(lval, EventKind::Assign(assign_src));
            },
            _ => todo!("\n{lval:#?}\n\n{rval:#?}\n"),
        }
    }

    fn post_event(&mut self, who: &'a mir::Place<'tcx>, kind: EventKind<'a, 'tcx>) {
        self.send_event(Event {
            bb: self.current_bb,
            place: *who,
            kind,
        });
    }
    fn send_event(&mut self, event: Event<'a, 'tcx>) {
        let next = self.autos[event.place.local].accept_event(event);
        if let Some(next_event) = next {
            self.send_event(next_event);
        }
    }

    fn do_term(&mut self, terminator: &'a mir::Terminator<'tcx>) -> Vec<mir::BasicBlock> {
        match &terminator.kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let dep_args = self.get_parents_of_return(func);
                args.iter().map(|x| &x.node).enumerate().for_each(|(index, op)| {
                    let lenders = if dep_args.contains(&index) {
                        vec![*destination]
                    } else {
                        vec![]
                    };
                    let reason = AccessReason::FnArg { lenders };
                    let arg_event = match op {
                        mir::Operand::Copy(place) => {
                            // Some((place, EventKind::Copy(reason)))
                            panic!("I would assert that in this MIR args are never compied")
                        },
                        mir::Operand::Move(place) => Some((place, EventKind::Move(reason))),
                        mir::Operand::Constant(_) => None,
                    };
                    if let Some((place, event)) = arg_event {
                        self.post_event(place, event);
                    }
                });

                let broker_places = dep_args.iter().filter_map(|idx| args[*idx].node.place()).collect();
                self.post_event(destination, EventKind::Assign(AssignSourceKind::FnRes(broker_places)));

                terminator.successors().collect()
            },
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                match discr {
                    mir::Operand::Copy(place) => {
                        unreachable!("I believe switch statments only move a temp variable");
                    },
                    mir::Operand::Move(place) => {
                        self.post_event(place, EventKind::Move(AccessReason::Switch));
                    },
                    // Don't care
                    mir::Operand::Constant(_) => {},
                }

                terminator.successors().collect()
            },
            mir::TerminatorKind::Drop { place, replace, .. } => {
                self.post_event(place, EventKind::Owned(OwnedEventKind::AutoDrop { replace: *replace }));
                terminator.successors().collect()
            },
            mir::TerminatorKind::Return => {
                assert_eq!(self.ret_ctn, 0, "is there always at most one return?");
                self.ret_ctn += 1;
                vec![]
            },
            // The resurn value is modeled as an assignment to the value `_0` and will be
            // handled by the assign statement. So this is basically a NoOp
            mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Unreachable => vec![],
            mir::TerminatorKind::Goto { target } => vec![*target],
            _ => {
                println!("TODO: Handle terminator: {terminator:#?}");
                terminator.successors().collect()
            },
        }
    }

    /// This function takes an operand, that identifies a function and returns the
    /// indices of the arguments that might be parents of the return type.
    ///
    /// ```
    /// fn example<'c, 'a: 'c, 'b: 'c>(cond: bool, a: &'a u32, b: &'b u32) -> &'c u32 {
    /// #    todo!()
    /// }
    /// ```
    /// This would return [1, 2], since the types in position 1 and 2 are related
    /// to the return type.
    ///
    /// TODO: This should also consider return via modification of `&mut` params
    fn get_parents_of_return(&self, op: &mir::Operand<'tcx>) -> Vec<usize> {
        if let Some((def_id, generic_args)) = op.const_fn_def() {
            // FIXME: The proper and long therm solution would be to use HIR
            // to find the call with generics that still have valid region markers.
            // However, for now I need to get this zombie in the air and not pefect
            let fn_sig = self.tcx().fn_sig(def_id).instantiate_identity();

            // On other functions this shouldn't matter. Even if they have late bounds
            // in their signature. We don't know how it's used and more imporantly,
            // The input and return types still need to follow Rust's type rules
            let fn_sig = fn_sig.skip_binder();

            let mut ret_regions = vec![];
            for_each_region(fn_sig.output(), |region| {
                ret_regions.push(region);
            });
            let ret_ty_regions = ret_regions.len();

            // FYI: Predicates don't include transitive bounds
            let item_predicates = self.tcx().predicates_of(def_id);
            // TODO Test: `inferred_outlives_of`

            let mut prev_len = 0;
            while prev_len != ret_regions.len() {
                prev_len = ret_regions.len();
                item_predicates
                    .predicates
                    .iter()
                    .filter_map(|(clause, _span)| clause.as_region_outlives_clause())
                    .for_each(|binder| {
                        if !binder.bound_vars().is_empty() {
                            todo!("Non empty depressing bounds 2: {binder:#?}");
                        }

                        let constaint = binder.skip_binder();
                        if ret_regions.contains(&constaint.1) && !ret_regions.contains(&constaint.0) {
                            ret_regions.push(constaint.0);
                        }
                    });
                // TODO: Check type outlives stuff
            }
            let ret_regions = ret_regions;

            // Collect dependent input types
            let mut input_indices = vec![];
            for (index, input) in fn_sig.inputs().iter().enumerate() {
                // "Here to stab things, don't case"
                for_each_ref_region(*input, &mut |reg, _ty, _mut| {
                    if ret_regions.contains(&reg) {
                        input_indices.push(index);
                    }
                });
            }

            // eprintln!("Dependent inputs: {input_indices:#?}");
            input_indices
        } else {
            todo!("{op:#?}\n\n{self:#?}")
        }
    }
}

#[derive(Debug)]
struct Automata<'a, 'tcx> {
    /// The local that this automata belongs to
    local: mir::Local,
    local_kind: LocalKind,
    body: PrintPrevent<&'a mir::Body<'tcx>>,
    state: State<'a, 'tcx>,
    /// Events handled by this automata, should only be used for debugging
    /// (Famous last works)
    events: Vec<Event<'a, 'tcx>>,
    /// The best pattern that was matched thus far.
    best_pet: PatternKind,
}

impl<'a, 'tcx> Automata<'a, 'tcx> {
    fn new(local: mir::Local, body: &'a mir::Body<'tcx>) -> Self {
        Self {
            local,
            local_kind: LocalKind::Unknown,
            body: PrintPrevent(body),
            state: State::Init,
            events: vec![],
            best_pet: PatternKind::Unknown,
        }
    }

    fn body(&self) -> &'a mir::Body<'tcx> {
        self.body.0
    }

    fn init_state(&mut self) {
        let decl = &self.body().local_decls[self.local];
        let is_owned = !decl.ty.is_ref();
        self.state = match (&self.local_kind, is_owned) {
            (LocalKind::Unknown, _) => unreachable!(),
            (LocalKind::Return, _) => State::Return(ReturnState::Init),
            (LocalKind::Arg(_), true) => State::Owned(OwnedState::Filled(InitKind::Arg)),
            (LocalKind::Arg(symbol), false) => State::NamedRef(NamedRefInfo {
                brokers: vec![BrokerInfo::Arg(self.local, *symbol)],
                state: NamedRefState::Life,
            }),
            (LocalKind::UserVar(_), true) => State::Owned(OwnedState::Empty),
            (LocalKind::Arg(symbol), false) => State::NamedRef(NamedRefInfo {
                brokers: vec![],
                state: NamedRefState::Empty,
            }),
            (LocalKind::AnonVar, true) => State::Owned(OwnedState::Empty),
            (LocalKind::AnonVar, false) => State::AnonRef(AnonRefInfo {
                brokers: vec![],
                state: AnonRefState::Init,
            }),
            (_, _) => todo!("{:#?}\n\n{:#?}\n\n{:#?}", self.local_kind, is_owned, self),
        };
    }

    /// This adds a detected pattern to this automata.
    fn add_pat(&mut self, pat: PatternKind) {
        self.best_pet = self.best_pet.max(pat);
    }

    /// This accepts an event and might create a followup event
    fn accept_event(&mut self, event: Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let followup = match &self.state {
            State::Owned(_) => self.update_owned_state(&event),
            State::AnonRef(_) => self.update_anon_ref_state(&event),
            State::NamedRef(_) => self.update_named_ref_state(&event),
            State::Return(_) => self.update_return_state(&event),
            State::Todo => None,
            _ => todo!("{:#?}\n\n{:#?}\n\n{:#?}", self.local_kind, event, self),
        };

        self.events.push(event);
        followup
    }

    fn update_owned_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::Owned(state) = &self.state else {
            unreachable!();
        };

        match (state, &event.kind) {
            (
                OwnedState::Empty,
                EventKind::Assign(AssignSourceKind::Const | AssignSourceKind::Copy(_) | AssignSourceKind::FnRes(_)),
            ) => {
                self.state = State::Owned(OwnedState::Filled(InitKind::Single(event.bb)));
                None
            },
            (
                OwnedState::Filled(InitKind::Single(bb)),
                EventKind::Assign(AssignSourceKind::Const | AssignSourceKind::Copy(_) | AssignSourceKind::FnRes(_)),
            ) => {
                if self.body().are_bbs_exclusive(*bb, event.bb) {
                    self.state = State::Owned(OwnedState::Filled(InitKind::Conditional(vec![*bb, event.bb])));
                } else {
                    todo!();
                }
                None
            },

            // Borrowing into an anonymous variable should always result into a
            // temporary borrow AFAIK. This will be verified by the automata of the
            // anonymous variable.
            (
                OwnedState::Filled(_),
                EventKind::Loan(
                    _,
                    LoanEventKind::Created {
                        borrower_kind: LocalKind::AnonVar,
                        mutability,
                        ..
                    },
                ),
            ) => {
                let pat = match mutability {
                    Mutability::Not => PatternKind::TempBorrowed,
                    Mutability::Mut => PatternKind::TempBorrowedMut,
                };
                self.add_pat(pat);
                None
            },
            (OwnedState::Filled(_), EventKind::Owned(OwnedEventKind::AutoDrop { replace: false })) => {
                self.state = State::Owned(OwnedState::Dropped);
                None
            },
            (OwnedState::Filled(_), EventKind::Move(AccessReason::Switch)) => {
                assert_eq!(self.local_kind, LocalKind::AnonVar);
                self.state = State::Owned(OwnedState::Moved);
                None
            },
            (OwnedState::Moved, _) => todo!("({state:?}, {:?})\n\n{self:#?}\n\n{event:#?}", event.kind),
            (OwnedState::Dropped, _) => todo!("({state:?}, {:?})\n\n{self:#?}\n\n{event:#?}", event.kind),
            _ => todo!("({state:?}\n\n{:?})\n\n{self:#?}\n\n{event:#?}", event.kind),
        }
    }

    fn update_anon_ref_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::AnonRef(info) = &mut self.state else {
            unreachable!();
        };

        match (&info.state, &event.kind) {
            // A line into an anonymous reference should always be just a temporaty borrow
            (AnonRefState::Init, EventKind::Assign(AssignSourceKind::Lone(place, _))) => {
                info.brokers.push(BrokerInfo::Borrowed(**place));
                info.state = AnonRefState::Live;
                None
            },
            (AnonRefState::Init, EventKind::Assign(AssignSourceKind::FnRes(args))) => {
                info.brokers
                    .extend(args.iter().map(|place| BrokerInfo::Borrowed(*place)));
                info.state = AnonRefState::Live;
                None
            },
            (AnonRefState::Init, EventKind::Assign(AssignSourceKind::Const)) => {
                info.brokers.push(BrokerInfo::Const);
                info.state = AnonRefState::Live;
                self.local_kind = LocalKind::AnonConst;
                None
            },
            (AnonRefState::Init, EventKind::Assign(AssignSourceKind::Copy(copy_src))) => {
                info.state = AnonRefState::Copy(copy_src.local);
                None
            },
            // The copy will forward all events too us, so we don't have to do anything
            // on the assignment here.
            (
                AnonRefState::Live,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::AnonVar,
                    ..
                }),
            ) => None,
            (
                AnonRefState::Live,
                EventKind::Move(AccessReason::FnArg { lenders }) | EventKind::Copy(AccessReason::FnArg { lenders }),
            ) => {
                let mut events: Vec<_> = info
                    .brokers
                    .iter()
                    .filter_map(|brocker| brocker.owner())
                    .map(|place| Event {
                        bb: event.bb,
                        place,
                        kind: EventKind::Loan(
                            self.local,
                            LoanEventKind::FnArg {
                                lenders: lenders.clone(),
                            },
                        ),
                    })
                    .collect();
                assert!(events.len() <= 1, "Handle larger events");
                let x = events.drain(..).next();
                x
            },
            (
                AnonRefState::Live,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::Return,
                    ..
                }),
            ) => {
                let events: Vec<_> = info
                    .brokers
                    .iter()
                    .filter_map(BrokerInfo::owner)
                    .map(|place| Event {
                        bb: event.bb,
                        place,
                        kind: EventKind::Loan(self.local, LoanEventKind::Return),
                    })
                    .collect();
                assert!(events.len() <= 1, "Multiple Brokers");
                events.into_iter().next()
            },
            (AnonRefState::Live, EventKind::Loan(_prev_loan, loan_event)) => {
                let events: Vec<_> = info
                    .brokers
                    .iter()
                    .filter_map(BrokerInfo::owner)
                    .map(|place| Event {
                        bb: event.bb,
                        place,
                        kind: EventKind::Loan(self.local, loan_event.clone()),
                    })
                    .collect();
                assert!(events.len() <= 1, "Multiple Brokers");
                events.into_iter().next()
            },
            (
                AnonRefState::Live,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::Return,
                    ..
                }),
            ) => {
                if let &[BrokerInfo::Borrowed(broker)] = &info.brokers[..] {
                    Some(Event {
                        bb: event.bb,
                        place: broker,
                        kind: EventKind::Loan(self.local, LoanEventKind::Return),
                    })
                } else {
                    todo!("\n{self:#?}\n\n{event:#?}\n\n")
                }
            },
            (AnonRefState::Copy(parent), EventKind::Move(reason)) => Some(Event {
                bb: event.bb,
                place: mir::Place {
                    local: *parent,
                    projection: List::empty(),
                },
                kind: EventKind::Copy(reason.clone()),
            }),
            (AnonRefState::Copy(parent), EventKind::Loan(_prev_loan, loan_event)) => Some(Event {
                bb: event.bb,
                place: mir::Place {
                    local: *parent,
                    projection: List::empty(),
                },
                kind: EventKind::Loan(self.local, loan_event.clone()),
            }),
            (_, EventKind::Owned(_)) => unreachable!(),
            _ => {
                todo!("{:#?}\n\n{:#?}", self, event);
            },
        }
    }

    fn update_named_ref_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::NamedRef(info) = &self.state else {
            unreachable!();
        };
        match (&info.state, &event.kind, event.place.is_part()) {
            // We're not interested in the borrow itself, but the way the anon variable
            // is used. The anon var takes responsibility of informing this named ref
            // about how it was used
            (
                NamedRefState::Life,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::AnonVar,
                    ..
                }),
                false,
            ) => None,
            (
                NamedRefState::Life,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::Return,
                    ..
                }),
                false,
            ) => {
                self.add_pat(PatternKind::ReturnLoan);
                None
            },
            (
                NamedRefState::Life,
                EventKind::Loan(
                    _,
                    LoanEventKind::Created {
                        borrower_kind: LocalKind::AnonVar,
                        ..
                    },
                ),
                true,
            ) => {
                self.add_pat(PatternKind::PartTodoPat);
                None
            },
            (NamedRefState::Life, EventKind::Loan(_, LoanEventKind::Return), true) => {
                self.add_pat(PatternKind::ReturnLoanedPart);
                None
            },
            (NamedRefState::Life, EventKind::Loan(_, LoanEventKind::FnArg { lenders }), true) => {
                // Unoptimized MIR should never directly store fn results into _0
                debug_assert!(lenders.iter().find(|place| place.local.as_u32() == 0).is_none());
                if lenders.is_empty() {
                    self.add_pat(PatternKind::PartAsFnArg);
                } else {
                    self.add_pat(PatternKind::PartAsFnArgWithDepLoan);
                }
                None
            },
            _ => {
                todo!("{:#?}\n\n{:#?}", self, event);
            },
        }
    }

    fn update_return_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::Return(ret_state) = &mut self.state else {
            unreachable!();
        };
        let EventKind::Assign(ass_event) = &event.kind else {
            unreachable!()
        };
        match (&ret_state, &ass_event) {
            (ReturnState::Init, AssignSourceKind::Const) => {
                *ret_state = ReturnState::Const;
                self.add_pat(PatternKind::ReturnConst);
            },
            (ReturnState::Init, AssignSourceKind::Lone(broker_places, _mutability)) => {
                *ret_state = ReturnState::Loan;
                self.add_pat(PatternKind::ReturnLoan);
            },
            (ReturnState::Loan, AssignSourceKind::Const) | (ReturnState::Const, AssignSourceKind::Lone(_, _)) => {
                *ret_state = ReturnState::LoanOrConst;
                self.add_pat(PatternKind::ReturnLoanOrConst);
            },
            (ReturnState::LoanOrConst, AssignSourceKind::Const | AssignSourceKind::Lone(_, _)) => {
                // Noop
            },
            (_, AssignSourceKind::FnRes(_)) => {
                unreachable!("Function results are always first stored in another local")
            },
            _ => {
                todo!("{:#?}\n\n{:#?}", self, event);
            },
        }
        None
    }
}

#[derive(Debug)]
enum State<'a, 'tcx> {
    Dummy(&'a &'tcx ()),
    /// The initial state, this should be short lived, as it's usually only used to directly
    /// jump to the next state.
    Init,
    /// A user created variable containing owned data.
    Owned(OwnedState),
    NamedRef(NamedRefInfo<'tcx>),
    AnonRef(AnonRefInfo<'tcx>),
    Return(ReturnState),
    /// Something needs to be added to handle this pattern correctly
    Todo,
}

#[derive(Debug)]
enum OwnedState {
    Empty,
    Filled(InitKind),
    Moved,
    Dropped,
}

#[derive(Debug)]
enum InitKind {
    Arg,
    Single(BasicBlock),
    Conditional(Vec<BasicBlock>),
}

#[derive(Debug)]
struct NamedRefInfo<'tcx> {
    /// "A pawnbroker is an individual or business [..] that offers secured loans to people"
    brokers: Vec<BrokerInfo<'tcx>>,
    state: NamedRefState,
}

#[derive(Debug)]
enum BrokerInfo<'tcx> {
    Arg(mir::Local, Symbol),
    Borrowed(mir::Place<'tcx>),
    Const,
}

impl<'tcx> BrokerInfo<'tcx> {
    /// This returns the owning place, if it is accessible. Constants and external loans
    /// will return none.
    fn owner(&self) -> Option<mir::Place<'tcx>> {
        match self {
            BrokerInfo::Borrowed(place) => Some(*place),
            BrokerInfo::Arg(_, _) | BrokerInfo::Const => None,
        }
    }
}

#[derive(Debug)]
enum NamedRefState {
    Empty,
    Life,
    Filled,
    Dead,
}

#[derive(Debug)]
struct AnonRefInfo<'tcx> {
    /// "A pawnbroker is an individual or business [..] that offers secured loans to people"
    brokers: Vec<BrokerInfo<'tcx>>,
    state: AnonRefState,
}

/// The state for a value generated by MIR, that holds a loan. It is unnamed
/// as the user cannot name this mystical creature.
#[derive(Debug)]
enum AnonRefState {
    Init,
    /// This is just a copy of another reference, all events should be forwarded.
    /// The events might need some modifications. For example, a move of this
    /// anonymous reference should be perceived as a copy on the other reference.
    Copy(mir::Local),
    Live,
    Dead,
}

#[derive(Debug)]
enum ReturnState {
    Init,
    Loan,
    Const,
    LoanOrConst,
}

#[derive(Debug, Clone)]
struct Event<'a, 'tcx> {
    /// The basic block this occured in
    bb: mir::BasicBlock,
    /// The local that is effected by this event
    place: mir::Place<'tcx>,
    /// The kind of the event
    kind: EventKind<'a, 'tcx>,
}

#[derive(Debug, Clone)]
enum EventKind<'a, 'tcx> {
    /// Events that can only happen to owned values
    Owned(OwnedEventKind),
    Assign(AssignSourceKind<'a, 'tcx>),
    /// Moved into a function as an argument
    Move(AccessReason<'a, 'tcx>),
    /// Coppied into a function as an argument
    Copy(AccessReason<'a, 'tcx>),
    /// Events that happened to a loan (identified by the Local) of this value
    Loan(mir::Local, LoanEventKind<'a, 'tcx>),
}

/// Something is being assigned to this value
#[derive(Debug, Clone)]
enum AssignSourceKind<'a, 'tcx> {
    /// The value of a place is being copied
    Copy(&'a mir::Place<'tcx>),
    /// The value of a place is being moved
    Move(&'a mir::Place<'tcx>),
    /// Create a lone to a place or a part of a place
    Lone(&'a mir::Place<'tcx>, Mutability),
    /// A constant value is being assigned, this can be a constant literal or
    /// a value determined at compile time like `size_of::<T>()`
    Const,

    /// The places are the arguments used for the function
    FnRes(Vec<mir::Place<'tcx>>),
}

#[derive(Debug, Clone)]
enum AccessReason<'a, 'tcx> {
    /// The value was accessed as a function argument
    FnArg {
        // See: [`LoanEventKind::FnArg`]
        lenders: Vec<mir::Place<'tcx>>,
    },
    /// The value was accessed for a conditional jump `SwitchInt`
    Switch,
    /// Assign to Local
    Assign {
        target: &'a mir::Place<'tcx>,
        target_kind: LocalKind,
    },
}

#[derive(Debug, Copy, Clone)]
enum OwnedEventKind {
    /// The value is automatically being dropped
    AutoDrop { replace: bool },
}

#[derive(Debug, Clone)]
enum LoanEventKind<'a, 'tcx> {
    Created {
        /// The place it's being loaned into
        borrower: &'a mir::Place<'tcx>,
        borrower_kind: LocalKind,
        mutability: Mutability,
    },
    /// The loan is used as a function argument. Lones are usually first copied and
    /// then moved into the function.
    FnArg {
        /// Values which might now hold a loan that depends on this input argument.
        ///
        /// For example:
        /// ```
        /// let a: Option<&u32> = slice::get(val, 1);
        /// //            ^^^^               ^^^
        /// // The output contains a loan depending on `val` but not on `1`.
        /// // Only loans are tracked, potentual clones and copies can't be determined
        /// // from the outside.
        /// ```
        lenders: Vec<mir::Place<'tcx>>,
    },
    /// The loan is being returned (i.e. assigned to _0 or a part of _0)
    Return,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum PatternKind {
    Unknown,
    TempBorrowed,
    TempBorrowedMut,
    /// A part of the value was borrowed.
    PartTodoPat,
    /// A part is used as a function argument.
    PartAsFnArg,
    /// A part is used as a function arguent and a dependent loan might escape the function.
    PartAsFnArgWithDepLoan,
    /// A constant value is returned. This can only be used by `_0`
    ReturnConst,
    /// The value might be returned, is it was assigned to `_0`
    ReturnLoan,
    /// A part of the value might be returned. This includes field
    ReturnLoanedPart,
    /// The function either returns a loan or a constant value. The function `unwrap_or_default()`
    /// is a good example for this.
    ReturnLoanOrConst,
}

fn run_analysis<'tcx>(cx: &LateContext<'tcx>, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, body_name: &str) {
    let mut brock = BorrowAnalysis::new(cx, tcx, body);
    brock.do_body();

    println!("- {body_name}");
    brock
        .autos
        .iter_enumerated()
        .filter_map(|(local, auto)| {
            if local.as_u32() == 0 {
                return Some(("Return [_0]".to_string(), auto));
            }

            let name = auto.local_kind.name()?;
            Some((format!("{:?} [{:?}]", name, local), auto))
        })
        .for_each(|(name, auto)| {
            println!("    - {name}: {:?}", auto.best_pet);
        });
}

// ===========================================================
// Old Analysis
// ===========================================================

impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
        // FIXME: Check what happens for closures
        let def = cx.tcx.hir().body_owner_def_id(body.id());
        let body_name = cx.tcx.item_name(def.into());

        // TODO: Mention in report that const can't be considered due to rustc internals
        match cx.tcx.def_kind(def) {
            hir::def::DefKind::Const => return,
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn if fn_has_unsatisfiable_preds(cx, def.into()) => return,
            _ => {},
        }

        let body_hir = cx.tcx.local_def_id_to_hir_id(def);
        let lint_level = cx.tcx.lint_level_at_node(BORROW_PATS, body_hir).0;
        let print_pats = std::env::var("CLIPPY_PETS_PRINT").is_ok();

        if lint_level != Level::Allow {
            if print_pats {
                println!("# {body_name:?}");
            }
        }

        if lint_level == Level::Forbid {
            // eprintln!("{body:#?}");
            print_debug_info(cx, body, def);
        }

        if lint_level != Level::Allow {
            let mut info = AnalysisInfo::new(cx, def);

            info.return_pats = ret::ReturnAnalysis::run(&info);

            return;
            for (local, local_info) in info.locals.iter() {
                // We're only interested in named trash
                if local_info.kind.name().is_some() {
                    let decl = &info.body.local_decls[*local];
                    let is_owned = !decl.ty.is_ref();
                    if is_owned {
                        let pats = owned::OwnedAnalysis::run(&info, *local);
                        println!("- {pats}");
                    } else {
                        eprintln!("TODO: implement analysis for named refs");
                    }
                }
            }

            if print_pats {
                // Return must be printed at the end, as it might be modified by
                // the following analysis thingies
                println!("- {}", info.return_pats);
                println!();
            }
        }

        return;

        // ===========================================================
        // Old Analysis
        // ===========================================================

        let (mir, _) = cx.tcx.mir_promoted(def);
        let mir_borrow = mir.borrow();
        let mir_borrow = &mir_borrow;
        let body_name = body_name.as_str();
        // Run analysis
        if lint_level != Level::Allow {
            run_analysis(cx, cx.tcx, &mir.borrow(), body_name);
        }
    }
}

fn print_debug_info<'tcx>(cx: &LateContext<'tcx>, body: &hir::Body<'tcx>, def: hir::def_id::LocalDefId) {
    let borrowck = get_body_with_borrowck_facts(cx.tcx, def, ConsumerOptions::RegionInferenceContext);
    println!("=====");
    print_body(&borrowck.body);
    println!();
    println!("- location_map: {:#?}", borrowck.borrow_set.location_map);
    println!("- activation_map: {:#?}", borrowck.borrow_set.activation_map);
    println!("- local_map: {:#?}", borrowck.borrow_set.local_map);
    match &borrowck.borrow_set.locals_state_at_exit {
        rustc_borrowck::borrow_set::LocalsStateAtExit::AllAreInvalidated => {
            println!("- locals_state_at_exit: AllAreInvalidated")
        },
        rustc_borrowck::borrow_set::LocalsStateAtExit::SomeAreInvalidated {
            has_storage_dead_or_moved,
        } => println!(
            "- locals_state_at_exit: SomeAreInvalidated {:#?}",
            has_storage_dead_or_moved
        ),
    };
    println!();
    let scope_info = calculate_borrows_out_of_scope_at_location(
        &borrowck.body,
        &borrowck.region_inference_context,
        &borrowck.borrow_set,
    );
    println!("- scope_info: {scope_info:#?}");
}
