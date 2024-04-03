#![expect(unused)]
//! # TODOs
//! - Refactor events to have places instead of locals.
//! - Refactor patterns to be made up of:
//!     - Init
//!     - Use
//!     - Death
//! - Add more patterns and states to the automata
//! - Add basic support for testing in uitests
//! - Handle or abort on feature use
//!
//! # Optional and good todos:
//! - Investigate the `explicit_outlives_requirements` lint

use std::collections::VecDeque;

use clippy_utils::is_lint_allowed;
use hir::Mutability;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir as hir;
use rustc_index::IndexVec;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::declare_lint_pass;

use rustc_middle::mir::{self, BasicBlock, Rvalue};
use rustc_span::source_map::Spanned;
use rustc_span::Symbol;

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

/// Extending the [`mir::Body`] where needed.
///
/// This is such a bad name for a trait, sorry.
trait BodyMagic {
    fn are_bbs_exclusive(&self, a: mir::BasicBlock, b: mir::BasicBlock) -> bool;
}

impl<'tcx> BodyMagic for mir::Body<'tcx> {
    fn are_bbs_exclusive(&self, a: mir::BasicBlock, b: mir::BasicBlock) -> bool {
        if a == b {
            return false;
        } else if a > b {
            return self.are_bbs_exclusive(b, a);
        }

        let mut visited = Vec::with_capacity(16);
        let mut queue = VecDeque::with_capacity(16);

        queue.push_back(a);
        while let Some(bbi) = queue.pop_front() {
            // Check we don't know the node yet
            if visited.contains(&bbi) {
                continue;
            }

            // Found our connection
            if bbi == b {
                return false;
            }

            self.basic_blocks[bbi]
                .terminator()
                .successors()
                .collect_into(&mut queue);
            visited.push(bbi);
        }

        true
    }
}

trait PlaceMagic {
    /// This returns true, if this is only a part of the local. A field or array
    /// element would be a part of a local.
    fn is_part(&self) -> bool;
}

impl PlaceMagic for mir::Place<'_> {
    fn is_part(&self) -> bool {
        self.projection.iter().any(|x| {
            matches!(
                x,
                mir::PlaceElem::Field(_, _)
                    | mir::PlaceElem::Index(_)
                    | mir::PlaceElem::ConstantIndex { .. }
                    | mir::PlaceElem::Subslice { .. }
            )
        })
    }
}

#[derive(Debug)]
struct BorrowAnalysis<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    current_bb: BasicBlock,
    edges: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
    autos: IndexVec<mir::Local, Automata<'a, 'tcx>>,
    ret_ctn: u32,
}

impl<'a, 'tcx> BorrowAnalysis<'a, 'tcx> {
    fn new(body: &'a mir::Body<'tcx>) -> Self {
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
                    LocalKind::UserArg(info.name)
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
        eprintln!("{lval:#?} -- {rval:#?}");
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
                eprintln!("This should be triggers!");
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
            mir::TerminatorKind::Call { args, destination, .. } => {
                args.iter().map(|x| &x.node).for_each(|op| {
                    let reason = AccessReason::FnArg;
                    let arg_event = match op {
                        mir::Operand::Copy(place) => Some((place, EventKind::Copy(reason))),
                        mir::Operand::Move(place) => Some((place, EventKind::Move(reason))),
                        mir::Operand::Constant(_) => None,
                    };
                    if let Some((place, event)) = arg_event {
                        self.post_event(place, event);
                    }
                });

                self.post_event(destination, EventKind::Assign(AssignSourceKind::FnRes(args)));

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

struct PrintPrevent<T>(T);

impl<T: std::fmt::Debug> std::fmt::Debug for PrintPrevent<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("PrintPrevent").finish()
    }
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
            (LocalKind::Return, _) => State::Todo,
            (LocalKind::UserArg(_), true) => State::Owned(OwnedState::Filled(InitKind::Arg)),
            (LocalKind::UserArg(symbol), false) => State::NamedRef(NamedRefInfo {
                brokers: vec![RefBrokerInfo::Arg(self.local, *symbol)],
                state: NamedRefState::Life,
            }),
            (LocalKind::UserVar(_), true) => State::Owned(OwnedState::Empty),
            (LocalKind::UserArg(symbol), false) => State::NamedRef(NamedRefInfo {
                brokers: vec![],
                state: NamedRefState::Empty,
            }),
            (LocalKind::AnonVar, true) => State::Owned(OwnedState::Empty),
            (LocalKind::AnonVar, false) => State::AnonRef(AnonRefState::Init),
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
        let State::AnonRef(state) = &self.state else {
            unreachable!();
        };

        match (state, &event.kind) {
            // A line into an anonymous reference should always be just a temporaty borrow
            (AnonRefState::Init, EventKind::Assign(AssignSourceKind::Lone(place, _))) => {
                self.state = State::AnonRef(AnonRefState::Live(vec![(place, event.bb)]));
                None
            },
            // // Just forward the event unless it's move
            // (AnonRefState::Init, EventKind::Assign(AssignSourceKind::Copy(place))) => {
            //     self.state = State::AnonRef(AnonRefState::Live(vec![(place, event.bb)]));
            //     None
            // },
            (AnonRefState::Live(..), EventKind::Move(AccessReason::FnArg)) => {
                // TODO: change this and the owned value thing, to determine the temporary
                // borrrow here and not in the owned automata
                self.state = State::AnonRef(AnonRefState::Dead);
                None
            },
            (
                AnonRefState::Live(brokers),
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::Return,
                    ..
                }),
            ) => {
                if let &[(broker, _)] = brokers.as_slice() {
                    Some(Event {
                        bb: event.bb,
                        place: *broker,
                        kind: EventKind::Loan(self.local, LoanEventKind::Return),
                    })
                } else {
                    todo!("\n{self:#?}\n\n{event:#?}\n\n")
                }
            },
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
        match (&info.state, &event.kind) {
            // We're not interested in the borrow itself, but the way the anon variable
            // is used. The anon var takes responsibility of informing this named ref
            // about how it was used
            (
                NamedRefState::Life,
                EventKind::Loan(
                    _,
                    LoanEventKind::Created {
                        borrower_kind: LocalKind::AnonVar,
                        ..
                    },
                )
                | EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::AnonVar,
                    ..
                }),
            ) => None,
            (
                NamedRefState::Life,
                EventKind::Copy(AccessReason::Assign {
                    target_kind: LocalKind::Return,
                    ..
                }),
            ) => {
                self.add_pat(PatternKind::ReturnLoan);
                None
            },
            _ => {
                todo!("{:#?}\n\n{:#?}", self, event);
            },
        }
    }
}

#[derive(Debug)]
enum State<'a, 'tcx> {
    /// The initial state, this should be short lived, as it's usually only used to directly
    /// jump to the next state.
    Init,
    /// A user created variable containing owned data.
    Owned(OwnedState),
    NamedRef(NamedRefInfo<'a, 'tcx>),
    AnonRef(AnonRefState<'a, 'tcx>),
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
struct NamedRefInfo<'a, 'tcx> {
    /// "A pawnbroker is an individual or business (pawnshop or pawn shop) that offers secured loans
    /// to people"
    brokers: Vec<RefBrokerInfo<'a, 'tcx>>,
    state: NamedRefState,
}

#[derive(Debug)]
enum RefBrokerInfo<'a, 'tcx> {
    Arg(mir::Local, Symbol),
    Borrowed(&'a mir::Place<'tcx>),
}

#[derive(Debug)]
enum NamedRefState {
    Empty,
    Life,
    Filled,
    Dead,
}

/// The state for a value generated by MIR, that holds a loan. It is unnamed
/// as the user cannot name this mystical creature.
#[derive(Debug)]
enum AnonRefState<'a, 'tcx> {
    Init,
    /// This is just a copy of another reference, all events should be forwarded.
    /// The events might need some modifications. For example, a move of this
    /// anonymous reference should be perceived as a copy on the other reference.
    Copy(mir::Local),
    Live(Vec<(&'a mir::Place<'tcx>, BasicBlock)>),
    Dead,
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
    FnRes(&'a Vec<Spanned<mir::Operand<'tcx>>>),
}

#[derive(Debug, Copy, Clone)]
enum AccessReason<'a, 'tcx> {
    /// The value was accessed as a function argument
    FnArg,
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

#[derive(Debug, Copy, Clone)]
enum LoanEventKind<'a, 'tcx> {
    Created {
        /// The place it's being loaned into
        borrower: &'a mir::Place<'tcx>,
        borrower_kind: LocalKind,
        mutability: Mutability,
    },
    MovedToFn,
    /// The loan is being returned (i.e. assigned to _0 or a part of _0)
    Return,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum LocalKind {
    Unknown,
    /// The return local
    Return,
    /// User defined argument
    UserArg(Symbol),
    /// User defined variable
    UserVar(Symbol),
    /// Generated variable, i.e. unnamed
    AnonVar,
}

impl LocalKind {
    fn user_name(&self) -> Option<Symbol> {
        match self {
            Self::UserArg(name) | Self::UserVar(name) => Some(*name),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum PatternKind {
    Unknown,
    TempBorrowed,
    TempBorrowedMut,
    /// The value might be returned, is it was assigned to `_0`
    ReturnLoan,
    /// A part of the value might be returned. THis includes fiel
    ReturnLoanedPart,
}

fn run_analysis(body: &mir::Body<'_>, body_name: &str) {
    let mut brock = BorrowAnalysis::new(body);
    brock.do_body();

    println!("- {body_name}");
    brock
        .autos
        .iter_enumerated()
        .filter_map(|(local, auto)| {
            if local.as_u32() == 0 {
                return Some(("Return [_0]".to_string(), auto));
            }

            let name = auto.local_kind.user_name()?;
            Some((format!("{:?} [{:?}]", name, local), auto))
        })
        .for_each(|(name, auto)| {
            println!("    - {name}: {:?}", auto.best_pet);
        });
}

impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
        // FIXME: Check what happens for closures
        let def = cx.tcx.hir().body_owner_def_id(body.id());

        let (mir, _) = cx.tcx.mir_promoted(def);
        let mir_borrow = mir.borrow();
        let mir_borrow = &mir_borrow;

        let body_name = cx.tcx.item_name(def.into());
        let body_name = body_name.as_str();

        // Testing and development magic
        if body_name.starts_with("borrow_field") | body_name.starts_with("borrow_self") {
            println!("# print_mir");
            println!("\n\n## MIR:");
            print_body(&mir.borrow());
            println!("\n\n## Body:");
            println!("{mir_borrow:#?}");
        }

        // Run analysis
        if !is_lint_allowed(cx, BORROW_PATS, cx.tcx.local_def_id_to_hir_id(def)) {
            run_analysis(&mir.borrow(), body_name);
        }

        if body_name == "simple_ownership" {
            println!("# simple_ownership");
            println!("\n\n## MIR:");
            print_body(&mir.borrow());

            println!("\n\n## Run:");
            let mut duck = BorrowAnalysis::new(mir_borrow);
            duck.do_body();

            println!("\n\n## Analysis:");
            println!("{duck:#?}");

            println!("\n\n## Results:");
            println!(
                "| {:>3} | {:<20} | {:<20} | {} |",
                "Name", "Kind", "Pattern", "Final State",
            );
            println!("|---|---|---|---|");
            for auto in duck.autos {
                println!(
                    "| {:>3} | {:<20} | {:<20} | {} |",
                    format!("{:?}", auto.local),
                    format!("{:?}", auto.local_kind),
                    format!("{:?}", auto.best_pet),
                    format!("[{:?}]", auto.state),
                );
            }
        }
    }
}

fn print_body(body: &mir::Body<'_>) {
    for (idx, data) in body.basic_blocks.iter_enumerated() {
        println!("bb{}:", idx.index());
        for stmt in &data.statements {
            println!("    {stmt:#?}");
        }
        println!("    {:#?}", data.terminator().kind);

        println!();
    }

    //println!("{body:#?}");
}
