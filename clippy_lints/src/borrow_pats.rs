#![expect(unused)]

use hir::Mutability;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir as hir;
use rustc_index::IndexVec;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::declare_lint_pass;

use rustc_middle::mir::{self, BasicBlock};
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

// TODO: Abort on feature use
// TODO: What fun is: explicit_outlives_requirements

declare_lint_pass!(BorrowPats => [BORROW_PATS]);

#[derive(Debug)]
struct BorrowAnalysis<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    current_bb: BasicBlock,
    edges: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
    autos: IndexVec<mir::Local, Automata<'a, 'tcx>>,
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
            mir::StatementKind::Assign(box (dst, mir::Rvalue::Ref(_reg, kind, src))) => {
                let mutability = match kind {
                    mir::BorrowKind::Shared => Mutability::Not,
                    mir::BorrowKind::Mut {..} => Mutability::Mut,
                    mir::BorrowKind::Fake => return,
                };

                // _0 should be handled in the automata
                if dst.projection.len() != 0 {
                    eprintln!("TODO: Handle src projections {dst:?}");
                }
                if src.projection.len() != 0 {
                    eprintln!("TODO: Handle src projections {src:?}");
                }

                // self.do_rvalue(*place, rval);

                self.accept_event(Event {
                    bb: self.current_bb,
                    local: dst.local,
                    kind: EventKind::BorrowFrom(mutability, src.local)
                });
                let local_kind = self.autos[dst.local].local_kind;
                self.accept_event(Event {
                    bb: self.current_bb,
                    local: src.local,
                    kind: EventKind::BorrowInto(mutability, dst.local, local_kind)
                });
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

    fn accept_event(&mut self, event: Event<'a, 'tcx>) {
        let next = self.autos[event.local].accept_event(event);
        if let Some(next_event) = next {
            self.accept_event(next_event);
        }
    }

    fn do_term(&mut self, terminator: &'a mir::Terminator<'tcx>) -> Vec<mir::BasicBlock> {
        match &terminator.kind {
            mir::TerminatorKind::Call {
                args, destination: _, ..
            } => {
                args.iter().map(|x| &x.node).for_each(|op| {
                    match op {
                        mir::Operand::Copy(place) => {
                            self.accept_event(Event {
                                bb: self.current_bb,
                                local: place.local,
                                kind: EventKind::CopyFn,
                            });
                        },
                        mir::Operand::Move(place) => {
                            self.accept_event(Event {
                                bb: self.current_bb,
                                local: place.local,
                                kind: EventKind::MoveFn,
                            });
                        },
                        // Don't care
                        mir::Operand::Constant(_) => {},
                    }
                });

                terminator.successors().collect()
            },
            // The resurn value is modeled as an assignment to the value `_0` and will be
            // handled by the assign statement. So this is basically a NoOp
            mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Unreachable => vec![],
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
    body: &'a mir::Body<'tcx>,
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
            body,
            state: State::Init,
            events: vec![],
            best_pet: PatternKind::Unknown,
        }
    }

    fn init_state(&mut self) {
        let decl = &self.body.local_decls[self.local];
        let is_owned = !decl.ty.is_ref();
        self.state = match (&self.local_kind, is_owned) {
            (LocalKind::Unknown, _) => unreachable!(),
            (LocalKind::Return, true) => State::Todo,
            (LocalKind::UserArg(_), true) => State::Owned(OwnedState::Filled),
            (LocalKind::UserVar(_), true) => State::Owned(OwnedState::Empty),
            (LocalKind::AnonVar, true) => State::Owned(OwnedState::Empty),
            (LocalKind::AnonVar, false) => State::AnonRef(AnonRefState::Init),
            (_, _) => todo!(),
        };
    }

    /// This accepts an event and might create a followup event
    fn accept_event(&mut self, event: Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let followup = match &self.state {
            State::Owned(_) => self.update_owned_state(&event),
            State::AnonRef(_) => self.update_anon_ref_state(&event),
            State::Todo => None,
            _ => todo!(),
        };

        self.events.push(event);
        followup
    }

    fn update_owned_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::Owned(state) = &self.state else {
            unreachable!()
        };

        match (state, &event.kind) {
            (OwnedState::Empty, _) => todo!("{self:#?}\n\n{event:#?}"),
            // Borrowing into an anonymous variable should always result into a
            // temporary borrow AFAIK. This will be verified by the automata of the
            // anonymous variable.
            (OwnedState::Filled, EventKind::BorrowInto(mutability, _borrower, LocalKind::AnonVar)) => {
                let pat = match mutability {
                    Mutability::Not => PatternKind::TempBorrowed,
                    Mutability::Mut => PatternKind::TempBorrowedMut,
                };
                self.best_pet = self.best_pet.max(pat);
                None
            },
            (OwnedState::Moved, _) => todo!(),
            (OwnedState::Dropped, _) => todo!(),
            _ => todo!(),
        }
    }

    fn update_anon_ref_state(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let State::AnonRef(state) = &self.state else {
            unreachable!()
        };

        match (state, &event.kind) {
            (AnonRefState::Init, EventKind::BorrowFrom(_mutability, _target)) => {
                self.state = State::AnonRef(AnonRefState::Live);
                None
            },
            (AnonRefState::Live, EventKind::MoveFn) => {
                self.state = State::AnonRef(AnonRefState::Dead);
                None
            },
            _ => {
                todo!()
            },
        }
    }
}

#[derive(Debug)]
enum State<'a, 'tcx> {
    #[expect(dead_code)]
    Dummy(&'a &'tcx ()),
    /// The initial state, this should be short lived, as it's usually only used to directly
    /// jump to the next state.
    Init,
    /// A user created variable containing owned data.
    Owned(OwnedState),
    AnonRef(AnonRefState),
    /// Something needs to be added to handle this pattern correctly
    Todo,
}

#[derive(Debug)]
enum OwnedState {
    Empty,
    Filled,
    Moved,
    Dropped,
}

/// The state for a value generated by MIR, that holds a loan. It is unnamed
/// as the user cannot name this mystical creature.
#[derive(Debug)]
enum AnonRefState {
    Init,
    Live,
    Dead,
}

#[derive(Debug, Clone)]
struct Event<'a, 'tcx> {
    /// The basic block this occured in
    bb: mir::BasicBlock,
    /// The local that is effected by this event
    local: mir::Local,
    /// The kind of the event
    kind: EventKind<'a, 'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum EventKind<'a, 'tcx> {
    #[expect(dead_code)]
    Dummy(&'a &'tcx ()),
    /// This value is being borrowed into
    BorrowInto(Mutability, mir::Local, LocalKind),
    /// This value was borrowed from
    BorrowFrom(Mutability, mir::Local),
    /// Moved into a function as an argument
    MoveFn,
    /// Coppied into a function as an argument
    CopyFn,
    /// Events that happened to a loan (identified by the Local) of this value
    Loan(mir::Local, LoanEventKind),
    #[expect(dead_code)]
    AutoDrop,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum LoanEventKind {
    MovedToFn,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum PatternKind {
    Unknown,
    TempBorrowed,
    TempBorrowedMut,
}

impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
        // if in_external_macro(cx.tcx.sess, body.value.span) && is_from_proc_macro(cx, &(&kind, body,
        // body.value.hir_id, body.value.span)) {     return;
        // }

        // TODO: Check what happens for closures
        let def = cx.tcx.hir().body_owner_def_id(body.id());

        let (mir, _) = cx.tcx.mir_promoted(def);
        let mir_borrow = mir.borrow();
        let mir_borrow = &mir_borrow;

        if cx.tcx.item_name(def.into()).as_str() == "simple_ownership" {
            let mut duck = BorrowAnalysis::new(mir_borrow);
            duck.do_body();

            print_body(&mir.borrow());
            println!("{duck:#?}");
        }
        // println!("========================");
        // let mir = cx.tcx.optimized_mir(def);
        // print_body(mir);
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
