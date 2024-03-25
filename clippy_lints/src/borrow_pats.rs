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

        body.args_iter().for_each(|x| {
            let decl = &body.local_decls[x];
            if decl.ty.is_ref() {
                unimplemented!();
            } else {
                autos[x].make_owned_arg();
            }
        });

        autos[mir::Local::from_u32(0)].local_kind = LocalKind::Return;
        body.var_debug_info.iter().for_each(|info| {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                let local = place.local;
                autos.get_mut(local).unwrap().local_kind = if local < body.arg_count.into() {
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
            .for_each(|x| x.local_kind = LocalKind::GenVar);

        Self {
            body,
            current_bb: BasicBlock::from_u32(0),
            edges: Default::default(),
            autos,
        }
    }

    fn do_body(&mut self) {
        for (bbi, bbd) in self.body.basic_blocks.iter_enumerated().filter(|(_, bbd)| !bbd.is_cleanup) {
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
                args,
                destination: _,
                ..
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
            state: State::Start,
            events: vec![],
            best_pet: PatternKind::None,
        }
    }

    fn make_owned_arg(&mut self) {
        self.state = State::UserOwned;
    }

    /// This accepts an event and might create a followup event
    fn accept_event(&mut self, event: Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let followup = match &self.local_kind {
            LocalKind::Unknown => unreachable!(),
            LocalKind::Return => {
                self.state = State::Todo;
                None
            },
            LocalKind::UserArg(_) | LocalKind::UserVar(_) => {
                if self.body.local_decls[self.local].ty.is_ref() {
                    self.state = State::Todo;
                    None
                } else {
                    self.accept_event_owned(&event)
                }
            },
            LocalKind::GenVar => self.accept_event_gen_var(&event),
        };

        self.events.push(event);
        followup
    }

    fn accept_event_owned(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        match (&mut self.state, &event.kind) {
            (State::Dummy(_), _) => unreachable!(),
            (State::UserOwned, EventKind::BorrowInto(mutability, borrower, LocalKind::GenVar)) => {
                self.state = State::TempBorrowed(*mutability, vec![*borrower]);
                None
            },
            (
                State::TempBorrowed(_old_mut, borrowers),
                EventKind::BorrowInto(_new_mut, borrower, LocalKind::GenVar),
            ) => {
                // If we have multiple borrows, they have to be immutable. We keep the mutability
                // stored in `TempBorrowed` as it might me mutable from a previous iteration
                borrowers.push(*borrower);
                None
            },
            (State::TempBorrowed(mutability, borrowers), EventKind::Loan(local, LoanEventKind::MovedToFn)) => {
                // If we have multiple borrows, they have to be immutable. We keep the mutability
                // stored in `TempBorrowed` as it might me mutable from a previous iteration
                borrowers.retain(|x| x != local);
                if borrowers.is_empty() {
                    let pat = match mutability {
                        Mutability::Not => PatternKind::TempBorrowed,
                        Mutability::Mut => PatternKind::TempBorrowedMut,
                    };
                    self.best_pet = self.best_pet.max(pat);
                    self.state = State::UserOwned;
                }
                None
            },
            (State::UserOwned, EventKind::AutoDrop) => {
                self.state = State::Dead;
                None
            },
            (State::Todo, _) => None,
            (_, _) => todo!(),
        }
    }

    fn accept_event_gen_var(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        assert_eq!(self.local_kind, LocalKind::GenVar);
        match (&self.state, &event.kind) {
            (State::Dummy(_), _) | (State::UserOwned, _) => unreachable!(),
            (State::Start, EventKind::BorrowFrom(mutability, target)) => {
                self.state = State::LocalBorrow(*mutability, *target);
                None
            },
            (State::LocalBorrow(_mut, target), EventKind::MoveFn) => {
                // This should only be called on temporary borrows. Temporary borrows should be
                // created in the same branch they are used. Therefore we don't need to consider
                // branching, or so the idea.
                let target = *target;
                self.state = State::Dead;
                Some(Event {
                    bb: event.bb,
                    local: target,
                    kind: EventKind::Loan(self.local, LoanEventKind::MovedToFn),
                })
            },
            (State::Todo, _) => None,
            (_, _) => todo!(),
        }
    }
}

#[derive(Debug)]
enum State<'a, 'tcx> {
    #[expect(dead_code)]
    Dummy(&'a &'tcx ()),
    /// The initial state, this should be short lived, as it's usually only used to directly
    /// jump to the next state.
    // TODO: Is this needed?
    Start,
    /// The value has been dropped or moved. It is dead :D
    Dead,
    /// A user created variable containing owned data.
    UserOwned,
    TempBorrowed(Mutability, Vec<mir::Local>),
    /// An unnamed local borrow. This is usually used for temporary borrows.
    ///
    /// This usually doesn't have followup states, but creates events for the originally
    /// owned value instead.
    LocalBorrow(Mutability, mir::Local),
    /// Something needs to be added to handle this pattern correctly
    Todo,
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
    GenVar,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum PatternKind {
    None,
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

            println!("{duck:#?}");
            print_body(&mir.borrow());
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
