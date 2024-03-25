#![expect(unused)]

use std::collections::VecDeque;

use hir::{Mutability, UseKind};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_index::IndexVec;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::declare_lint_pass;

use rustc_middle::mir;
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
    edges: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
    // These are variables defined in code, extracted from the scope
    vars: IndexVec<mir::Local, ValueUsage<'a, 'tcx>>,
    autos: IndexVec<mir::Local, Automata<'a, 'tcx>>,
}

impl<'a, 'tcx> BorrowAnalysis<'a, 'tcx> {
    fn new(body: &'a mir::Body<'tcx>) -> Self {
        let mut vars: IndexVec<_, _> = body
            .local_decls
            .iter_enumerated()
            .map(|(mir_name, decl)| ValueUsage::new(mir_name, decl))
            .collect();

        vars[mir::Local::from_u32(0)].kind = ValueKind::Return;
        body.var_debug_info.iter().for_each(|info| {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                vars.get_mut(place.local).unwrap().kind = ValueKind::UserDef(info.name);
            } else {
                todo!("How should this be handled? {info:#?}");
            }
        });

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
        autos.iter_mut().filter(|x| matches!(x.local_kind, LocalKind::Unknown)).for_each(|x| x.local_kind = LocalKind::GenVar);

        Self {
            body,
            edges: Default::default(),
            vars,
            autos,
        }
    }

    fn do_body(&mut self) {
        for (bbi, bbd) in self.body.basic_blocks.iter_enumerated() {
            bbd.statements.iter().for_each(|stmt| self.do_stmt(stmt, bbi));
            let next = self.do_term(&bbd.terminator);
            self.edges.insert(bbi, next);
        }

        self.assign_value_kinds();
    }

    fn do_stmt(&mut self, stmt: &'a mir::Statement<'tcx>, bb: mir::BasicBlock) {
        match &stmt.kind {
            // Handle first
            mir::StatementKind::Assign(box (dst, mir::Rvalue::Ref(_reg, kind, src))) => {
                let mutability = match kind {
                    mir::BorrowKind::Shared => Mutability::Not,
                    mir::BorrowKind::Mut {..} => Mutability::Mut,
                    mir::BorrowKind::Fake => return,
                };

                // _0 should be handled in the automata
                if (dst.projection.len() != 0) {
                    eprintln!("TODO: Handle src projections {dst:?}");
                }
                if (src.projection.len() != 0) {
                    eprintln!("TODO: Handle src projections {src:?}");
                }

                // self.do_rvalue(*place, rval);

                self.accept_event(Event {
                    bb,
                    local: dst.local,
                    kind: EventKind::BorrowFrom(mutability, src.local)
                });
                let local_kind = self.autos[dst.local].local_kind;
                self.accept_event(Event {
                    bb,
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

    /// Note: this only handles the usage of `rval`. `lval` should be handled by the caller
    fn do_rvalue(&mut self, lval: mir::Place<'tcx>, rval: &'a mir::Rvalue<'tcx>) {
        match rval {
            mir::Rvalue::Use(op) => todo!(),
            // Repeat is the construction of a new value. The value has to be `Copy`,
            // Probably only interesting if the type has a lifetime
            //
            // Follow up question, is there a semantic difference between `&'a T` and `U<'a>`
            mir::Rvalue::Repeat(_, _) => todo!(),
            mir::Rvalue::Ref(_, _, _) => todo!(),
            mir::Rvalue::ThreadLocalRef(_) => todo!(),
            mir::Rvalue::AddressOf(_, _) => todo!(),
            mir::Rvalue::Len(_) => todo!(),
            mir::Rvalue::Cast(_, _, _) => todo!(),
            mir::Rvalue::BinaryOp(_, _) => todo!(),
            mir::Rvalue::CheckedBinaryOp(_, _) => todo!(),
            mir::Rvalue::NullaryOp(_, _) => todo!(),
            mir::Rvalue::UnaryOp(_, _) => todo!(),
            mir::Rvalue::Discriminant(_) => todo!(),
            mir::Rvalue::Aggregate(_, _) => todo!(),
            mir::Rvalue::ShallowInitBox(_, _) => todo!(),
            mir::Rvalue::CopyForDeref(_) => todo!(),
        }
    }

    fn do_term(&mut self, terminator: &'a Option<mir::Terminator<'tcx>>) -> Vec<mir::BasicBlock> {
        let Some(terminator) = terminator else { return vec![] };
        match &terminator.kind {
            _ => {
                println!("TODO: Handle terminator: {terminator:#?}");
                terminator.successors().collect()
            },
        }
    }

    fn assign_value_kinds(&mut self) {
        // These need to be ordered, as kind assignments might depend on other kind assignments

        // Temporary Borrows
        self.vars
            .iter_mut()
            .filter(|v| matches!(v.kind, ValueKind::Unknown))
            .for_each(|v| {
                if let [maybe_ass, rest @ ..] = &v.uses[..]
                    && let Some(place) = maybe_ass.assign_place()
                    && place.projection.is_empty()
                {
                    match rest {
                        [] => {
                            v.kind = ValueKind::DiscardNonDrop;
                        },
                        [
                            ValueUse::Drop {
                                place: _,
                                is_replace: false,
                            },
                        ] => {
                            v.kind = ValueKind::DiscardDrop;
                        },
                        [ValueUse::MoveArg] => {
                            v.kind = ValueKind::TempBorrow;
                        },
                        _ => {},
                    }
                }
            });
    }
}

#[derive(Debug)]
struct ValueUsage<'a, 'tcx> {
    mir_name: mir::Local,
    decl: &'a mir::LocalDecl<'tcx>,
    kind: ValueKind,
    uses: Vec<ValueUse<'a, 'tcx>>,
}

impl<'a, 'tcx> ValueUsage<'a, 'tcx> {
    fn new(mir_name: mir::Local, decl: &'a mir::LocalDecl<'tcx>) -> Self {
        Self {
            mir_name,
            decl,
            kind: ValueKind::Unknown,
            uses: vec![],
        }
    }
}

#[derive(Debug)]
enum ValueKind {
    Unknown,
    /// This is the value, that will be returned to the user
    Return,
    /// This variable was defined by the user and has the name stored in the symbol
    UserDef(Symbol),
    /// A temporary value used to call a functions. The fact that it is only used to
    /// be moved indicates that it's temporary
    ///
    /// Example:
    /// ```
    /// _1 = const 6;
    ///
    /// // Temp is initalized
    /// _2 = &_1;
    /// // Value is directly moved, indicating that it was temporary
    /// some_func(move _2)
    /// ```
    TempBorrow,
    /// The value is automatically generated and only written to once, but never read.
    DiscardNonDrop,
    /// The value is automatically generated and only written to once, but never read (besides
    /// drop).
    DiscardDrop,
}

#[derive(Debug)]
enum ValueUse<'a, 'tcx> {
    Assign(&'a mir::StatementKind<'tcx>),
    AssignFromCall(&'a mir::TerminatorKind<'tcx>),
    /// The value is borrowed into a local
    Borrow(mir::Local),
    /// Moved into a function via arguments
    MoveArg,
    CopyArg,
    /// The value is being dropped. This also stores the place, as it might first
    Drop {
        place: mir::Place<'tcx>,
        is_replace: bool,
    },
    /// Used to decide which branch to take
    Scrutinee {
        place: mir::Place<'tcx>,
        targets: &'a mir::SwitchTargets,
    },
    CopiedTo {
        from: mir::Place<'tcx>,
        to: mir::Place<'tcx>,
    },
    MovedTo {
        from: mir::Place<'tcx>,
        to: mir::Place<'tcx>,
    },
    /// AKA unhandled for now
    Hmm,
}

impl<'a, 'tcx> ValueUse<'a, 'tcx> {
    /// This function returns the destination of the assignment, if this is an assignment.
    fn assign_place(&self) -> Option<mir::Place<'tcx>> {
        match self {
            Self::Assign(mir::StatementKind::Assign(box (place, _expr))) => Some(*place),
            Self::AssignFromCall(mir::TerminatorKind::Call { destination, .. }) => Some(*destination),
            _ => None,
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
}

impl<'a, 'tcx> Automata<'a, 'tcx> {
    fn new(local: mir::Local, body: &'a mir::Body<'tcx>) -> Self {
        Self {
            local,
            local_kind: LocalKind::Unknown,
            body,
            state: State::Start,
            events: vec![],
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

    fn accept_event_owned(&mut self, event: &Event<'a, 'tcx>)  -> Option<Event<'a, 'tcx>> {
        match (&mut self.state, &event.kind) {
            (State::Dummy(_), _) => unreachable!(),
            (State::UserOwned, EventKind::BorrowInto(mutability, borrower, LocalKind::GenVar)) => {
                self.state = State::TempBorrowed(*mutability, vec![*borrower]);
                None
            }
            (State::TempBorrowed(_old_mut, borrowers), EventKind::BorrowInto(_new_mut, borrower, LocalKind::GenVar)) => {
                // If we have multiple borrows, they have to be immutable. We keep the mutability
                // stored in `TempBorrowed` as it might me mutable from a previous iteration
                borrowers.push(*borrower);
                None
            }
            (State::PatOwnedTempBorrowed(old_mut), EventKind::BorrowInto(new_mut, borrower, LocalKind::GenVar)) => {
                let mutability = match (*old_mut, *new_mut) {
                    (_, Mutability::Mut)|(Mutability::Mut, _) => Mutability::Mut,
                    _ => Mutability::Not,
                };
                self.state = State::TempBorrowed(mutability, vec![*borrower]);
                None
            }
            (State::Todo, _) => None,
            (_, _) => todo!(),
        }
    }

    fn accept_event_gen_var(&mut self, event: &Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        assert_eq!(self.local_kind, LocalKind::GenVar);
        match (&self.state, &event.kind) {
            (State::Dummy(_), _) | (State::UserOwned, _) => unreachable!(),
            (State::Start, EventKind::BorrowFrom(mutability, target) ) => {
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
    PatOwnedTempBorrowed(Mutability),
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
    Dummy(&'a &'tcx ()),
    /// This value is being borrowed into
    BorrowInto(Mutability, mir::Local, LocalKind),
    /// This value was borrowed from
    BorrowFrom(Mutability, mir::Local),
    /// Moved into a function as an argument
    MoveFn,
    /// Events that happened to a loan (identified by the Local) of this value
    Loan(mir::Local, LoanEventKind)
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
            print_vars(&duck);
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

fn print_vars(bro: &BorrowAnalysis<'_, '_>) {
    println!("# Variables");
    for data in bro.vars.iter() {
        println!("  {:>4?}: {:?}", data.mir_name, data.kind);
    }
}
