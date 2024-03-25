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

struct BorrowAnalysis<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    body: &'a mir::Body<'tcx>,
    edges: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
    // These are variables defined in code, extracted from the scope
    vars: IndexVec<mir::Local, ValueUsage<'a, 'tcx>>,
    autos: IndexVec<mir::Local, Automata<'a, 'tcx>>,
}

impl<'a, 'tcx> BorrowAnalysis<'a, 'tcx> {
    fn new(cx: &'a LateContext<'tcx>, body: &'a mir::Body<'tcx>) -> Self {
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

        Self {
            cx,
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

                
            },

            // Accept with TODO prints
            mir::StatementKind::Assign(_)
             | mir::StatementKind::SetDiscriminant { .. }
            |mir::StatementKind::Deinit(_)
            |mir::StatementKind::PlaceMention(_)
            |mir::StatementKind::AscribeUserType(_, _)
            |mir::StatementKind::Intrinsic(_)
            |mir::StatementKind::ConstEvalCounter => eprintln!("TODO Handle STMT: {stmt:?}"),

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

impl<'a, 'tcx> std::fmt::Debug for BorrowAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowAnalysis")
            .field("body", &self.body)
            .field("edges", &self.edges)
            .field("vars", &self.vars)
            .finish()
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
            body,
            state: State::Init,
            events: vec![],
        }
    }

    fn make_owned_arg(&mut self) {
        self.state = State::UserOwned;
    }

    /// This accepts an event and might create a followup event
    fn accept_event(&mut self, event: Event<'a, 'tcx>) -> Option<Event<'a, 'tcx>> {
        let mut result = None;

        match self.state {
            State::Dummy(_) => unreachable!(),
            State::Init => todo!(),
            State::UserOwned => todo!(),
            State::LocalBorrow(_mut, target) => result = Some(event.followup_event(target)),

            // Should remain uninteresting?
            State::Generated => {},
            // TODOs
            State::Todo => {},
        }

        self.events.push(event);
        result
    }
}

#[derive(Debug)]
enum State<'a, 'tcx> {
    Dummy(&'a &'tcx ()),
    /// The initial state, this should be short lived, as it's usually only used to directly
    /// jump to the next state.
    // TODO: Is this needed?
    Init,
    /// A value generated for MIR
    Generated,
    /// A user created variable containing owned data.
    UserOwned,
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

impl<'a, 'tcx> Event<'a, 'tcx> {
    fn followup_event(&self, target: mir::Local) -> Self {
        let new_kind = match self.kind {
            EventKind::Dummy(_) => unreachable!(),
            EventKind::BorrowInto(_, _) => todo!(),
            EventKind::BorrowFrom(_, _) => todo!(),
        };
        Self {
            bb: self.bb,
            local: target,
            kind: new_kind,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum EventKind<'a, 'tcx> {
    Dummy(&'a &'tcx ()),
    /// This value is being borrowed into
    BorrowInto(Mutability, mir::Local),
    /// This value was borrowed from
    BorrowFrom(Mutability, mir::Local),
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
            let mut duck = BorrowAnalysis::new(cx, mir_borrow);
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
