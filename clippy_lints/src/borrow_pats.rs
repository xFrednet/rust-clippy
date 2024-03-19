#![expect(unused)]

use std::collections::VecDeque;

use hir::UseKind;
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
    checked_bbs: FxHashSet<mir::BasicBlock>,
    // These are variables defined in code, extracted from the scope
    vars: IndexVec<mir::Local, ValueUsage<'a, 'tcx>>,
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

        Self {
            cx,
            body,
            checked_bbs: Default::default(),
            vars,
        }
    }

    fn do_body(&mut self) {
        let mut q: VecDeque<mir::BasicBlock> = VecDeque::new();

        q.push_back(mir::BasicBlock::from_u32(0));

        while let Some(bb) = q.pop_front() {
            if self.checked_bbs.contains(&bb) {
                continue;
            }
            self.checked_bbs.insert(bb);

            let bbd = &self.body.basic_blocks[bb];
            bbd.statements.iter().for_each(|stmt| self.do_stmt(stmt));
            let next_bbs = self.do_term(&bbd.terminator);
            q.extend(next_bbs);
        }

        // TODO assert that all BBs have been checked

        self.assign_value_kinds();
    }

    fn do_stmt(&mut self, stmt: &'a mir::Statement<'tcx>) {
        match &stmt.kind {
            // Handle first
            mir::StatementKind::Assign(box (place, _expr)) => {
                // TODO: add handling for _0
                if (place.projection.len() != 0) {
                    eprintln!("TODO: Handle projections {place:?}");
                }

                self.vars[place.local].uses.push(ValueUse::Assign(stmt));
            },

            // Accept with TODO prints
            mir::StatementKind::SetDiscriminant { .. } => eprintln!("TODO Handle STMT: {stmt:?}"),
            mir::StatementKind::Deinit(_) => eprintln!("TODO Handle STMT: {stmt:?}"),
            mir::StatementKind::PlaceMention(_) => eprintln!("TODO Handle STMT: {stmt:?}"),
            mir::StatementKind::AscribeUserType(_, _) => eprintln!("TODO Handle STMT: {stmt:?}"),
            mir::StatementKind::Intrinsic(_) => eprintln!("TODO Handle STMT: {stmt:?}"),
            mir::StatementKind::ConstEvalCounter => eprintln!("TODO Handle STMT: {stmt:?}"),

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

    fn do_term(&mut self, terminator: &'a Option<mir::Terminator<'tcx>>) -> Vec<mir::BasicBlock> {
        let Some(terminator) = terminator else { return vec![] };
        match &terminator.kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                self.vars[destination.local]
                    .uses
                    .push(ValueUse::AssignFromCall(&terminator.kind));

                args.iter().map(|x| &x.node).for_each(|op| {
                    match op {
                        mir::Operand::Copy(place) => self.vars[place.local].uses.push(ValueUse::CopyArg),
                        mir::Operand::Move(place) => self.vars[place.local].uses.push(ValueUse::MoveArg),
                        // Don't care
                        mir::Operand::Constant(_) => {},
                    }
                });

                
                let mut next = vec![target.unwrap()];
                if let mir::UnwindAction::Cleanup(bb) = unwind {
                    next.push(*bb)
                }
                next
            },
            // The resurn value is modeled as an assignment to the value `_0` and will be
            // handled by the assign statement. So this is basically a NoOp
            mir::TerminatorKind::Return => vec![],
            mir::TerminatorKind::Goto { target } => vec![*target],
            _ => {
                println!("TODO: Handle terminator: {terminator:#?}");
                vec![]
            },
            // mir::TerminatorKind::SwitchInt { discr, targets } => todo!(),
            // mir::TerminatorKind::UnwindResume => todo!(),
            // mir::TerminatorKind::UnwindTerminate(_) => todo!(),
            // mir::TerminatorKind::Unreachable => todo!(),
            // mir::TerminatorKind::Drop { place, target, unwind, replace } => todo!(),
            // mir::TerminatorKind::Assert { cond, expected, msg, target, unwind } => todo!(),
            // mir::TerminatorKind::Yield { value, resume, resume_arg, drop } => todo!(),
            // mir::TerminatorKind::CoroutineDrop => todo!(),
            // mir::TerminatorKind::FalseEdge { real_target, imaginary_target } => todo!(),
            // mir::TerminatorKind::FalseUnwind { real_target, unwind } => todo!(),
            // mir::TerminatorKind::InlineAsm { template, operands, options, line_spans, destination, unwind } =>
            // todo!(),
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
            .field("checked_bbs", &self.checked_bbs)
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
}

#[derive(Debug)]
enum ValueUse<'a, 'tcx> {
    Assign(&'a mir::Statement<'tcx>),
    AssignFromCall(&'a mir::TerminatorKind<'tcx>),
    /// The value is borrowed into a local
    Borrow(mir::Local),
    /// Moved into a function via arguments
    MoveArg,
    CopyArg,
    /// AKA unhandled for now
    Hmm,
}

impl<'a, 'tcx> ValueUse<'a, 'tcx> {
    /// This function returns the destination of the assignment, if this is an assignment.
    fn assign_place(&self) -> Option<&'a mir::Place<'tcx>> {
        match self {
            Self::Assign(stmt) => {
                let mir::StatementKind::Assign(box (place, _expr)) = &stmt.kind else {unreachable!()};
                Some(place)
            },
            Self::AssignFromCall(mir::TerminatorKind::Call { destination, .. }) => {
                Some(destination)
            },
            _ => None
        }
    }
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
        let mut duck = BorrowAnalysis::new(cx, mir_borrow);
        duck.do_body();

        if cx.tcx.item_name(def.into()).as_str() == "simple_ownership" {
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
