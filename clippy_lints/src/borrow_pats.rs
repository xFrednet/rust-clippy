#![expect(unused)]

use rustc_hir as hir;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::declare_lint_pass;

use rustc_middle::mir as mir;

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

declare_lint_pass!(BorrowPats => [BORROW_PATS]);

struct BasicBlock {
    
}

#[derive(Debug)]
struct MyBody<'tcx> {
    mir: &'tcx mir::Body<'tcx>,
}

impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
        // if in_external_macro(cx.tcx.sess, body.value.span) && is_from_proc_macro(cx, &(&kind, body, body.value.hir_id, body.value.span)) {
        //     return;
        // }

        let def = cx.tcx.hir().body_owner_def_id(body.id());
        
        if cx.tcx.item_name(def.into()).as_str() != "simple_ownership" {
            return;
        }
        
        let (mir, _) = cx.tcx.mir_promoted(def);
        print_body(&mir.borrow());
        //let mir = cx.tcx.optimized_mir(def);
        //print_body(mir);
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
