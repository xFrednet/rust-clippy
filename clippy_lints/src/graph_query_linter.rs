use clippy_utils::is_lint_allowed;
use rustc_hir as hir;
use rustc_hir::intravisit::{self, FnKind, NestedVisitorMap, Visitor};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::hir::map::Map;
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::Span;

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    pub GRAPH_QUERY_LINTER,
    nursery,
    "default lint description"
}

declare_lint_pass!(GraphQueryLinter => [GRAPH_QUERY_LINTER]);

impl LateLintPass<'_> for GraphQueryLinter {
    // A full blown linter would start at the `Crate` node with `check_crate` however this is
    // just a fancy prototype. Therefore, I'll start at the function level with `check_fn` that
    // reduces the complexity (a lot).

    /// This `check_fn` is the entry point to the graph generation later used for linting. Some
    /// arguments are ignored as they provide span or type data that will not be exported as part
    /// of the labeled property graph. They'll later be retrieved from the [`LateContext`].
    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _kind: FnKind<'tcx>,
        _fn_declaration: &'tcx hir::FnDecl<'tcx>,
        _body: &'tcx hir::Body<'tcx>,
        _span: Span,
        hir_id: hir::HirId,
    ) {
        // We'll pass the actual graph creation off to a visitor to use a stack like structure.
        // Similar to how [`rustc_lint::levels::LintLevelsBuilder`] does it.
        if is_lint_allowed(cx, GRAPH_QUERY_LINTER, hir_id) {
            return;
        }
    }
}

struct GraphCreateVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
}

impl<'a, 'tcx> Visitor<'tcx> for GraphCreateVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        // Using `All` here would capture more nodes as items would also be visited and
        // translated into a graph. However, I decided to neglect items for the sake of simplicity
        NestedVisitorMap::OnlyBodies(self.cx.tcx.hir())
    }

    fn visit_param(&mut self, param: &'tcx hir::Param<'tcx>) {
        intravisit::walk_param(self, param)
    }

    fn visit_body(&mut self, b: &'tcx hir::Body<'tcx>) {
        intravisit::walk_body(self, b)
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        intravisit::walk_expr(self, ex)
    }
}
