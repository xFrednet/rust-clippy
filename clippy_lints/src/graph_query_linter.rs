use clippy_utils::is_lint_allowed;
use rustc_hir as hir;
use rustc_hir::intravisit::{self, FnKind, NestedVisitorMap, Visitor};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::hir::map::Map;
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::Span;

use rusted_cypher::{cypher_stmt, Statement};

use rusted_cypher::GraphClient;

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
        body: &'tcx hir::Body<'tcx>,
        _span: Span,
        hir_id: hir::HirId,
    ) {
        // We'll pass the actual graph creation off to a visitor to use a stack like structure.
        // Similar to how [`rustc_lint::levels::LintLevelsBuilder`] does it.
        if is_lint_allowed(cx, GRAPH_QUERY_LINTER, hir_id) {
            return;
        }

        create_body_graph(cx, body);
    }
}

fn create_body_graph<'tcx>(cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
    let mut query_creator = GraphCreateVisitor::new(cx);

    query_creator.visit_body(body);

    #[rustfmt::skip]
    {
        // Use 
        // ```cmd
        // sudo docker run --publish=7474:7474 --publish=7687:7687 --volume=$HOME/neo4j/data:/data --volume=$HOME/neo4j/logs:/logs neo4j:3.5.29-community`
        // ```
        // to create the docker container. Note that this implementation is using 3.5.
        // Keep the default neo4j user and set the password to pw-clippy-query
    }
    let graph = GraphClient::connect("http://neo4j:pw-clippy-query@localhost:7474/db/data").unwrap();
    let mut query = graph.query();
    query.set_statements(query_creator.query);
    let res = query.send();
    assert!(res.is_ok(), "ERR: {:#?}", res.unwrap_err());
}

fn to_query(hir_id: hir::HirId) -> String {
    assert_eq!(std::mem::size_of::<hir::HirId>(), 8, "The size of HirId is weird");

    // > transmute is **incredibly** unsafe. There are a vast number of ways to cause undefined
    // > behavior with this function. transmute should be the absolute last resort.
    //
    // It's gonna be fine... ~@xFrednet

    let (owner, local_id) = unsafe { std::mem::transmute::<hir::HirId, (u32, u32)>(hir_id) };

    format!("{:08X}-{:08X}", owner, local_id)
}

struct GraphCreateVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    query: Vec<Statement>,
}

impl<'a, 'tcx> GraphCreateVisitor<'a, 'tcx> {
    fn new(cx: &'a LateContext<'tcx>) -> Self {
        Self { cx, query: Vec::new() }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for GraphCreateVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        // Using `All` here would capture more nodes as items would also be visited and
        // translated into a graph. However, I decided to neglect items for the sake of simplicity
        NestedVisitorMap::OnlyBodies(self.cx.tcx.hir())
    }

    fn visit_body(&mut self, body: &'tcx hir::Body<'tcx>) {
        // Create Self node
        let self_id = to_query(body.id().hir_id);
        self.query.push(
            cypher_stmt!(
                "CREATE (:Body {name: 'body', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                    "hir_id" => &self_id,
                    "from_expansion" => body.value.span.from_expansion()
                }
            )
            .unwrap(),
        );

        // Extracting parameters
        for (index, param) in body.params.iter().enumerate() {
            self.query.push(
                cypher_stmt!(
                    "MATCH (parent:Body) where parent.hir_id = {parent_hir_id}
                    CREATE (parent) -[:PARAM {index: {index}}]->(:Param { name: 'param', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                        "parent_hir_id" => &self_id,
                        "index" => index,
                        "hir_id" => &to_query(param.hir_id),
                        "from_expansion" => param.span.from_expansion()
                    }
                )
                .unwrap(),
            );
        }

        intravisit::walk_body(self, body);
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        intravisit::walk_expr(self, ex);
    }
}
