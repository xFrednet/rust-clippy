use clippy_utils::is_lint_allowed;
use rustc_hir as hir;
use rustc_hir::intravisit::FnKind;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::Span;

use rusted_cypher::cypher::result::Row;
use rusted_cypher::{cypher_stmt, GraphClient, GraphError, Statement};

const DB_URL: &str = "http://neo4j:pw-clippy-query@localhost:7474/db/data";
const VEC_INIT_THEN_PUSH_QUERY: &str = r#"
MATCH
    (assign {from_expansion: false}),
    (assign)-[:Child {index: 0}]->(var),
    (assign)-[:Child {index: 1}]->(init_call:Call)-[:Child]->(init:Path) 
WHERE 
    (var.name = "Pat" OR var.name = "Path")
    AND (assign.name = "Local" OR assign.name = "Assign")
    AND (init.path CONTAINS 'new' 
        OR init.path CONTAINS 'with_capacity'
        OR init.path CONTAINS 'default')

MATCH
    (scope)-[assign_edge:Child]->(assign),
    (scope)-[next_edge:Child]->(method:MethodCall)
WHERE
    next_edge.index = assign_edge.index + 1
    AND method.ident = "push"

MATCH
    (method)-[:Child {index: 0}]->(self_arg:Path),
    (method)-[:Child {index: 1}]->(push_arg)
WHERE
    1 = 1

return var.hir_id, assign.hir_id, method.hir_id, self_arg.hir_id, push_arg.hir_id
"#;

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

    fn check_crate(&mut self, _: &LateContext<'tcx>) {
        let graph = GraphClient::connect(DB_URL).unwrap();
        graph.exec("MATCH (node) DETACH DELETE (node)").unwrap();
    }

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
        if is_lint_allowed(cx, GRAPH_QUERY_LINTER, hir_id) {
            return;
        }

        // We'll pass the actual graph creation off to a visitor to use a stack like structure.
        // Similar to how [`rustc_lint::levels::LintLevelsBuilder`] does it.
        create_body_graph(cx, body);
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let graph = GraphClient::connect(DB_URL).unwrap();
        let result = match graph.exec(VEC_INIT_THEN_PUSH_QUERY) {
            Ok(result) => result,
            Err(err) => {
                eprintln!("Query Err: {:#?}", err);
                return;
            },
        };

        for row in result.rows() {
            if let Err(err) = process_vec_init_then_push_row(cx, row) {
                eprintln!("Row Err: {:#?}", err);
            }
        }
    }
}

fn process_vec_init_then_push_row(_cx: &LateContext<'tcx>, row: Row<'_>) -> Result<(), GraphError> {
    let _ = deserialize_hir_id(row.get("var.hir_id")?);
    let _ = deserialize_hir_id(row.get("assign.hir_id")?);
    let _ = deserialize_hir_id(row.get("method.hir_id")?);
    let _ = deserialize_hir_id(row.get("self_arg.hir_id")?);
    let _ = deserialize_hir_id(row.get("push_arg.hir_id")?);
    Ok(())
}

fn create_body_graph<'tcx>(cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
    let mut query_creator = GraphCreateVisitor::new(cx);

    query_creator.visit_body(body);

    #[rustfmt::skip]
    {
        // Use 
        // ```cmd
        // sudo docker run --publish=7474:7474 --publish=7687:7687 --volume=$home/neo4j/data:/data --volume=$home/neo4j/logs:/logs neo4j:3.5.29-community
        // ```
        // to create the docker container. Note that this implementation is using 3.5.
        // Keep the default neo4j user and set the password to pw-clippy-query
    }
    let graph = GraphClient::connect(DB_URL).unwrap();
    let mut query = graph.query();
    query.set_statements(query_creator.query);
    let res = query.send();
    assert!(res.is_ok(), "ERR: {:#?}", res.unwrap_err());
}

fn serialize_hir_id(hir_id: hir::HirId) -> String {
    assert_eq!(std::mem::size_of::<hir::HirId>(), 8, "The size of HirId is weird");

    // > transmute is **incredibly** unsafe. There are a vast number of ways to cause undefined
    // > behavior with this function. transmute should be the absolute last resort.
    //
    // It's gonna be fine... ~@xFrednet

    let (owner, local_id) = unsafe { std::mem::transmute::<hir::HirId, (u32, u32)>(hir_id) };

    format!("{:08X}-{:08X}", owner, local_id)
}

fn deserialize_hir_id(hir_id_str: String) -> hir::HirId {
    assert_eq!(std::mem::size_of::<hir::HirId>(), 8, "The size of HirId is weird");

    let (owner_str, local_id_str) = hir_id_str.split_once("-").unwrap();
    let owner_int = u32::from_str_radix(owner_str, 16).unwrap();
    let local_id_int = u32::from_str_radix(local_id_str, 16).unwrap();

    unsafe { std::mem::transmute::<(u32, u32), hir::HirId>((owner_int, local_id_int)) }
}

struct GraphCreateVisitor<'a, 'tcx> {
    #[allow(dead_code)]
    cx: &'a LateContext<'tcx>,
    query: Vec<Statement>,
}

impl<'a, 'tcx> GraphCreateVisitor<'a, 'tcx> {
    fn new(cx: &'a LateContext<'tcx>) -> Self {
        Self { cx, query: Vec::new() }
    }
}

#[rustfmt::skip]
impl<'a, 'tcx> GraphCreateVisitor<'a, 'tcx> {

    fn create_link(&mut self, from_hir_id: hir::HirId, edge: &str, index: usize, to_hir_id: hir::HirId) {
        let from_hir_id = serialize_hir_id(from_hir_id);
        let to_hir_id = serialize_hir_id(to_hir_id);

        self.query.push(cypher_stmt!(
            r#"
            MATCH (from), (to)
                where from.hir_id = {from_hir_id} AND to.hir_id = {to_hir_id}
            CREATE (from)-[:Child {name: {edge}, index: {index}}]->(to)"#, {
                "from_hir_id" => &from_hir_id,
                "to_hir_id" => &to_hir_id,
                "edge" => edge,
                "index" => index
            }
        )
        .unwrap());
    }

    fn visit_body(&mut self, body: &'tcx hir::Body<'tcx>) {
        // Create Self node
        let self_hir_id = body.id().hir_id;
        self.query.push(
            cypher_stmt!(
                "CREATE (:Body {name: 'body', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                    "hir_id" => &serialize_hir_id(self_hir_id),
                    "from_expansion" => body.value.span.from_expansion()
                }
            )
            .unwrap(),
        );

        // Extracting parameters
        for (index, param) in body.params.iter().enumerate() {
            self.query.push(
                cypher_stmt!(
                    "CREATE (:Param { name: 'param', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                        "hir_id" => &serialize_hir_id(param.hir_id),
                        "from_expansion" => param.span.from_expansion()
                    }
                )
                .unwrap(),
            );
            self.create_link(self_hir_id, "Param", index, param.hir_id)
        }

        let child_hir_id = self.visit_expr(&body.value);
        self.create_link(self_hir_id, "Child", 0, child_hir_id)
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) -> hir::HirId {
        let from_expansion = ex.span.from_expansion();
        let self_hir_id = ex.hir_id;
        let hir_id = serialize_hir_id(self_hir_id);

        match &ex.kind {
            hir::ExprKind::Err
                | hir::ExprKind::ConstBlock(..)
                | hir::ExprKind::Box(..)
                | hir::ExprKind::InlineAsm(..)
                | hir::ExprKind::LlvmInlineAsm(..)
                | hir::ExprKind::Struct(..)
                | hir::ExprKind::Repeat(..)
                | hir::ExprKind::Yield(..)
                | hir::ExprKind::Closure(..)
                | hir::ExprKind::Cast(..)
                | hir::ExprKind::Type(..) => unimplemented!("Ignored for the sake of simplicity {:#?}", ex),
            hir::ExprKind::DropTemps(..) => {
                // Accepted ignore
            }
            hir::ExprKind::Tup(args) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Tup {name: 'Tup', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                for (index, child) in args.iter().enumerate() {
                    let child_hir_id = self.visit_expr(child);
                    self.create_link(ex.hir_id, "Child", index, child_hir_id);
                }
            }
            hir::ExprKind::Array(args) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Array {name: 'Array', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                for (index, child) in args.iter().enumerate() {
                    let child_hir_id = self.visit_expr(child);
                    self.create_link(ex.hir_id, "Child", index, child_hir_id);
                }
            },
            hir::ExprKind::Call(call, args) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Call {name: 'Call', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );
                
                let call_hir_id = self.visit_expr(call);
                self.create_link(ex.hir_id, "Call", 0, call_hir_id);

                for (index, child) in args.iter().enumerate() {
                    let child_hir_id = self.visit_expr(child);
                    self.create_link(ex.hir_id, "Child", index, child_hir_id);
                }
            },
            hir::ExprKind::MethodCall(path_seg, _span1, args, _span2) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:MethodCall {name: 'MethodCall', hir_id: {hir_id}, from_expansion: {from_expansion}, ident: {ident}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "ident" => &format!("{}", &path_seg.ident.as_str())
                        }
                    )
                    .unwrap(),
                );

                for (index, child) in args.iter().enumerate() {
                    let child_hir_id = self.visit_expr(child);
                    self.create_link(ex.hir_id, "Child", index, child_hir_id);
                }
            },
            hir::ExprKind::Binary(op, left, right) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:AssignOp {name: 'AssignOp', hir_id: {hir_id}, from_expansion: {from_expansion}, op: {op}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "op" => &format!("{:?}", op)
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(left);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);

                let child_hir_id = self.visit_expr(right);
                self.create_link(ex.hir_id, "Child", 1, child_hir_id);
            },
            hir::ExprKind::Unary(op, expr) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:AssignOp {name: 'AssignOp', hir_id: {hir_id}, from_expansion: {from_expansion}, op: {op}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "op" => &format!("{:?}", op)
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(expr);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);
            },
            hir::ExprKind::Let(pat, expr, _span) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Let {name: 'Let', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let pat_hir_id = self.visit_pat(pat);
                self.create_link(ex.hir_id, "Child", 0, pat_hir_id);

                let child_hir_id = self.visit_expr(expr);
                self.create_link(ex.hir_id, "Child", 1, child_hir_id);
            },
            hir::ExprKind::If(condition, then_expr, else_expr) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:If {name: 'If', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let condition_hir_id = self.visit_expr( condition);
                self.create_link(ex.hir_id, "Condition", 0, condition_hir_id);

                let then_hir_id = self.visit_expr( then_expr);
                self.create_link(ex.hir_id, "Then", 0, then_hir_id);

                if let Some(else_expr) = else_expr {
                    let else_hir_id = self.visit_expr( else_expr);
                    self.create_link(ex.hir_id, "Else", 0, else_hir_id);
                }
            },
            hir::ExprKind::Loop(block, _label, _source, _span) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Loop {name: 'Loop', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_block( block);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);
            },
            hir::ExprKind::Match(scrutinee, arms, _source) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Match {name: 'Match', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let scrutinee_hir_id = self.visit_expr(scrutinee);
                self.create_link(self_hir_id, "Child", 0, scrutinee_hir_id);

                for (index, arm) in arms.iter().enumerate() {
                    let arm_hir_id = arm.hir_id;
                    self.query.push(
                        cypher_stmt!(
                            "CREATE (:Arm {name: 'Arm', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                                "hir_id" => &serialize_hir_id(arm.hir_id),
                                "from_expansion" => from_expansion
                            }
                        )
                        .unwrap(),
                    );
                    self.create_link(self_hir_id, "Arm", index, arm_hir_id);

                    if let Some(_guard) = &arm.guard {
                        unimplemented!();
                    }

                    let child_hir_id = self.visit_expr(arm.body);
                    self.create_link(arm.hir_id, "Child", 0, child_hir_id);
                }
            },
            hir::ExprKind::Block(block, _) => {
                return self.visit_block(block);
            },
            hir::ExprKind::Assign(value, expr, _) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Assign {name: 'Assign', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(value);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);

                let child_hir_id = self.visit_expr(expr);
                self.create_link(ex.hir_id, "Child", 1, child_hir_id);
            },
            hir::ExprKind::AssignOp(op, value, expr) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:AssignOp {name: 'AssignOp', hir_id: {hir_id}, from_expansion: {from_expansion}, op: {op}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "op" => &format!("{:?}", op)
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(value);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);

                let child_hir_id = self.visit_expr(expr);
                self.create_link(ex.hir_id, "Child", 1, child_hir_id);
            },
            hir::ExprKind::Field(value, ident) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Field {name: 'Field', hir_id: {hir_id}, from_expansion: {from_expansion}, ident: {ident}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "ident" => &*ident.as_str()
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(value);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);
            },
            hir::ExprKind::Index(value, index) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Index {name: 'Index', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(value);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);

                let child_hir_id = self.visit_expr(index);
                self.create_link(ex.hir_id, "Index", 0, child_hir_id);
            },
            hir::ExprKind::Path(path) => {
                let path_str = match path {
                    hir::QPath::Resolved(_, path) => {
                        path.segments.iter().fold(String::new(), |mut acc, seg| {
                            acc.push_str(&seg.ident.as_str());
                            acc
                        })
                    },
                    hir::QPath::TypeRelative(ty, path_seg) => {
                        format!("{:?}::{:?}", ty, path_seg.ident.as_str())
                        // if let hir::Adt(adt, _) = ty.kind {
                        //     let path = self.cx.get_def_path(adt.did).iter().fold(String::new(), |acc, sym| {
                        //         acc.push_str(&sym.as_str());
                        //         acc
                        //     });
                        //     path.push_str(&path_seg.ident.as_str());
                        //     path
                        // } else {
                        //     unimplemented!()
                        // }
                    },
                    hir::QPath::LangItem(..) => unimplemented!(),
                };

                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Path {name: 'Path', hir_id: {hir_id}, from_expansion: {from_expansion}, path: {path}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "path" => &path_str
                        }
                    )
                    .unwrap(),
                );
            },
            hir::ExprKind::AddrOf(borrow_kind, mutability, value) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:AddrOf {name: 'AddrOf', hir_id: {hir_id}, from_expansion: {from_expansion}, borrow_kind: {borrow_kind}, mutability: {mutability}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "borrow_kind" => &format!("{:?}", borrow_kind),
                            "mutability" => &format!("{:?}", mutability)
                        }
                    )
                    .unwrap(),
                );

                let child_hir_id = self.visit_expr(value);
                self.create_link(ex.hir_id, "Child", 0, child_hir_id);
            },
            hir::ExprKind::Break(dest, value) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Break {name: 'Break', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                if let Ok(target) = dest.target_id {
                    self.create_link(ex.hir_id, "Jump", 0, target);
                }

                if let Some(value) = value {
                    let child_hir_id = self.visit_expr(value);
                    self.create_link(ex.hir_id, "Child", 0, child_hir_id);
                }
            },
            hir::ExprKind::Continue(dest) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Continue {name: 'Continue', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );
                
                if let Ok(target) = dest.target_id {
                    self.create_link(ex.hir_id, "Jump", 0, target);
                }
            },
            hir::ExprKind::Ret(value) => {
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Return {name: 'Return', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                if let Some(value) = value {
                    let child_hir_id = self.visit_expr(value);
                    self.create_link(ex.hir_id, "Child", 0, child_hir_id);
                }
            },
            hir::ExprKind::Lit(lit) => {
                let value = format!("{:?}", lit.node);
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Lit {name: 'Lit', hir_id: {hir_id}, from_expansion: {from_expansion}, value: {value}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion,
                            "value" => &value
                        }
                    )
                    .unwrap(),
                );
            },
        }

        ex.hir_id
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) -> hir::HirId {
        let from_expansion = block.span.from_expansion();
        let hir_id = serialize_hir_id(block.hir_id);

        self.query.push(
            cypher_stmt!(
                "CREATE (:Block {name: 'Block', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                    "hir_id" => &hir_id,
                    "from_expansion" => from_expansion
                }
            )
            .unwrap(),
        );

        for (index, stmt) in block.stmts.iter().enumerate() {
            let child_hir_id = self.visit_stmt(stmt);
            self.create_link(block.hir_id, "Child", index, child_hir_id);
        }

        if let Some(value) = block.expr {
            let child_hir_id = self.visit_expr(value);
            self.create_link(block.hir_id, "Expr", 0, child_hir_id);
        }

        block.hir_id
    }

    fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> hir::HirId {
        match stmt.kind {
            hir::StmtKind::Local(local) => {
                let from_expansion = stmt.span.from_expansion();
                let hir_id = serialize_hir_id(local.hir_id);
                self.query.push(
                    cypher_stmt!(
                        "CREATE (:Local {name: 'Local', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                            "hir_id" => &hir_id,
                            "from_expansion" => from_expansion
                        }
                    )
                    .unwrap(),
                );

                let pat_hir_id = self.visit_pat(local.pat);
                self.create_link(local.hir_id, "Child", 0, pat_hir_id);

                if let Some(value) = local.init {
                    let child_hir_id = self.visit_expr(value);
                    self.create_link(local.hir_id, "Child", 1, child_hir_id);
                }

                local.hir_id
            },
            hir::StmtKind::Expr(expr) | hir::StmtKind::Semi(expr) => {
                self.visit_expr(expr)
            },
            hir::StmtKind::Item(_item_id) => unimplemented!(),
        }
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) -> hir::HirId {
        let from_expansion = pat.span.from_expansion();
        let hir_id = serialize_hir_id(pat.hir_id);
        self.query.push(
            cypher_stmt!(
                "CREATE (:Pat {name: 'Pat', hir_id: {hir_id}, from_expansion: {from_expansion}})", {
                    "hir_id" => &hir_id,
                    "from_expansion" => from_expansion
                }
            )
            .unwrap(),
        );

        pat.hir_id
    }
}
