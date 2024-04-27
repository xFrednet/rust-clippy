#![expect(unused)]
//! # TODOs
//! - [ ] Update meta analysis
//!     - [ ] Handle loops by partially retraverse them
//!     - [ ] Determine value reachability (This might only be needed for returns)
//! - [ ] Update Return analysis
//!     - [ ] Add Computed to Return
//!     - [ ] Check if the relations implied by the function signature aline with usage
//! - [ ] Analysis for named references
//! - [ ] Output and summary
//!     - [ ] Collect and summarize all data per crate
//!     - [ ] The output states need to be sorted... OH NO
//!
//! # Done
//! - [x] Track properties separatly and uniformly (Argument, Mutable, Owned, Dropable)
//! - [x] Handle or abort on feature use
//! - [x] Consider HIR based visitor `rustc_hir_typeck::expr_use_visitor::Delegate`
//!
//! # Insights:
//! - Loans are basically just special dependent typed
//! - Binary Assign Ops on primitive types result in overwrites instead of `&mut` borrows
//!
//! # Report
//! - Mention Crater Blacklist: https://github.com/rust-lang/crater/blob/master/config.toml (170)
//! - Write about fricking named borrows...
//! - MIR can violate rust semantics:
//!     - `(_1 = &(*_2))`
//!     - Two Phased Borrows
//!
//! # Optional and good todos:
//! - Investigate the `explicit_outlives_requirements` lint

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ops::ControlFlow;

use self::body::BodyContext;
use borrowck::borrow_set::BorrowSet;
use borrowck::consumers::calculate_borrows_out_of_scope_at_location;
use clippy_config::msrvs::Msrv;
use clippy_utils::ty::{for_each_ref_region, for_each_region, for_each_top_level_late_bound_region};
use clippy_utils::{fn_has_unsatisfiable_preds, is_lint_allowed};
use hir::def_id::{DefId, LocalDefId};
use hir::{BodyId, HirId, Mutability};
use mid::mir::visit::Visitor;
use mid::mir::Location;
use rustc_borrowck::consumers::{get_body_with_borrowck_facts, ConsumerOptions};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_lint::{LateContext, LateLintPass, Level};
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use rustc_middle::ty::{Clause, List, TyCtxt};
use rustc_session::{declare_lint_pass, impl_lint_pass};
use rustc_span::source_map::Spanned;
use rustc_span::Symbol;

use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

mod body;
mod owned;

mod info;
mod prelude;
mod rustc_extention;
mod util;
pub use info::*;
pub use rustc_extention::*;
pub use util::*;

const RETURN: Local = Local::from_u32(0);

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

impl_lint_pass!(BorrowPats => [BORROW_PATS]);

pub struct BorrowPats {
    msrv: Msrv,
    /// Indicates if this analysis is enabled. It may be disabled in the following cases:
    /// * Nightly features are enabled
    enabled: bool,
    /// Indicates if the collected patterns should be printed for each pattern.
    print_pats: bool,
    print_call_relations: bool,
    print_locals: bool,
    print_stats: bool,
}

impl BorrowPats {
    pub fn new(msrv: Msrv) -> Self {
        // Determined by `check_crate`
        let enabled = true;
        let print_pats = std::env::var("CLIPPY_PETS_PRINT").is_ok();
        let print_call_relations = std::env::var("CLIPPY_PETS_TEST_RELATIONS").is_ok();
        let print_locals = std::env::var("CLIPPY_LOCALS_PRINT").is_ok();
        let print_stats = std::env::var("CLIPPY_STATS_PRINT").is_ok();

        Self {
            msrv,
            enabled,
            print_pats,
            print_call_relations,
            print_locals,
            print_stats,
        }
    }

    fn check_fn_body<'tcx>(
        &mut self,
        cx: &LateContext<'tcx>,
        def_id: LocalDefId,
        body_id: BodyId,
        hir_sig: &hir::FnSig<'tcx>,
        context: BodyContext,
    ) {
        if !self.enabled {
            return;
        }

        if fn_has_unsatisfiable_preds(cx, def_id.into()) {
            return;
        }

        let Some(body_name) = cx.tcx.opt_item_name(def_id.into()) else {
            return;
        };

        let lint_level = cx
            .tcx
            .lint_level_at_node(BORROW_PATS, cx.tcx.local_def_id_to_hir_id(def_id))
            .0;
        let body = cx.tcx.hir().body(body_id);

        if lint_level != Level::Allow && self.print_pats {
            println!("# {body_name:?}");
        }

        if lint_level == Level::Forbid {
            print_debug_info(cx, body, def_id);
        }

        if lint_level != Level::Allow {
            let mut info = AnalysisInfo::new(cx, def_id);

            let (body_info, body_pats, body_stats) = body::BodyAnalysis::run(&info, def_id, hir_sig, context);
            info.stats.replace(body_stats);

            if self.print_call_relations {
                println!("# Relations for {body_name:?}");
                println!("- Self relations: {:#?}", info.stats.borrow());
                println!("- Called function relations: {:#?}", info.terms);
                println!("- Body: {} {:?}", body_info, body_pats);
                println!();
                return;
            }

            if self.print_locals {
                println!("# Locals");
                println!("{:#?}", info.locals);
            }

            for (local, local_info) in info.locals.iter().skip(1) {
                match &local_info.kind {
                    LocalKind::Return => unreachable!("Skipped before"),
                    LocalKind::UserVar(name, var_info) => {
                        if var_info.owned {
                            let pats = owned::OwnedAnalysis::run(&info, *local);
                            if self.print_pats {
                                println!("- {:<15}: ({var_info}) {pats:?}", name.as_str());
                            }
                        } else {
                            eprintln!("TODO: implement analysis for named refs");
                        }
                    },
                    LocalKind::AnonVar | LocalKind::Unused => continue,
                }
            }

            if self.print_pats {
                // Return must be printed at the end, as it might be modified by
                // the following analysis thingies
                println!("- Body: {} {:?}", body_info, body_pats);
            }
            if self.print_stats {
                println!("- Stats: {:#?}", info.stats.borrow());
            }

            if self.print_pats || self.print_stats {
                println!();
            }
        }
    }
}

impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        self.enabled = cx.tcx.features().all_features().iter().all(|x| *x == 0);

        if !self.enabled && self.print_pats {
            println!("Disabled due to feature use");
        }
    }

    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx hir::Item<'tcx>) {
        match &item.kind {
            hir::ItemKind::Fn(sig, _generics, body_id) => {
                self.check_fn_body(cx, item.owner_id.def_id, *body_id, sig, BodyContext::Free);
            },
            hir::ItemKind::Impl(impl_item) => {
                let context = match impl_item.of_trait {
                    Some(_) => BodyContext::TraitImpl,
                    None => BodyContext::Impl,
                };

                for sub_item_ref in impl_item.items {
                    if matches!(sub_item_ref.kind, hir::AssocItemKind::Fn { .. }) {
                        let sub_item = cx.tcx.hir().impl_item(sub_item_ref.id);
                        let (sig, body_id) = sub_item.expect_fn();
                        self.check_fn_body(cx, sub_item.owner_id.def_id, body_id, sig, context)
                    }
                }
            },
            _ => {},
        }
    }

    fn check_trait_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx hir::TraitItem<'tcx>) {
        if let hir::TraitItemKind::Fn(sig, hir::TraitFn::Provided(body_id)) = &item.kind {
            self.check_fn_body(cx, item.owner_id.def_id, *body_id, sig, BodyContext::TraitDef)
        }
    }
}

fn print_debug_info<'tcx>(cx: &LateContext<'tcx>, body: &hir::Body<'tcx>, def: hir::def_id::LocalDefId) {
    println!("=====");
    println!("Body for: {def:#?}");
    let body = cx.tcx.optimized_mir(def);
    print_body(body);
    println!("=====");
}
