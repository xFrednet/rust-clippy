#![expect(unused)]
#![allow(
    clippy::module_name_repetitions,
    clippy::default_trait_access,
    clippy::wildcard_imports,
    clippy::enum_variant_names
)]
//! # TODOs
//! - [ ] Update meta analysis
//!     - [ ] Handle loops by partially retraverse them
//!         - [ ] Handle loop overwrites for !drop
//! - [ ] Anonymous stuff should be more unified and not broken into borrows etc like it is now.
//!
//! # Done
//! - [x] Determine value reachability (This might only be needed for returns)
//! - [x] Track properties separatly and uniformly (Argument, Mutable, Owned, Dropable)
//! - [x] Handle or abort on feature use
//! - [x] Consider HIR based visitor `rustc_hir_typeck::expr_use_visitor::Delegate`
//! - [-] Update Return analysis (Removed)
//!     - [-] Add Computed to Return
//!     - [-] Check if the relations implied by the function signature aline with usage
//! - [x] Output and summary
//!     - [x] Collect and summarize all data per crate
//!     - [x] The output states need to be sorted... OH NO
//!
//! # Insights:
//! - Loans are basically just special dependent typed
//! - Binary Assign Ops on primitive types result in overwrites instead of `&mut` borrows
//!
//! # Report
//! - Mention Crater Blacklist: <https://github.com/rust-lang/crater/blob/master/config.toml> (170)
//! - Write about fricking named borrows...
//! - MIR can violate rust semantics:
//!     - `(_1 = &(*_2))`
//!     - Two Phased Borrows
//! - Analysis only tracks named values. Anonymous values are generated by Rustc but might change
//!   and are also MIR version specific.
//! - `impl Drop` types behave differently, as fields need to be valid until the `drop()`
//!
//! # Optional and good todos:
//! - [ ] Analysis for named references
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
mod stats;
mod util;
pub use info::*;
pub use rustc_extention::*;
pub use stats::*;
pub use util::*;

const RETURN: Local = Local::from_u32(0);

const OUTPUT_MARKER: &str = "[THESIS-ANALYSIS-OUTPUT]";

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```ignore
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```ignore
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.78.0"]
    pub BORROW_PATS,
    nursery,
    "non-default lint description"
}

impl_lint_pass!(BorrowPats => [BORROW_PATS]);

#[expect(clippy::struct_excessive_bools)]
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
    print_mir: bool,
    print_fns: bool,
    debug_func_name: Symbol,
    stats: CrateStats,
}

impl BorrowPats {
    pub fn new(msrv: Msrv) -> Self {
        // Determined by `check_crate`
        let enabled = true;
        let print_pats = std::env::var("CLIPPY_PETS_PRINT").is_ok();
        let print_call_relations = std::env::var("CLIPPY_PETS_TEST_RELATIONS").is_ok();
        let print_locals = std::env::var("CLIPPY_LOCALS_PRINT").is_ok();
        let print_stats = std::env::var("CLIPPY_STATS_PRINT").is_ok();
        let print_mir = std::env::var("CLIPPY_PRINT_MIR").is_ok();
        let print_fns = std::env::var("CLIPPY_PRINT_FNS").is_ok();

        Self {
            msrv,
            enabled,
            print_pats,
            print_call_relations,
            print_locals,
            print_stats,
            print_mir,
            print_fns,
            debug_func_name: Symbol::intern("super-weird"),
            stats: Default::default(),
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

        if self.print_fns {
            println!("# {body_name:?}");
        }
        if lint_level != Level::Allow && self.print_pats {
            println!("# {body_name:?}");
        }

        if self.print_mir && lint_level == Level::Forbid || body_name == self.debug_func_name {
            print_debug_info(cx, body, def_id);
        }

        let mut info = AnalysisInfo::new(cx, def_id);

        if body_name == self.debug_func_name {
            dbg!(&info);
        }
        let (body_info, mut body_pats) = body::BodyAnalysis::run(&info, def_id, hir_sig, context);
        
        if lint_level != Level::Allow {
            if self.print_call_relations {
                println!("# Relations for {body_name:?}");
                println!("- Incompltete Stats: {:#?}", info.stats.borrow());
                println!("- Called function relations: {:#?}", info.terms);
                println!("- Incompltete Body: {body_info} {body_pats:?}");
                println!();
                panic!();
                return;
            }

            if self.print_locals {
                println!("# Locals");
                println!("{:#?}", info.locals);
            }
        }

        for (local, local_info) in info.locals.iter_enumerated().skip(1) {
            match &local_info.kind {
                LocalKind::Return => unreachable!("Skipped before"),
                LocalKind::UserVar(name, var_info) => {
                    if var_info.owned {
                        let pats = owned::OwnedAnalysis::run(&info, local);
                        if self.print_pats && lint_level != Level::Allow {
                            println!("- {:<15}: ({var_info}) {pats:?}", name.as_str());
                        }

                        self.stats.add_pat(*var_info, pats);
                    } else {
                        // eprintln!("TODO: implement analysis for named refs");
                    }
                },
                LocalKind::AnonVar => continue,
            }
        }

        body::update_pats_from_stats(&mut body_pats, &info);

        if lint_level != Level::Allow {
            if self.print_pats {
                // Return must be printed at the end, as it might be modified by
                // the following analysis thingies
                println!("- Body: {body_info} {body_pats:?}");
            }
            if self.print_stats {
                println!("- Stats: {:#?}", info.stats.borrow());
            }

            if self.print_pats || self.print_stats {
                println!();
            }
        }

        self.stats.add_body(info.body, info.stats.take(), body_info, body_pats);
    }
}

#[expect(clippy::missing_msrv_attr_impl)]
impl<'tcx> LateLintPass<'tcx> for BorrowPats {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        self.enabled = cx.tcx.features().all_features().iter().all(|x| *x == 0);

        if !self.enabled && self.print_pats {
            println!("Disabled due to feature use");
        }
    }

    fn check_crate_post(&mut self, _: &LateContext<'tcx>) {
        if self.enabled {
            let stats = std::mem::take(&mut self.stats);
            let serde = stats.into_serde();
            println!("{OUTPUT_MARKER} {}", serde_json::to_string(&serde).unwrap());
        } else {
            println!(r#"{OUTPUT_MARKER} {{"Disabled due to feature usage"}} "#);
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
                        self.check_fn_body(cx, sub_item.owner_id.def_id, body_id, sig, context);
                    }
                }
            },
            _ => {},
        }
    }

    fn check_trait_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx hir::TraitItem<'tcx>) {
        if let hir::TraitItemKind::Fn(sig, hir::TraitFn::Provided(body_id)) = &item.kind {
            self.check_fn_body(cx, item.owner_id.def_id, *body_id, sig, BodyContext::TraitDef);
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
