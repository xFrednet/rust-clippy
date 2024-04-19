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
//! # Notes
//! - Insight: Loans are basically just special dependent typed
//!
//! # Optional and good todos:
//! - Investigate the `explicit_outlives_requirements` lint

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::ops::ControlFlow;

use borrowck::borrow_set::BorrowSet;
use borrowck::consumers::calculate_borrows_out_of_scope_at_location;
use clippy_config::msrvs::Msrv;
use clippy_utils::ty::{for_each_ref_region, for_each_region, for_each_top_level_late_bound_region};
use clippy_utils::{fn_has_unsatisfiable_preds, is_lint_allowed};
use hir::def_id::LocalDefId;
use hir::{HirId, Mutability};
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

mod owned;
mod ret;

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
}

impl BorrowPats {
    pub fn new(msrv: Msrv) -> Self {
        // Determined by `check_crate`
        let enabled = true;
        let print_pats = std::env::var("CLIPPY_PETS_PRINT").is_ok();
        let print_call_relations = std::env::var("CLIPPY_PETS_TEST_RELATIONS").is_ok();

        Self {
            msrv,
            enabled,
            print_pats,
            print_call_relations,
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

    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx hir::Body<'tcx>) {
        if !self.enabled {
            return;
        }

        // FIXME: Check what happens for closures
        let def = cx.tcx.hir().body_owner_def_id(body.id());
        let Some(body_name) = cx.tcx.opt_item_name(def.into()) else {
            return;
        };

        // TODO: Mention in report that const can't be considered due to rustc internals
        match cx.tcx.def_kind(def) {
            hir::def::DefKind::Const => return,
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn if fn_has_unsatisfiable_preds(cx, def.into()) => return,
            _ => {},
        }

        let body_hir = cx.tcx.local_def_id_to_hir_id(def);
        let lint_level = cx.tcx.lint_level_at_node(BORROW_PATS, body_hir).0;

        if lint_level != Level::Allow && self.print_pats {
            println!("# {body_name:?}");
        }

        if lint_level == Level::Forbid {
            print_debug_info(cx, body, def);
        }

        if lint_level != Level::Allow {
            let mut info = AnalysisInfo::new(cx, def);
            if self.print_call_relations {
                println!("# Relations for {body_name:?}");
                println!("{:#?}", info.terms);
                return;
            }

            if lint_level == Level::Forbid {
                // println!("{info:#?}");
            }

            info.return_pats = ret::ReturnAnalysis::run(&info);

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
                    LocalKind::AnonVar | LocalKind::Unused => break,
                }
            }

            if self.print_pats {
                // Return must be printed at the end, as it might be modified by
                // the following analysis thingies
                println!("- Return (-, -, -, -, -) {}", info.return_pats);
                println!();
            }
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
