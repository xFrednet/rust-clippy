#![warn(unused)]

use std::collections::BTreeMap;

use hir::def_id::LocalDefId;
use rustc_borrowck::consumers::{get_body_with_borrowck_facts, ConsumerOptions};
use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_lint::LateContext;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, Local, Place};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use super::meta::MetaAnalysis;

use {rustc_borrowck as borrowck, rustc_hir as hir};

pub struct AnalysisInfo<'tcx> {
    pub cx: &'tcx LateContext<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub body: mir::Body<'tcx>,
    pub def_id: LocalDefId,
    pub local_kinds: IndexVec<mir::Local, LocalKind>,
    // borrow_set: Rc<borrowck::BorrowSet<'tcx>>,
    // locs:  FxIndexMap<Location, Vec<BorrowIndex>>
    pub cfg: BTreeMap<BasicBlock, CfgInfo>,
    /// The set defines the loop bbs, and the basic block determines the end of the loop
    pub loops: Vec<(BitSet<BasicBlock>, BasicBlock)>,
    pub terms: BTreeMap<BasicBlock, BTreeMap<Local, Vec<Local>>>,
}

impl<'tcx> std::fmt::Debug for AnalysisInfo<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnalysisInfo")
            .field("body", &self.body)
            .field("def_id", &self.def_id)
            .field("local_kinds", &self.local_kinds)
            .field("cfg", &self.cfg)
            .field("loops", &self.loops)
            .field("terms", &self.terms)
            .finish()
    }
}

impl<'tcx> AnalysisInfo<'tcx> {
    pub fn new(cx: &LateContext<'tcx>, def_id: LocalDefId) -> Self {
        // This is totally unsafe and I will not pretend it isn't.
        // In this context it is safe, this struct will never outlive `cx`
        let cx = unsafe { core::mem::transmute::<&LateContext<'tcx>, &'tcx LateContext<'tcx>>(cx) };

        let borrowck::consumers::BodyWithBorrowckFacts {
            body,
            // borrow_set, location_table
            ..
        } = get_body_with_borrowck_facts(cx.tcx, def_id, ConsumerOptions::RegionInferenceContext);

        // Maybe check: borrowck::dataflow::calculate_borrows_out_of_scope_at_location

        let local_kinds = Self::determine_local_kinds(&body);
        let mut res = Self {
            cx,
            tcx: cx.tcx,
            body,
            def_id,
            local_kinds,
            cfg: Default::default(),
            loops: Default::default(),
            terms: Default::default(),
        };
        res.collect_meta();
        res
    }

    fn determine_local_kinds(body: &mir::Body<'tcx>) -> IndexVec<mir::Local, LocalKind> {
        let mut kinds = IndexVec::default();
        kinds.resize(body.local_decls.len(), LocalKind::AnonVar);

        kinds[mir::Local::from_u32(0)] = LocalKind::Return;
        body.var_debug_info.iter().for_each(|info| {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                let local = place.local;
                // +1, since `_0` is used for the return
                kinds.get_mut(local).map(|kind| {
                    *kind = if local < (body.arg_count + 1).into() {
                        LocalKind::UserArg(info.name)
                    } else {
                        LocalKind::UserVar(info.name)
                    }
                });
            } else {
                todo!("How should this be handled? {info:#?}");
            }
        });

        kinds
    }

    fn collect_meta(&mut self) {
        let mut meta_analysis = MetaAnalysis::new(self);
        meta_analysis.run();

        // This needs deconstruction to kill the loan of self
        let MetaAnalysis { cfg, loops, terms, .. } = meta_analysis;
        self.cfg = cfg;
        self.loops = loops;
        self.terms = terms;
    }

    #[expect(dead_code)]
    pub fn places_conflict(&self, a: Place<'tcx>, b: Place<'tcx>) -> bool {
        borrowck::consumers::places_conflict(
            self.tcx,
            &self.body,
            a,
            b,
            borrowck::consumers::PlaceConflictBias::NoOverlap,
        )
    }

    #[expect(dead_code)]
    pub fn find_loop(&self, bb: BasicBlock) -> Option<&(BitSet<BasicBlock>, BasicBlock)> {
        super::find_loop(&self.loops, bb)
    }
}

#[derive(Debug)]
pub enum CfgInfo {
    /// The basic block is linear or almost linear. This is also the
    /// value used for function calls which could result in unwinds.
    Linear(BasicBlock),
    /// The control flow can diverge after this block and will join
    /// together at `join`
    Condition { branches: Vec<BasicBlock> },
    /// This basic block breaks loop. It could also be the first condition.
    /// This includes the loop conditions at the start. However, it doesn't
    /// have to be the first block of the loop.
    Break { next: BasicBlock, brea: BasicBlock },
    /// This branch doesn't have any successors
    None,
    /// Let's see if we can detect this
    Return,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LocalKind {
    Unknown,
    /// The return local
    Return,
    /// User defined argument
    UserArg(Symbol),
    /// User defined variable
    UserVar(Symbol),
    /// Generated variable, i.e. unnamed
    AnonVar,
    /// An anonymous constant value
    AnonConst,
}

impl LocalKind {
    pub fn name(&self) -> Option<Symbol> {
        match self {
            Self::UserArg(name) | Self::UserVar(name) => Some(*name),
            _ => None,
        }
    }
}
