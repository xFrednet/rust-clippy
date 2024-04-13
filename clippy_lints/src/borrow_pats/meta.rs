#[warn(unused)]
use std::collections::BTreeMap;
use std::ops::Range;

use super::{calc_call_local_relations, AnalysisInfo, CfgInfo};

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{Terminator, TerminatorKind, VarDebugInfo, VarDebugInfoContents};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

/// This analysis is special as it is always the first one to run. It collects
/// information about the control flow etc, which will be used by future analysis.
///
/// For better construction and value tracking, it uses reverse order depth search
#[derive(Debug)]
pub struct MetaAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    visited: BitSet<BasicBlock>,
    pub cfg: BTreeMap<BasicBlock, CfgInfo>,
    /// The set defines the loop bbs, and the basic block determines the end of the loop
    pub loops: Vec<(BitSet<BasicBlock>, BasicBlock)>,
    pub terms: BTreeMap<BasicBlock, BTreeMap<Local, Vec<Local>>>,
    pub return_block: BasicBlock,
}

impl<'a, 'tcx> MetaAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        let bbs_len = info.body.basic_blocks.len();
        Self {
            info,
            cfg: Default::default(),
            visited: BitSet::new_empty(bbs_len),
            loops: Default::default(),
            terms: Default::default(),
            return_block: BasicBlock::from_u32(0),
        }
    }

    pub fn run(&mut self) {
        self.collect_loops();

        let (bb, _bbd) = &self
            .info
            .body
            .basic_blocks
            .iter_enumerated()
            .find(|(_bb, bbd)| matches!(bbd.terminator().kind, mir::TerminatorKind::Return))
            .unwrap();

        self.return_block = *bb;
        self.walk_block(*bb);
    }

    fn collect_loops(&mut self) {
        let predecessors = self.info.body.basic_blocks.predecessors();
        for (bb, bbd) in self.info.body.basic_blocks.iter_enumerated() {
            if let TerminatorKind::Goto { target } = bbd.terminator().kind {
                if target < bb {
                    let mut loop_set = BitSet::new_empty(self.info.body.basic_blocks.len());
                    loop_set.insert(target);

                    let mut queue = vec![bb];
                    while let Some(pred) = queue.pop() {
                        if !loop_set.contains(pred) {
                            loop_set.insert(pred);
                            queue.extend_from_slice(&predecessors[pred]);
                        }
                    }

                    self.loops.push((loop_set, bb));
                }
            }
        }
    }

    fn find_loop(&self, bb: BasicBlock) -> Option<&(BitSet<BasicBlock>, BasicBlock)> {
        super::find_loop(&self.loops, bb)
    }

    fn walk_block(&mut self, bb: BasicBlock) {
        if self.visited.contains(bb) {
            return;
        }
        self.visited.insert(bb);

        // Here we also have to traverse everything in reverse order
        let bbd = &self.info.body.basic_blocks[bb];
        self.visit_terminator_for_terms(bbd.terminator(), bb);
        self.visit_terminator_for_cfg(bbd.terminator(), bb);

        let pre_bbs = &self.info.body.basic_blocks.predecessors()[bb];
        for pre_bb in pre_bbs {
            self.walk_block(*pre_bb);
        }
    }

    fn visit_terminator_for_cfg(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        let cfg_info = match &term.kind {
            #[rustfmt::skip]
            mir::TerminatorKind::FalseEdge { real_target: target, .. }
            | mir::TerminatorKind::FalseUnwind { real_target: target, .. }
            | mir::TerminatorKind::Assert { target, .. }
            | mir::TerminatorKind::Call { target: Some(target), .. }
            | mir::TerminatorKind::Drop { target, .. }
            | mir::TerminatorKind::InlineAsm { destination: Some(target), .. }
            | mir::TerminatorKind::Goto { target } => {
                CfgInfo::Linear(*target)
            },
            mir::TerminatorKind::SwitchInt { targets, .. } => {
                if let Some((loop_set, _loop_bb)) = self.find_loop(bb)
                    && let Some((next, brea)) = match targets.all_targets() {
                        [a, b] | [b, a] if !loop_set.contains(*b) => Some((*a, *b)),
                        _ => None,
                    }
                {
                    CfgInfo::Break { next, brea }
                } else {
                    let mut branches = Vec::new();
                    branches.extend_from_slice(targets.all_targets());

                    CfgInfo::Condition { branches }
                }
            },
            #[rustfmt::skip]
            mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::Call { .. }
            | mir::TerminatorKind::InlineAsm { .. } => {
                CfgInfo::None
            },
            mir::TerminatorKind::Return => CfgInfo::Return,
            mir::TerminatorKind::Yield { .. } => unreachable!(),
        };

        self.cfg.insert(bb, cfg_info);
    }

    fn visit_terminator_for_terms(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                assert!(destination.projection.is_empty());
                let dest = destination.local;
                self.terms
                    .insert(bb, calc_call_local_relations(self.info.tcx, func, dest, args));
            },
            _ => {},
        }
    }
}
