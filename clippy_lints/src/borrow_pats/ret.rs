use std::collections::BTreeMap;
use std::ops::Range;

use super::{AnalysisInfo, CfgInfo};

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{Terminator, TerminatorKind, VarDebugInfo, VarDebugInfoContents};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, FakeReadCause, Local, Place, Rvalue};
use rustc_span::Symbol;
use {rustc_borrowck as borrowck, rustc_hir as hir, rustc_middle as mid};

/// This analysis is special as it is always the first one to run. It collects
/// information about the control flow etc, which will be used by future analysis.
///
/// For better construction and value tracking, it uses reverse order depth search
#[derive(Debug)]
pub struct ReturnAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    inputs: FxHashSet<Local>,
    pats: FxHashSet<Pets>,
    cfg: BTreeMap<BasicBlock, CfgInfo>,
    cfg_stack: Vec<CfgJoinInfo>,
    visited: BitSet<BasicBlock>,
    /// All found loops with the start points in decending order
    /// Example `[6..8, 3..5, 1..9]`
    loops: Vec<Range<BasicBlock>>,
}

impl<'a, 'tcx> std::fmt::Display for ReturnAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Return: {:?}", self.pats)
    }
}

#[derive(Debug)]
enum Pets {
    /// Just the unit type is returned, nothing interesting
    Unit,
    /// A constant value is returned. `Unit` implies this
    Const,
    /// The return depends on some kind of condition
    ConditionalReturn,
    /// An argument is included in the return
    Argument,
}

#[derive(Debug)]
struct CfgJoinInfo(BasicBlock, usize);

impl<'a, 'tcx> ReturnAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        let bbs_len = info.body.basic_blocks.len();
        Self {
            info,
            inputs: Default::default(),
            pats: Default::default(),
            cfg: Default::default(),
            cfg_stack: Default::default(),
            visited: BitSet::new_empty(bbs_len),
            loops: Default::default(),
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
        self.walk_block(*bb);
    }

    fn collect_loops(&mut self) {
        for (bb, bbd) in self.info.body.basic_blocks.iter_enumerated() {
            if let TerminatorKind::Goto { target } = bbd.terminator().kind {
                if target < bb {
                    // I want to have `Ranges` instead of `InclusiveRanges`
                    let stop = BasicBlock::from_u32(bb.as_u32() + 1);
                    self.loops.push(target..stop);
                }
            }
        }

        // Reverse order for cache performence during search :D
        self.loops.sort_by(|a, b| b.start.cmp(&a.start));
    }

    fn find_loop(&self, bb: BasicBlock) -> Option<&Range<BasicBlock>> {
        // Example `[6..8, 3..5, 1..9]`
        //  7 -> Some(6..8)
        //  2 -> Some(1..9)
        // 10 -> None
        self.loops.iter().find(|l| l.contains(&bb))
    }

    fn walk_block(&mut self, bb: BasicBlock) {
        if self.visited.contains(bb) {
            return;
        }
        eprintln!("Visited: {bb:#?}");
        self.visited.insert(bb);

        // Here we also have to traverse everything in reverse order
        let bbd = &self.info.body.basic_blocks[bb];
        self.visit_terminator_for_cfg(bbd.terminator(), bb);
        self.visit_terminator_for_locals(bbd.terminator(), bb);

        // A bias is added to the
        let pre_bbs = &self.info.body.basic_blocks.predecessors()[bb];
        // let loop_bias = self
        //     .find_loop(bb)
        //     .map(|l| pre_bbs.iter().filter(|pre_bb| l.contains(pre_bb)).count())
        //     .unwrap_or_default();
        let incoming_bbs_ctn = pre_bbs.iter().filter(|pre_bb| **pre_bb < bb).count();
        match incoming_bbs_ctn {
            0 | 1 => {},
            len => self.cfg_stack.push(CfgJoinInfo(bb, len)),
        }
        for pre_bb in pre_bbs {
            self.walk_block(*pre_bb);
        }
    }

    fn visit_terminator_for_locals(&mut self, _term: &Terminator<'tcx>, _bb: BasicBlock) {
        eprintln!("TODO: visit_terminator_for_local")
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
                if let Some(loop_range) = self.find_loop(bb)
                    && let Some((next, brea)) = match targets.all_targets() {
                        [a, b] | [b, a] if !loop_range.contains(b) => Some((*a, *b)),
                        _ => None,
                    }
                {
                    self.cfg_stack.retain_mut(|CfgJoinInfo(join_bb, edges)| {
                        if *join_bb == brea {
                            *edges -= 1;
                            *edges == 0
                        } else {
                            true
                        }
                    });

                    CfgInfo::Break { next, brea }
                } else {
                    let CfgJoinInfo(join_bb, edges) = self.cfg_stack.last_mut().unwrap();
                    let mut branches = Vec::new();
                    branches.extend_from_slice(targets.all_targets());
                    let join_bb = *join_bb;

                    *edges -= branches.len();
                    if *edges == 0 {
                        self.cfg_stack.pop();
                    }

                    CfgInfo::Condition {
                        branches,
                        join: join_bb,
                    }
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

    pub fn update_info(&mut self) {
        todo!()
    }
}
