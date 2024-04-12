use super::{AnalysisInfo, CfgInfo};

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{Terminator, VarDebugInfo, VarDebugInfoContents};
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
    cfg: FxHashMap<BasicBlock, CfgInfo>,
    cfg_stack: Vec<CfgConstructionInfo>,
    visited: BitSet<BasicBlock>,
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
enum CfgConstructionInfo {
    /// A block that rejoins control flow. The second argument is the number of
    /// incoming edges
    Join(BasicBlock, usize),
    LoopJmp(BasicBlock),
}

impl<'a, 'tcx> ReturnAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        Self {
            info,
            inputs: Default::default(),
            pats: Default::default(),
            cfg: Default::default(),
            cfg_stack: Default::default(),
            visited: BitSet::new_empty(info.body.basic_blocks.len()),
        }
    }

    pub fn run(&mut self) {
        let bbs = &self.info.body.basic_blocks;
        self.walk_block(bbs.last_index().unwrap());
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

        let pre_bbs = &self.info.body.basic_blocks.predecessors()[bb];
        match pre_bbs.len() {
            0 | 1 => {},
            len => self.cfg_stack.push(CfgConstructionInfo::Join(bb, len)),
        }
        for pre_bb in pre_bbs {
            self.walk_block(*pre_bb);
        }
    }

    fn visit_terminator_for_locals(&mut self, _term: &Terminator<'tcx>, _bb: BasicBlock) {
        eprintln!("TODO: visit_terminator_for_local")
    }

    fn visit_terminator_for_cfg(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        #[rustfmt::skip]
        let cfg_info = match &term.kind {
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
                // Should always be valid since every switch needs a join
                let join = self.cfg_stack.last_mut().unwrap();
                if let CfgConstructionInfo::Join(join_bb, edges) = join {
                    let mut branches = Vec::new();
                    branches.extend_from_slice(targets.all_targets());
                    let join_bb = *join_bb;

                    *edges -= branches.len();
                    if *edges == 0 {
                        println!("Pop: {:#?}", &self.cfg_stack);
                        self.cfg_stack.pop();
                    }

                    CfgInfo::Condition {
                        branches,
                        join: join_bb,
                    }
                } else {
                    unreachable!()
                }
            },
            mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::Call { .. }
            | mir::TerminatorKind::InlineAsm { destination: None, .. } => {
                CfgInfo::None
            },
            mir::TerminatorKind::Return => {
                CfgInfo::Return
            },
            mir::TerminatorKind::Yield { .. } => unreachable!(),
        };
        self.cfg.insert(bb, cfg_info);
    }

    pub fn update_info(&mut self) {
        todo!()
    }
}
