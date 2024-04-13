#[warn(unused)]
use std::collections::BTreeMap;
use std::ops::Range;

use super::{calc_call_local_relations, AnalysisInfo, CfgInfo, LocalAssignInfo, LocalInfo};

use hir::Mutability;
use mid::mir::visit::Visitor;
use mid::mir::{Terminator, TerminatorKind, VarDebugInfo, VarDebugInfoContents};
use mid::ty::TypeVisitableExt;
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
    pub local_infos: BTreeMap<Local, LocalInfo<'tcx>>,
}

impl<'a, 'tcx> MetaAnalysis<'a, 'tcx> {
    pub fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        let local_info_iter = info
            .local_kinds
            .iter_enumerated()
            .map(|(id, kind)| (id, LocalInfo::new(*kind)));
        let mut local_infos = BTreeMap::new();
        local_infos.extend(local_info_iter);

        let bbs_len = info.body.basic_blocks.len();
        Self {
            info,
            cfg: Default::default(),
            visited: BitSet::new_empty(bbs_len),
            loops: Default::default(),
            terms: Default::default(),
            return_block: BasicBlock::from_u32(0),
            local_infos,
        }
    }

    pub fn run(&mut self) {
        self.collect_loops();
        self.visit_body(&self.info.body);
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
            mir::TerminatorKind::Return => {
                self.return_block = bb;
                CfgInfo::Return
            },
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

    fn visit_terminator_for_locals(&mut self, term: &Terminator<'tcx>, bb: BasicBlock) {
        match &term.kind {
            mir::TerminatorKind::Call { destination, .. } => {
                // TODO: Should mut arguments be handled?
                assert!(destination.projection.is_empty());
                let local = destination.local;
                self.local_infos
                    .get_mut(&local)
                    .unwrap()
                    .add_assign(*destination, LocalAssignInfo::Computed);
            },
            _ => {},
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for MetaAnalysis<'a, 'tcx> {
    fn visit_terminator(&mut self, term: &Terminator<'tcx>, loc: mir::Location) {
        self.visit_terminator_for_cfg(term, loc.block);
        self.visit_terminator_for_terms(term, loc.block);
        self.visit_terminator_for_locals(term, loc.block);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rval: &Rvalue<'tcx>, _loc: mir::Location) {
        let local = place.local;

        let assign_info = match rval {
            mir::Rvalue::Ref(_reg, kind, src) => {
                match src.projection.as_slice() {
                    [mir::PlaceElem::Deref] => {
                        // &(*_1) = Copy
                        LocalAssignInfo::Copy(src.local)
                    },
                    _ => LocalAssignInfo::Loan(*src),
                }
            },
            mir::Rvalue::Use(op) => match &op {
                mir::Operand::Copy(other) | mir::Operand::Move(other) => {
                    if other.has_projections() {
                        LocalAssignInfo::Part(*other)
                    } else {
                        LocalAssignInfo::Copy(other.local)
                    }
                },
                mir::Operand::Constant(_) => LocalAssignInfo::Const,
            },
            // Will be handled as computed for now, but in theory this is a clear construction
            Rvalue::Repeat(_, _) |
            Rvalue::Aggregate(_, _) => LocalAssignInfo::Computed,

            // Casts should depend on the input data
            Rvalue::Cast(_, _, _) => todo!("Assign: {place:#?} = {rval:#?}"),

            Rvalue::NullaryOp(_, _) => LocalAssignInfo::Const,

            Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_)
            | Rvalue::BinaryOp(_, _)
            | Rvalue::CheckedBinaryOp(_, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Discriminant(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::CopyForDeref(_) => LocalAssignInfo::Computed,
            
        };

        self.local_infos
            .get_mut(&local)
            .unwrap()
            .add_assign(*place, assign_info);
    }
}
