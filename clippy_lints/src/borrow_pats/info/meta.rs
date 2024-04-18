use std::collections::{BTreeMap, VecDeque};

use crate::borrow_pats::info::VarInfo;
use crate::borrow_pats::PrintPrevent;

use super::super::{calc_call_local_relations, CfgInfo, DataInfo, LocalInfo, LocalOrConst};
use super::LocalKind;

use clippy_utils::ty::is_copy;
use mid::mir::visit::Visitor;
use mid::mir::{Body, Terminator, TerminatorKind, START_BLOCK};
use mid::ty::{TyCtxt, TypeVisitableExt};
use rustc_data_structures::fx::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_lint::LateContext;
use rustc_middle as mid;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, Local, Place, Rvalue};

/// This analysis is special as it is always the first one to run. It collects
/// information about the control flow etc, which will be used by future analysis.
///
/// For better construction and value tracking, it uses reverse order depth search
#[derive(Debug)]
pub struct MetaAnalysis<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: PrintPrevent<TyCtxt<'tcx>>,
    cx: PrintPrevent<&'tcx LateContext<'tcx>>,
    pub cfg: BTreeMap<BasicBlock, CfgInfo>,
    /// The set defines the loop bbs, and the basic block determines the end of the loop
    pub loops: Vec<(BitSet<BasicBlock>, BasicBlock)>,
    pub terms: BTreeMap<BasicBlock, FxHashMap<Local, Vec<Local>>>,
    pub return_block: BasicBlock,
    pub locals: BTreeMap<Local, LocalInfo<'tcx>>,
    pub preds: BTreeMap<BasicBlock, BitSet<BasicBlock>>,
    pub preds_unlooped: BTreeMap<BasicBlock, BitSet<BasicBlock>>,
    pub visit_order: Vec<BasicBlock>,
}

impl<'a, 'tcx> MetaAnalysis<'a, 'tcx> {
    pub fn from_body(cx: &'tcx LateContext<'tcx>, body: &'a Body<'tcx>) -> Self {
        let mut anly = Self::new(cx, body);
        anly.visit_body(body);
        anly.mark_unused_locals();
        anly.unloop_preds();
        anly.build_trav();

        anly
    }

    pub fn new(cx: &'tcx LateContext<'tcx>, body: &'a Body<'tcx>) -> Self {
        let locals = Self::setup_local_infos(body);
        let bb_len = body.basic_blocks.len();

        let mut preds = BTreeMap::new();
        preds.extend((0..bb_len).map(|bb| (BasicBlock::from_usize(bb), BitSet::new_empty(bb_len))));

        let mut anly = Self {
            body,
            tcx: PrintPrevent(cx.tcx),
            cx: PrintPrevent(cx),
            cfg: Default::default(),
            loops: Default::default(),
            terms: Default::default(),
            return_block: BasicBlock::from_u32(0),
            locals,
            preds,
            preds_unlooped: Default::default(),
            visit_order: Default::default(),
        };

        anly.collect_loops();
        anly
    }

    fn setup_local_infos(body: &mir::Body<'tcx>) -> BTreeMap<Local, LocalInfo<'tcx>> {
        let local_info_iter = body
            .local_decls
            .indices()
            .map(|id| (id, LocalInfo::new(LocalKind::AnonVar)));
        let mut local_infos = BTreeMap::new();
        local_infos.extend(local_info_iter);

        if let Some(info) = local_infos.get_mut(&super::super::RETURN) {
            info.kind = LocalKind::Return;
        }

        // The arg and named variable info will be filled in `visit_debug_info` thingy

        local_infos
    }

    fn collect_loops(&mut self) {
        let predecessors = self.body.basic_blocks.predecessors();
        for (bb, bbd) in self.body.basic_blocks.iter_enumerated() {
            if let TerminatorKind::Goto { target } = bbd.terminator().kind {
                if target < bb {
                    let mut loop_set = BitSet::new_empty(self.body.basic_blocks.len());
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
        super::super::find_loop(&self.loops, bb)
    }

    fn mark_unused_locals(&mut self) {
        self.locals
            .iter_mut()
            .filter(|(_, info)| info.data == DataInfo::Unresolved)
            .for_each(|(_, info)| {
                info.kind = LocalKind::Unused;
            });
    }

    fn unloop_preds(&mut self) {
        let mut unlooped = self.preds.clone();

        if !self.body.basic_blocks.is_cfg_cyclic() {
            self.preds_unlooped = unlooped;
            return;
        }

        for (bb, preds) in &mut unlooped {
            if let Some((loop_set, end_bb)) = self.find_loop(*bb) {
                if preds.contains(*end_bb) {
                    preds.subtract(loop_set);
                }
            }
        }
        self.preds_unlooped = unlooped;
    }

    fn build_trav(&mut self) {
        let bb_len = self.body.basic_blocks.len();
        let mut visited: BitSet<BasicBlock> = BitSet::new_empty(bb_len);
        let mut order: Vec<BasicBlock> = Vec::with_capacity(bb_len);

        let mut buffer_queue = VecDeque::new();
        let mut queue = VecDeque::new();
        queue.push_back(START_BLOCK);
        loop {
            while let Some(bb) = queue.pop_front() {
                if visited.contains(bb) {
                    continue;
                }

                let preds = &self.preds_unlooped[&bb];
                if preds.clone().intersect(&visited) {
                    // Not all prerequisites are fulfilled. This bb will be added again by the other branch
                    continue;
                }

                match &self.cfg[&bb] {
                    CfgInfo::Linear(next) => queue.push_back(*next),
                    CfgInfo::Condition { branches } => queue.extend(branches.iter()),
                    CfgInfo::Break { next, brea } => {
                        queue.push_back(*next);
                        buffer_queue.push_back(*brea);
                    },
                    CfgInfo::None | CfgInfo::Return => {},
                }

                order.push(bb);
                visited.insert(bb);
            }

            if buffer_queue.is_empty() {
                break;
            }

            std::mem::swap(&mut buffer_queue, &mut queue);
        }

        self.visit_order = order;
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
                self.preds.get_mut(target).map(|x| x.insert(bb));
                CfgInfo::Linear(*target)
            },
            mir::TerminatorKind::SwitchInt { targets, .. } => {
                if let Some((loop_set, _loop_bb)) = self.find_loop(bb)
                    && let Some((next, brea)) = match targets.all_targets() {
                        [a, b] | [b, a] if !loop_set.contains(*b) => Some((*a, *b)),
                        _ => None,
                    }
                {
                    self.preds.get_mut(&next).map(|x| x.insert(bb));
                    self.preds.get_mut(&brea).map(|x| x.insert(bb));
                    CfgInfo::Break { next, brea }
                } else {
                    let mut branches = Vec::new();
                    branches.extend_from_slice(targets.all_targets());

                    for target in &branches {
                        self.preds.get_mut(target).map(|x| x.insert(bb));
                    }

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
                    .insert(bb, calc_call_local_relations(self.tcx.0, func, dest, args));
            },
            _ => {},
        }
    }

    fn visit_terminator_for_locals(&mut self, term: &Terminator<'tcx>, _bb: BasicBlock) {
        match &term.kind {
            mir::TerminatorKind::Call { destination, .. } => {
                // TODO: Should mut arguments be handled?
                assert!(destination.projection.is_empty());
                let local = destination.local;
                self.locals
                    .get_mut(&local)
                    .unwrap()
                    .add_assign(*destination, DataInfo::Computed);
            },
            _ => {},
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for MetaAnalysis<'a, 'tcx> {
    fn visit_var_debug_info(&mut self, info: &mir::VarDebugInfo<'tcx>) {
        if let mir::VarDebugInfoContents::Place(place) = info.value {
            assert!(!place.has_projections());
            let local = place.local;
            if let Some(local_info) = self.locals.get_mut(&local) {
                let decl = &self.body.local_decls[local];
                let var_info = VarInfo {
                    argument: info.argument_index.is_some(),
                    mutable: decl.mutability.is_mut(),
                    owned: !decl.ty.is_ref(),
                    copy: is_copy(self.cx.0, decl.ty),
                    // Turns out that both `has_significant_drop` and `has_drop`
                    // return false if only fields require drops. Strings are a
                    // good testing example for this.
                    drop: decl.ty.needs_drop(self.tcx.0, self.cx.0.param_env),
                };

                local_info.kind = LocalKind::UserVar(info.name, var_info);

                if local_info.kind.is_arg() {
                    // +1 since it's assigned outside of the body
                    local_info.assign_count += 1;
                    local_info.add_assign(place, DataInfo::Argument);
                }
            }
        } else {
            todo!("How should this be handled? {info:#?}");
        }
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, loc: mir::Location) {
        self.visit_terminator_for_cfg(term, loc.block);
        self.visit_terminator_for_terms(term, loc.block);
        self.visit_terminator_for_locals(term, loc.block);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rval: &Rvalue<'tcx>, _loc: mir::Location) {
        let local = place.local;

        let assign_info = match rval {
            mir::Rvalue::Ref(_reg, _kind, src) => {
                match src.projection.as_slice() {
                    [mir::PlaceElem::Deref] => {
                        // &(*_1) = Copy
                        DataInfo::Local(src.local)
                    },
                    _ => DataInfo::Loan(*src),
                }
            },
            mir::Rvalue::Use(op) => match &op {
                mir::Operand::Copy(other) | mir::Operand::Move(other) => {
                    if other.has_projections() {
                        DataInfo::Part(*other)
                    } else {
                        DataInfo::Local(other.local)
                    }
                },
                mir::Operand::Constant(_) => DataInfo::Const,
            },

            // Constructed Values
            Rvalue::Aggregate(_, fields) => {
                let parts = fields.iter().map(LocalOrConst::from).collect();
                DataInfo::Ctor(parts)
            },
            Rvalue::Repeat(op, _) => DataInfo::Ctor(vec![op.into()]),

            // Casts should depend on the input data
            Rvalue::Cast(_kind, op, _target) => {
                if let Some(place) = op.place() {
                    assert!(!place.has_projections());
                    DataInfo::Cast(place.local)
                } else {
                    DataInfo::Const
                }
            },

            Rvalue::NullaryOp(_, _) => DataInfo::Const,

            Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_)
            | Rvalue::BinaryOp(_, _)
            | Rvalue::CheckedBinaryOp(_, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Discriminant(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::CopyForDeref(_) => DataInfo::Computed,
        };

        self.locals.get_mut(&local).unwrap().add_assign(*place, assign_info);
    }
}
