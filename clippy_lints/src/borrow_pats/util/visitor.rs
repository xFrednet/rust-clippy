use super::super::prelude::*;
pub trait MyStateInfo<V>: Eq + Clone + std::fmt::Debug + Default {
    /// The return value indicates if the visitor has changed.
    fn join(&mut self, state_owner: &mut V, bb: BasicBlock) -> bool;
}

pub trait MyVisitor<'tcx>: Visitor<'tcx> + std::marker::Sized {
    type State: MyStateInfo<Self>;

    fn init_start_block_state(&mut self);

    fn set_state(&mut self, bb: BasicBlock, state: Self::State);
}

pub fn visit_body_in_order<'tcx, V: MyVisitor<'tcx>>(vis: &mut V, info: &AnalysisInfo<'tcx>) {
    for bb in info.visit_order.iter().copied() {
        // Init state
        if bb == START_BLOCK {
            vis.init_start_block_state();
        } else {
            let preds = &info.preds[&bb];
            let mut state = V::State::default();
            preds.iter().for_each(|bb| {
                state.join(vis, bb);
            });
            vis.set_state(bb, state);
        }

        // Walk block
        vis.visit_basic_block_data(bb, &info.body.basic_blocks[bb]);
    }
}
