#![warn(unused)]
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use clippy_utils::ty::{for_each_ref_region, for_each_region};
use rustc_ast::Mutability;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{BasicBlock, Local, Operand};
use rustc_middle::ty::{FnSig, GenericArgsRef, GenericPredicates, Region, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::source_map::Spanned;

use super::AnalysisInfo;

pub struct PrintPrevent<T>(pub T);

impl<T> std::fmt::Debug for PrintPrevent<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("PrintPrevent").finish()
    }
}

/// A helper struct to build relations between function arguments and the return
///
/// I really should stop using such stupid names. At this pooint I'm just making fun
/// of everything to make this work somehow tollerable.
#[derive(Debug)]
struct FuncReals<'tcx> {
    /// A list of several universes
    ///
    /// Mapping from `'short` (key) is outlives by `'long` (value)
    multiverse: BTreeMap<Region<'tcx>, BTreeSet<Region<'tcx>>>,
    sig: FnSig<'tcx>,
}

impl<'tcx> FuncReals<'tcx> {
    fn from_fn_def(tcx: TyCtxt<'tcx>, def_id: DefId, _args: GenericArgsRef<'tcx>) -> Self {
        // FIXME: The proper and long therm solution would be to use HIR
        // to find the call with generics that still have valid region markers.
        // However, for now I need to get this zombie in the air and not pefect
        let fn_sig = tcx.fn_sig(def_id).instantiate_identity();

        // On other functions this shouldn't matter. Even if they have late bounds
        // in their signature. We don't know how it's used and more imporantly,
        // The input and return types still need to follow Rust's type rules
        let fn_sig = fn_sig.skip_binder();

        let mut reals = Self {
            multiverse: Default::default(),
            sig: fn_sig,
        };

        // FYI: Predicates don't include transitive bounds
        let item_predicates = tcx.predicates_of(def_id);
        // TODO Test: `inferred_outlives_of`
        reals.build_multiverse(item_predicates);

        reals
    }

    fn build_multiverse(&mut self, predicates: GenericPredicates<'tcx>) {
        let preds = predicates
            .predicates
            .iter()
            .filter_map(|(clause, _span)| clause.as_region_outlives_clause());

        // I know this can be done in linear time, but I wasn't able to get this to
        // work quickly. So I'll do the n^2 version for now
        for binder in preds {
            // By now I believe (aka. wish) this is unimportant and can be removed.
            // But first I need to find something which actually triggers this todo.
            if !binder.bound_vars().is_empty() {
                todo!("Non empty depressing bounds 2: {binder:#?}");
            }

            let constaint = binder.skip_binder();
            let long = constaint.0;
            let short = constaint.1;

            let longi_verse = self.multiverse.get(&long).cloned().unwrap_or_default();
            let shorti_verse = self.multiverse.entry(short).or_default();
            if !shorti_verse.insert(long) {
                continue;
            }
            shorti_verse.extend(longi_verse);

            for (_, universe) in &mut self.multiverse {
                if universe.contains(&short) {
                    universe.insert(long);
                }
            }
        }
    }

    fn relations(&self, dest: Local, args: &Vec<Spanned<Operand<'tcx>>>) -> FxHashMap<Local, Vec<Local>> {
        let mut reals = FxHashMap::default();
        let ret_rels = self.return_relations();
        if !ret_rels.is_empty() {
            let locals: Vec<_> = ret_rels
                .into_iter()
                .filter_map(|idx| args[idx].node.place())
                .map(|place| place.local)
                .collect();
            reals.insert(dest, locals);
        }

        for (arg_index, arg_ty) in self.sig.inputs().iter().enumerate() {
            let mut arg_rels = FxHashSet::default();
            for_each_ref_region(*arg_ty, &mut |_reg, child_ty, mutability| {
                // `&mut &X` is not really interesting here
                if matches!(mutability, Mutability::Mut) {
                    arg_rels.extend(self.find_relations(child_ty, arg_index));
                }
            });

            if !arg_rels.is_empty() {
                // It has to be a valid place, since we found a location
                let place = args[arg_index].node.place().unwrap();
                assert!(!place.has_projections());

                let locals: Vec<_> = arg_rels
                    .into_iter()
                    .filter_map(|idx| args[idx].node.place())
                    .map(|place| place.local)
                    .collect();
                reals.insert(place.local, locals);
            }
        }

        reals
    }

    /// This function takes an operand, that identifies a function and returns the
    /// indices of the arguments that might be parents of the return type.
    ///
    /// ```
    /// fn example<'c, 'a: 'c, 'b: 'c>(cond: bool, a: &'a u32, b: &'b u32) -> &'c u32 {
    /// #    todo!()
    /// }
    /// ```
    /// This would return [1, 2], since the types in position 1 and 2 are related
    /// to the return type.
    fn return_relations(&self) -> FxHashSet<usize> {
        self.find_relations(self.sig.output(), usize::MAX)
    }

    fn find_relations(&self, child_ty: Ty<'tcx>, child_index: usize) -> FxHashSet<usize> {
        let mut child_regions = FxHashSet::default();
        for_each_region(child_ty, |region| {
            if child_regions.insert(region) {
                if let Some(longer_regions) = self.multiverse.get(&region) {
                    child_regions.extend(longer_regions);
                }
            }
        });

        let mut parents = FxHashSet::default();
        if child_regions.is_empty() {
            return parents;
        }

        for (index, ty) in self.sig.inputs().iter().enumerate() {
            if index == child_index {
                continue;
            }

            // "Here to stab things, don't case"
            for_each_ref_region(*ty, &mut |reg, _ty, _mutability| {
                if child_regions.contains(&reg) {
                    parents.insert(index);
                }
            });
        }

        parents
    }
}

pub fn calc_call_local_relations<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    dest: Local,
    args: &Vec<Spanned<Operand<'tcx>>>,
) -> FxHashMap<Local, Vec<Local>> {
    if let Some((def_id, generic_args)) = func.const_fn_def() {
        let builder = FuncReals::from_fn_def(tcx, def_id, generic_args);
        let relations = builder.relations(dest, args);
        relations
    } else {
        todo!()
    }
}

pub fn find_loop(
    loops: &Vec<(BitSet<BasicBlock>, BasicBlock)>,
    bb: BasicBlock,
) -> Option<&(BitSet<BasicBlock>, BasicBlock)> {
    loops
        .iter()
        .filter(|(set, _)| set.contains(bb))
        .min_by(|(a, _), (b, _)| a.count().cmp(&b.count()))
}

pub trait PatternEnum: Copy + Clone + std::fmt::Debug + std::hash::Hash + Eq + PartialEq + Ord + PartialOrd {}

/// A convinient wrapper to make sure patterns are tracked correctly.
pub struct PatternStorage<T: PatternEnum> {
    pats: RefCell<BTreeSet<T>>,
}

impl<T: PatternEnum> std::fmt::Display for PatternStorage<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.pats.borrow())
    }
}

impl<T: PatternEnum> std::fmt::Debug for PatternStorage<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.pats.borrow().fmt(f)
    }
}

impl<T: PatternEnum> PatternStorage<T> {
    pub fn new() -> Self {
        Self {
            pats: Default::default(),
        }
    }

    pub fn push(&self, new_pat: T) {
        self.pats.borrow_mut().insert(new_pat);
    }

    #[expect(unused)]
    pub fn get(self) -> BTreeSet<T> {
        self.pats.take()
    }
}

/// Indicates the validity of a value.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Validity {
    /// Is valid on all paths
    Valid,
    /// Maybe filled with valid data
    Maybe,
    /// Not filled with valid data
    Not,
}

pub fn visit_body_in_order<'tcx, V: Visitor<'tcx>>(vis: &mut V, info: &AnalysisInfo<'tcx>) {
    for info in &info.body.var_debug_info {
        vis.visit_var_debug_info(info);
    }

    for bb in info.visit_order.iter().copied() {
        vis.visit_basic_block_data(bb, &info.body.basic_blocks[bb]);
    }
}
