#![warn(unused)]

use std::collections::BTreeMap;

use hir::def_id::LocalDefId;
use meta::MetaAnalysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_lint::LateContext;
use rustc_middle::mir;
use rustc_middle::mir::{BasicBlock, Local, Place};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use super::body::ReturnPats;
use super::{PatternStorage, PlaceMagic};

use {rustc_borrowck as borrowck, rustc_hir as hir};

mod meta;

pub struct AnalysisInfo<'tcx> {
    pub cx: &'tcx LateContext<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx mir::Body<'tcx>,
    pub def_id: LocalDefId,
    // borrow_set: Rc<borrowck::BorrowSet<'tcx>>,
    // locs:  FxIndexMap<Location, Vec<BorrowIndex>>
    pub cfg: BTreeMap<BasicBlock, CfgInfo>,
    /// The set defines the loop bbs, and the basic block determines the end of the loop
    pub loops: Vec<(BitSet<BasicBlock>, BasicBlock)>,
    pub terms: BTreeMap<BasicBlock, FxHashMap<Local, Vec<Local>>>,
    /// The final block that contains the return.
    pub return_block: BasicBlock,
    pub locals: BTreeMap<Local, LocalInfo<'tcx>>,
    pub return_pats: ReturnPats,
    pub preds: BTreeMap<BasicBlock, BitSet<BasicBlock>>,
    pub preds_unlooped: BTreeMap<BasicBlock, BitSet<BasicBlock>>,
    pub visit_order: Vec<BasicBlock>,
}

impl<'tcx> std::fmt::Debug for AnalysisInfo<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnalysisInfo")
            .field("body", &self.body)
            .field("def_id", &self.def_id)
            .field("cfg", &self.cfg)
            .field("loops", &self.loops)
            .field("terms", &self.terms)
            .field("locals", &self.locals)
            .field("preds", &self.preds)
            .field("preds_unlooped", &self.preds_unlooped)
            .finish()
    }
}

impl<'tcx> AnalysisInfo<'tcx> {
    pub fn new(cx: &LateContext<'tcx>, def_id: LocalDefId) -> Self {
        // This is totally unsafe and I will not pretend it isn't.
        // In this context it is safe, this struct will never outlive `cx`
        let cx = unsafe { core::mem::transmute::<&LateContext<'tcx>, &'tcx LateContext<'tcx>>(cx) };

        let body = cx.tcx.optimized_mir(def_id);

        let meta_analysis = MetaAnalysis::from_body(cx, body);

        // This needs deconstruction to kill the loan of self
        let MetaAnalysis {
            cfg,
            loops,
            terms,
            return_block,
            locals,
            preds,
            preds_unlooped,
            visit_order,
            ..
        } = meta_analysis;

        // Maybe check: borrowck::dataflow::calculate_borrows_out_of_scope_at_location

        Self {
            cx,
            tcx: cx.tcx,
            body,
            def_id,
            cfg,
            loops,
            terms,
            return_block,
            locals,
            return_pats: PatternStorage::new(),
            preds,
            preds_unlooped,
            visit_order,
        }
    }

    pub fn places_conflict(&self, a: Place<'tcx>, b: Place<'tcx>) -> bool {
        borrowck::consumers::places_conflict(
            self.tcx,
            &self.body,
            a,
            b,
            borrowck::consumers::PlaceConflictBias::NoOverlap,
        )
    }

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

#[derive(Debug, Clone)]
pub struct LocalInfo<'tcx> {
    pub kind: LocalKind,
    pub assign_count: u32,
    pub data: DataInfo<'tcx>,
}

impl<'tcx> LocalInfo<'tcx> {
    pub fn new(kind: LocalKind) -> Self {
        Self {
            kind,
            assign_count: 0,
            data: DataInfo::Unresolved,
        }
    }

    pub fn add_assign(&mut self, place: mir::Place<'tcx>, assign: DataInfo<'tcx>) {
        if place.is_part() {
            self.data.part_assign();
        } else if place.just_local() {
            self.assign_count += 1;
            self.data.mix(assign);
        } else {
            todo!("Handle weird assign {place:#?}\n{self:#?}");
        }
    }
}

#[derive(Debug, Clone)]
pub enum LocalKind {
    /// The return local
    Return,
    /// User defined variable
    UserVar(Symbol, VarInfo),
    /// Generated variable, i.e. unnamed
    AnonVar,
    /// This value was previously part of rustc's MIR but is no longer used.
    Unused,
}

impl LocalKind {
    pub fn name(&self) -> Option<Symbol> {
        match self {
            Self::UserVar(name, _) => Some(*name),
            _ => None,
        }
    }

    pub fn is_arg(&self) -> bool {
        match self {
            Self::UserVar(_, info) => info.argument,
            _ => false,
        }
    }
}

#[derive(Clone)]
pub struct VarInfo {
    pub argument: bool,
    /// Indicates if this is mutable
    pub mutable: bool,
    /// Indicates if the value is owned or a reference.
    pub owned: bool,
    /// Indicates if the value is copy
    pub copy: bool,
    /// Indicates if this type needs to be dropped
    pub drop: bool,
}

impl std::fmt::Debug for VarInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "VarInfo({self})")
    }
}
impl std::fmt::Display for VarInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mutable = if self.mutable { "Mutable" } else { "Immutable" };
        let owned = if self.owned { "Owned" } else { "Reference" };
        let argument = if self.argument { "Argument" } else { "Local" };
        let copy = if self.copy { "Copy" } else { "NonCopy" };
        let dropable = if self.drop { "Drop" } else { "NonDrop" };
        write!(f, "{mutable:<9}, {owned:<9}, {argument:<8}, {copy:<7}, {dropable:<7}")
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum DataInfo<'tcx> {
    /// The default value, before it has been resolved. This should never be the
    /// final version.
    Unresolved,
    /// The value is an argument. This will add a *fake* mutation to the mut count
    Argument,
    /// The value has several assignment spots with different data types
    Mixed,
    /// The local is a strait copy from another local, this includes moves
    Local(mir::Local),
    /// A part of a place was moved or copied into this
    Part(mir::Place<'tcx>),
    /// The value is constant, this includes static loans
    Const,
    /// The value is the result of a computation, usually done by function calls
    Computed,
    /// A loan of a place
    Loan(mir::Place<'tcx>),
    /// This value is the result of a cast of a different local. The data
    /// state depends on the case source
    Cast(mir::Local),
    /// The Ctor of a transparent type. This Ctor can be constant, so the
    /// content depends on the used locals
    Ctor(Vec<LocalOrConst>),
}

impl<'tcx> DataInfo<'tcx> {
    pub fn mix(&mut self, new_value: Self) {
        if *self == Self::Unresolved {
            *self = new_value;
        } else if *self != new_value {
            *self = Self::Mixed;
        }
    }

    /// This is used to indicate, that a part of this value was mutated via a projection
    fn part_assign(&mut self) {
        *self = Self::Mixed;
    }
}

#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq)]
pub enum LocalOrConst {
    Local(mir::Local),
    Const,
}

impl From<&mir::Operand<'_>> for LocalOrConst {
    fn from(value: &mir::Operand<'_>) -> Self {
        if let Some(place) = value.place() {
            assert!(place.just_local());
            Self::Local(place.local)
        } else {
            Self::Const
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LocalConstness {
    /// Is const
    #[expect(unused)]
    Const,
    /// Maybe const
    #[expect(unused)]
    Maybe,
    /// Def not const
    #[expect(unused)]
    Nope,
}
