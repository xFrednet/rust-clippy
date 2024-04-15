use std::cell::{Cell, RefCell};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, BasicBlock, Local, Operand, Rvalue};
use rustc_middle::ty::TypeVisitableExt;

use crate::borrow_pats::{DataInfo, LocalConstness};

use super::{AnalysisInfo, PatternEnum, PatternStorage, RETURN};

#[derive(Debug)]
pub struct ReturnAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    pats: ReturnPats,
    visited: BitSet<BasicBlock>,
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ReturnPat {
    /// A constant value is returned.
    Const,
    /// A argument is returned
    Argument,
    /// This is a part of an argument
    ArgumentPart,
    /// A computed value is returned
    Computed,
    /// A loan to a constant value. This only means that the lifetime can be
    /// static. The lifetime for calling functions still depends on the
    /// function signature.
    StaticLoan,

    /// Just the unit type is returned, nothing interesting
    Unit,
    /// The return depends on some kind of condition
    Conditional,
    /// All returned values are constant
    AllConst,
}
impl PatternEnum for ReturnPat {}
pub type ReturnPats = PatternStorage<ReturnPat>;

impl<'a, 'tcx> ReturnAnalysis<'a, 'tcx> {
    fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        Self {
            info,
            pats: PatternStorage::new("Return"),
            visited: BitSet::new_empty(info.body.basic_blocks.len()),
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>) -> ReturnPats {
        let mut anly = Self::new(info);

        let decl = &info.body.local_decls[RETURN];
        if decl.ty.is_unit() {
            anly.pats.push(ReturnPat::Unit);
            anly.pats.push(ReturnPat::Const);
            anly.pats.push(ReturnPat::AllConst);
        } else {
            let return_info = &info.locals[&RETURN];

            match info.local_constness(RETURN) {
                LocalConstness::Const => {
                    anly.pats.push(ReturnPat::Const);
                    anly.pats.push(ReturnPat::AllConst);
                },
                // Here we need to investigate
                LocalConstness::Nope | LocalConstness::Maybe => {
                    // Loans and arguments in the data should be added by the
                    // loans and owned analysis (Famous last words)
                    anly.visit_body(&info.body);
                },
            }

            if return_info.assign_count > 1 {
                anly.pats.push(ReturnPat::Conditional);
            }
        }

        anly.pats
    }
}

impl<'a, 'tcx> Visitor<'tcx> for ReturnAnalysis<'a, 'tcx> {
    fn visit_assign(&mut self, target: &mir::Place<'tcx>, rval: &mir::Rvalue<'tcx>, _loc: mir::Location) {
        if target.local != RETURN {
            return;
        }

        assert!(!target.has_projections());

        match rval {
            mir::Rvalue::Ref(_reg, _kind, src) => {
                match src.projection.as_slice() {
                    [mir::PlaceElem::Deref] => {
                        // &(*_1) = Copy
                        if self.info.local_constness(src.local) == LocalConstness::Const {
                            self.pats.push(ReturnPat::Const)
                        }
                    },
                    _ => {},
                }
            },
            Rvalue::Repeat(op, _) | mir::Rvalue::Use(op) => match &op {
                mir::Operand::Copy(other) | mir::Operand::Move(other) => {
                    if !other.has_projections() && self.info.local_constness(other.local) == LocalConstness::Const {
                        self.pats.push(ReturnPat::Const)
                    }
                },
                mir::Operand::Constant(_) => self.pats.push(ReturnPat::Const),
            },

            // Constructed Values
            Rvalue::Aggregate(_, fields) => {
                let constness = fields
                    .iter()
                    .filter_map(|op| op.place())
                    .map(|place| {
                        assert!(!place.has_projections());
                        self.info.local_constness(place.local)
                    })
                    .max()
                    .unwrap_or(LocalConstness::Const);
                if constness == LocalConstness::Const {
                    self.pats.push(ReturnPat::Const)
                }
            },

            // Casts should depend on the input data
            Rvalue::Cast(_kind, op, _target) => {
                if let Some(place) = op.place() {
                    assert!(!place.has_projections());
                    if self.info.local_constness(place.local) == LocalConstness::Const {
                        self.pats.push(ReturnPat::Const)
                    }
                } else {
                    self.pats.push(ReturnPat::Const)
                }
            },

            Rvalue::NullaryOp(_, _) => self.pats.push(ReturnPat::Const),

            Rvalue::ThreadLocalRef(_)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_)
            | Rvalue::BinaryOp(_, _)
            | Rvalue::CheckedBinaryOp(_, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Discriminant(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::CopyForDeref(_) => {},
        }
    }
}
