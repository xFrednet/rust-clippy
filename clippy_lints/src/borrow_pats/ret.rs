use std::cell::{Cell, RefCell};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{self, BasicBlock, Local, Operand};

use super::AnalysisInfo;

const RETURN: Local = Local::from_u32(0);

#[derive(Debug)]
pub struct ReturnAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    pats: ReturnPats,
    visited: BitSet<BasicBlock>,
}

impl<'a, 'tcx> std::fmt::Display for ReturnAnalysis<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Return: {:?}", self.pats)
    }
}

/// A convinient wrapper to make sure patterns are tracked correctly.
#[derive(Default)]
pub struct ReturnPats {
    has_multiple: Cell<bool>,
    pats: RefCell<Vec<ReturnPat>>,
}

impl std::fmt::Debug for ReturnPats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.pats.fmt(f)
    }
}

impl ReturnPats {
    pub fn push(&self, pat: ReturnPat) {
        assert!(
            pat.is_value(),
            "External analysis should only ever insert value patterns"
        );

        if !self.has_multiple.get() {
            let add_cond = self.pats.borrow().get(0).map(ReturnPat::is_value).unwrap_or_default();
            if add_cond {
                self.push_direct(ReturnPat::ConditionalReturn);
                self.has_multiple.set(true);
            }
        }

        self.push_direct(pat);
    }
    fn push_direct(&self, pat: ReturnPat) {
        if self.pats.borrow().contains(&pat) {
            return;
        }
        if pat.is_value() {
            self.pats.borrow_mut().insert(0, pat);
        } else {
            self.pats.borrow_mut().push(pat);
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum ReturnPat {
    /// Just the unit type is returned, nothing interesting
    Unit,
    /// The return depends on some kind of condition
    ConditionalReturn,

    /// A constant value is returned.
    Const,
    /// A argument is returned
    Argument,
    /// A computed value is returned
    Computed,
    /// A loan to a constant value. This only means that the lifetime can be
    /// static. The lifetime for calling functions still depends on the
    /// function signature.
    StaticLoan,
}

impl ReturnPat {
    fn is_value(&self) -> bool {
        match self {
            ReturnPat::ConditionalReturn | ReturnPat::Unit => false,
            ReturnPat::Const | ReturnPat::Argument | ReturnPat::Computed | ReturnPat::StaticLoan => true,
        }
    }
}

impl<'a, 'tcx> ReturnAnalysis<'a, 'tcx> {
    fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        Self {
            info,
            pats: Default::default(),
            visited: BitSet::new_empty(info.body.basic_blocks.len()),
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>) {
        let mut anly = Self::new(info);

        let decl = &info.body.local_decls[RETURN];
        if decl.ty.is_unit() {
            anly.pats.push(ReturnPat::Const);
            anly.pats.push_direct(ReturnPat::Unit);
        } else {
            println!("Type: {decl:#?}");
            anly.visit_body(&info.body);
        }

        eprintln!("{anly}");
    }
}

impl<'a, 'tcx> Visitor<'tcx> for ReturnAnalysis<'a, 'tcx> {
    fn visit_assign(&mut self, target: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>, _loc: mir::Location) {
        if target.local != RETURN {
            return;
        }

        match &rvalue {
            mir::Rvalue::Use(Operand::Constant(_)) => {
                self.pats.push(ReturnPat::Const);
            },
            mir::Rvalue::Cast(_, _, _) | mir::Rvalue::Use(_) => todo!("Return: {rvalue:#?}"),
            mir::Rvalue::Repeat(_, _) | mir::Rvalue::Aggregate(_, _) => {
                todo!("Return: {rvalue:#?}")
            },

            mir::Rvalue::Ref(_, _, _)
            | mir::Rvalue::ThreadLocalRef(_)
            | mir::Rvalue::AddressOf(_, _)
            | mir::Rvalue::Len(_)
            | mir::Rvalue::BinaryOp(_, _)
            | mir::Rvalue::CheckedBinaryOp(_, _)
            | mir::Rvalue::NullaryOp(_, _)
            | mir::Rvalue::UnaryOp(_, _)
            | mir::Rvalue::Discriminant(_)
            | mir::Rvalue::ShallowInitBox(_, _)
            | mir::Rvalue::CopyForDeref(_) => unreachable!("Return: None of these ops should be inlined {rvalue:#?}"),
        }
    }
}
