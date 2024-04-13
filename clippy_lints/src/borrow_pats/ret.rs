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
    assigns: u32,
}

/// A convinient wrapper to make sure patterns are tracked correctly.
#[derive(Default)]
pub struct ReturnPats {
    pats: RefCell<Vec<ReturnPat>>,
}

impl std::fmt::Display for ReturnPats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Return: {:?}", self.pats)
    }
}

impl std::fmt::Debug for ReturnPats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.pats.borrow().fmt(f)
    }
}

impl ReturnPats {
    pub fn push(&self, new_pat: ReturnPat) {
        let mut pats = self.pats.borrow_mut();
        if let Some((idx, check_pat)) = pats.iter().take_while(|x| **x <= new_pat).enumerate().last()
            && *check_pat != new_pat
        {
            pats.insert(idx + 1, new_pat);
        } else {
            pats.insert(0, new_pat);
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, PartialOrd)]
pub enum ReturnPat {
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

    /// Just the unit type is returned, nothing interesting
    Unit,
    /// The return depends on some kind of condition
    Conditional,
}

impl<'a, 'tcx> ReturnAnalysis<'a, 'tcx> {
    fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        Self {
            info,
            pats: Default::default(),
            visited: BitSet::new_empty(info.body.basic_blocks.len()),
            assigns: 0,
        }
    }

    pub fn run(info: &'a AnalysisInfo<'tcx>) {
        let mut anly = Self::new(info);

        let decl = &info.body.local_decls[RETURN];
        if decl.ty.is_unit() {
            anly.pats.push(ReturnPat::Const);
            anly.pats.push(ReturnPat::Unit);
        } else {
            println!("Type: {decl:#?}");
            anly.visit_body(&info.body);
            assert!(anly.assigns >= 1);
            if anly.assigns > 1 {
                anly.pats.push(ReturnPat::Conditional);
            }
        }

        eprintln!("{}", anly.pats);
    }
}

impl<'a, 'tcx> Visitor<'tcx> for ReturnAnalysis<'a, 'tcx> {
    fn visit_assign(&mut self, target: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>, _loc: mir::Location) {
        if target.local != RETURN {
            return;
        }

        self.assigns += 1;

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

    fn visit_terminator(&mut self, term: &mir::Terminator<'tcx>, _loc: mir::Location) {
        match &term.kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                if destination.local != RETURN {
                    return;
                }
                assert!(destination.projection.is_empty());

                self.assigns += 1;
                self.pats.push(ReturnPat::Computed);
            },
            _ => {},
        }
    }
}
