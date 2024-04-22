//! This module analyzes the relationship between the function signature and
//! the internal dataflow. Specifically, it checks for the following things:
//!
//! - Might an owned argument be returned
//! - Are arguments stored in `&mut` loans
//! - Are dependent loans returned
//! - Might a returned loan be `'static`
//! - Are all returned values const
//! - Is the unit type returned
//! - How often do `&mut self` refs need to be `&mut`
//! - Are all the dependencies from the function signature used.

#![warn(unused)]

use super::prelude::*;
use super::{calc_fn_arg_relations, visit_body};

mod pattern;
pub use pattern::*;
mod flow;
use flow::*;

use super::{PatternEnum, PatternStorage};

#[derive(Debug)]
pub struct BodyAnalysis<'a, 'tcx> {
    info: &'a AnalysisInfo<'tcx>,
    pats: BTreeSet<BodyPat>,
    data_flow: IndexVec<Local, SmallVec<[AssignInfo<'tcx>; 2]>>,
    stats: BodyStats,
}

/// This indicates an assignment to `to`. In most cases, there is also a `from`.
///
/// TODO: Maybe handle &mut
#[derive(Debug, Copy, Clone)]
enum AssignInfo<'tcx> {
    Place {
        from: Place<'tcx>,
        to: Place<'tcx>,
    },
    Const {
        to: Place<'tcx>,
    },
    Calc {
        to: Place<'tcx>,
    },
    /// This is typical for loans and function calls. If a places might depend
    /// multiple things this will be added mutiple times.
    Dep {
        from: Place<'tcx>,
        to: Place<'tcx>,
    },
    /// A value was constructed with this data
    Ctor {
        from: Place<'tcx>,
        /// The `to` indicates the part of the target, that hols the from value.
        to: Place<'tcx>,
    },
}

impl<'tcx> AssignInfo<'tcx> {
    #[expect(unused)]
    fn to(&self) -> Place<'tcx> {
        match self {
            Self::Place { to, .. }
            | Self::Const { to }
            | Self::Calc { to }
            | Self::Dep { to, .. }
            | Self::Ctor { to, .. } => *to,
        }
    }
}

impl<'a, 'tcx> BodyAnalysis<'a, 'tcx> {
    fn new(info: &'a AnalysisInfo<'tcx>) -> Self {
        let mut data_flow = IndexVec::default();
        data_flow.resize(info.locals.len(), Default::default());
        Self {
            info,
            pats: BTreeSet::default(),
            data_flow,
            stats: Default::default(),
        }
    }

    pub fn run(
        info: &'a AnalysisInfo<'tcx>,
        def_id: LocalDefId,
        hir_sig: &rustc_hir::FnSig<'_>,
        context: BodyContext,
    ) -> (BodyInfo, BTreeSet<BodyPat>, BodyStats) {
        let mut anly = Self::new(info);

        visit_body(&mut anly, info);
        anly.check_fn_relations(def_id);

        let body_info = BodyInfo::from_sig(hir_sig, context);
        (body_info, anly.pats, anly.stats)
    }

    fn check_fn_relations(&mut self, def_id: LocalDefId) {
        let mut rels = calc_fn_arg_relations(self.info.cx.tcx, def_id);
        let return_rels = rels.remove(&RETURN_LOCAL).unwrap_or_default();

        // TODO: Add special check for _0 = `const` | &'static _
        self.check_return_relations(&return_rels);

        // Argument relations
        for (child, maybe_parents) in &rels {
            self.check_arg_relation(child, maybe_parents)
        }
    }

    fn check_return_relations(&mut self, sig_parents: &[Local]) {
        self.stats.return_relations_signature = sig_parents.len();

        let arg_ctn = self.info.body.arg_count;
        let args: Vec<_> = (0..arg_ctn).map(|i| Local::from(i + 1)).collect();

        let mut checker = DfWalker::new(self.info, &self.data_flow, RETURN_LOCAL, &args);
        checker.walk();

        for arg in &args {
            if checker.found_connection(*arg) {
                // These two branches are mutually exclusive:
                if sig_parents.contains(arg) {
                    self.stats.return_relations_found += 1;
                } else if !self.info.body.local_decls[*arg].ty.is_ref() {
                    println!("TODO: Track owned argument returned");
                }
            }
        }

        // let relation_count = 0;
        // relation_count += 1;
        // TODO: Also check for mut borrows here
        // if relation_count == 0 && checker.has_const_assign() && !checker.has_computed_assign() {
        //     self.pats.insert(BodyPat)
        // }
    }

    fn check_arg_relation(&mut self, child: &Local, maybe_parents: &[Local]) {
        let mut checker = DfWalker::new(self.info, &self.data_flow, *child, maybe_parents);
        checker.walk();

        self.stats.arg_relations_signature += maybe_parents.len();
        self.stats.arg_relations_found += checker.connection_count();

        // Debugging
        for maybe in maybe_parents {
            if !checker.found_connection(*maybe) {
                println!("Connection from {child:?} to {maybe:?} was not confirmed");
            }
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for BodyAnalysis<'a, 'tcx> {
    fn visit_assign(&mut self, target: &Place<'tcx>, rval: &Rvalue<'tcx>, _loc: mir::Location) {
        match rval {
            Rvalue::Ref(_reg, _kind, src) => {
                match src.projection.as_slice() {
                    [mir::PlaceElem::Deref] => {
                        // &(*_1) => Copy
                        self.data_flow[target.local].push(AssignInfo::Place {
                            from: *src,
                            to: *target,
                        });
                    },
                    _ => {
                        // _1 = &_2 => simple loan
                        self.data_flow[target.local].push(AssignInfo::Dep {
                            from: *src,
                            to: *target,
                        });
                    },
                }
            },
            Rvalue::Cast(_, op, _) | Rvalue::Use(op) => {
                let event = match &op {
                    Operand::Constant(_) => AssignInfo::Const { to: *target },
                    Operand::Copy(from) | Operand::Move(from) => AssignInfo::Place {
                        from: *from,
                        to: *target,
                    },
                };
                self.data_flow[target.local].push(event);
            },
            Rvalue::CopyForDeref(from) => {
                self.data_flow[target.local].push(AssignInfo::Place {
                    from: *from,
                    to: *target,
                });
            },
            Rvalue::Repeat(op, _) => {
                let event = match &op {
                    Operand::Constant(_) => AssignInfo::Const { to: *target },
                    Operand::Copy(from) | Operand::Move(from) => AssignInfo::Ctor {
                        from: *from,
                        to: *target,
                    },
                };
                self.data_flow[target.local].push(event);
            },
            // Constructed Values
            Rvalue::Aggregate(_, _fields) => {
                todo!();
            },
            // Casts should depend on the input data
            Rvalue::ThreadLocalRef(_)
            | Rvalue::NullaryOp(_, _)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Discriminant(_)
            | Rvalue::ShallowInitBox(_, _)
            | Rvalue::Len(_)
            | Rvalue::BinaryOp(_, _)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::CheckedBinaryOp(_, _) => {
                self.data_flow[target.local].push(AssignInfo::Calc { to: *target });
            },
        }
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, loc: Location) {
        let TerminatorKind::Call { destination: dest, .. } = &term.kind else {
            return;
        };

        let rels = &self.info.terms[&loc.block];

        assert!(dest.just_local());
        if !rels.contains_key(&dest.local) {
            self.data_flow[dest.local].push(AssignInfo::Calc { to: *dest });
        }

        for (target, sources) in rels {
            for src in sources {
                // At this point, I don't care anymore
                let from = unsafe { std::mem::transmute::<Place<'static>, Place<'tcx>>((*src).as_place()) };
                let to = unsafe { std::mem::transmute::<Place<'static>, Place<'tcx>>((*target).as_place()) };
                self.data_flow[*target].push(AssignInfo::Dep { from, to });
            }
        }
    }
}

#[expect(unused)]
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
