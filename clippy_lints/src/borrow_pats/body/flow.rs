use super::super::prelude::*;
use super::AssignInfo;

#[derive(Debug)]
pub struct DfWalker<'a, 'tcx> {
    _info: &'a AnalysisInfo<'tcx>,
    assignments: &'a IndexVec<Local, SmallVec<[AssignInfo<'tcx>; 2]>>,
    child: Local,
    maybe_parents: &'a [Local],
    found_parents: Vec<Local>,
    const_parent: bool,
    computed_parent: bool,
}

impl<'a, 'tcx> DfWalker<'a, 'tcx> {
    pub fn new(
        info: &'a AnalysisInfo<'tcx>,
        assignments: &'a IndexVec<Local, SmallVec<[AssignInfo<'tcx>; 2]>>,
        child: Local,
        maybe_parents: &'a [Local],
    ) -> Self {
        Self {
            _info: info,
            assignments,
            child,
            maybe_parents,
            found_parents: vec![],
            const_parent: false,
            computed_parent: false,
        }
    }

    pub fn walk(&mut self) {
        let mut seen = BitSet::new_empty(self.assignments.len());
        let mut stack = Vec::with_capacity(16);
        stack.push(self.child);

        while let Some(parent) = stack.pop() {
            if self.maybe_parents.contains(&parent) {
                self.found_parents.push(parent);
            }

            for assign in &self.assignments[parent] {
                match assign {
                    AssignInfo::Place { from, .. } | AssignInfo::Dep { from, .. } | AssignInfo::Ctor { from, .. } | AssignInfo::MutRef { loan: from, .. } => {
                        let grandparent = from.local;
                        if seen.insert(grandparent) {
                            stack.push(grandparent);
                        }
                    },
                    AssignInfo::Const { .. } => {
                        self.const_parent = true;
                    },
                    AssignInfo::Calc { .. } => {
                        self.computed_parent = true;
                    },
                }
            }
        }
    }

    pub fn connection_count(&self) -> usize {
        self.found_parents.len()
    }

    pub fn found_connection(&self, maybe_parent: Local) -> bool {
        self.found_parents.contains(&maybe_parent)
    }

    #[expect(unused)]
    pub fn has_const_assign(&self) -> bool {
        self.const_parent
    }

    #[expect(unused)]
    pub fn has_computed_assign(&self) -> bool {
        self.computed_parent
    }
}
