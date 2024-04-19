// Aliases
pub use rustc_middle::mir;

// Traits:
pub use super::rustc_extention::{BodyMagic, LocalMagic, PlaceMagic};
pub use itertools::Itertools;
pub use rustc_lint::LateLintPass;
pub use rustc_middle::mir::visit::Visitor;

// Data Structures
pub use rustc_data_structures::fx::{FxHashMap, FxHashSet};
pub use rustc_index::IndexVec;
pub use std::collections::{BTreeMap, BTreeSet};

// Common Types
pub use super::{AnalysisInfo, LocalKind, Validity};
pub use rustc_ast::Mutability;
pub use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BorrowKind, Local, Location, Operand, Place, PlaceElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, VarDebugInfo, VarDebugInfoContents, START_BLOCK,
};
pub use rustc_span::{sym, Symbol};
