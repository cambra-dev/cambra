//! Lowering a program of several modules: each module lowered once, and each
//! run of it created from that lowering (`docs/modules.md`, "A module lowers
//! once").
//!
//! A module lowers to the chain of its top-level statements around
//! [`MODULE_BODY`], a placeholder for the code below it wherever a run of it
//! stands. The chain is not uniquified. A binder is a raw name, a reference to
//! another module's member is a raw name spelled through its qualifier, `m::f`,
//! and a `run` statement is a [`TypedExprNode::Run`] over the rest of the
//! module. The module's [`Interface`] records what it declares, for the modules
//! that reach it to resolve against while they lower.
//!
//! Linking creates each run from its module's chain
//! ([`ProgramLowering::create`]): a copy, with each `Run` replaced by the run it
//! declares, uniquified with the run's home and a scope that maps each qualified
//! spelling to the binder of the run it reaches. Each imported module has one
//! shared run per distinct set of arguments its imports pass, the root has one
//! run, and each `run` statement declares another.

mod imports;
mod interface;
mod link;
mod parameters;
mod scope;
mod types;

use imports::*;
pub use interface::*;
pub use link::*;
pub(super) use parameters::*;
pub use scope::*;
use types::*;

use super::{
    AliasAt, DeclaredSink, LoweringContext, LoweringError, LoweringResult, finish_program,
    library_statement_refusals, lower_module_body, lower_root, sink_site, state_site,
};
use crate::ccl::ccl_utils::{PredMemo, walk_refined_predicates_mut};
use crate::ccl::load::LoadedProgram;
use crate::ccl::module_type::{AliasType, ModuleEntry, ModuleType};
use crate::ccl::names::QualifiedName;
use crate::ccl::scope::{ScopedItemMut, for_each_scoped_item_mut};
use crate::ccl::uniquify;
use crate::ccl::{
    Expr, Home, KeyArgument, Label, Lit, Name, RunPath, SharedRun, Type, TypedExprNode,
};
use crate::chl_parser::ast::{
    AssignTarget, Expr as ChlExpr, KeywordArg, Lit as ChlLit, Module as ChlModule,
    QualifiedName as ParserQualifiedName, Span, Spanned, Stmt as ChlStmt, UnaryOp, WrittenPath,
};
use crate::chl_parser::{FileId, ModulePath, SurfaceBuiltin};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
