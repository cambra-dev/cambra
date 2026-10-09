//! Lowering a program of several modules: each module lowered once, and the
//! shared run of each imported module created from that lowering
//! (`docs/modules.md`, "A module lowers once").
//!
//! A module lowers to the chain of its top-level statements around
//! [`MODULE_BODY`], a placeholder for the code below it wherever a run of it
//! stands. The chain is not uniquified. A binder is a raw name, and a reference
//! to another module's member is a raw name spelled through its qualifier,
//! `m::f`. The module's [`Interface`] records what it declares, for the modules
//! that reach it to resolve against while they lower.
//!
//! Linking creates each imported module's shared run from its chain
//! ([`ProgramLowering::create`]): a copy, uniquified with a scope that maps each
//! qualified spelling to the binder of the run it reaches.
//! The root has one run, and the shared runs' chains wrap it.

mod interface;
mod link;
mod scope;

pub use interface::*;
pub use link::*;
pub use scope::*;

use super::{
    LoweringContext, LoweringError, LoweringResult, lower_library, lower_stmts, sink_site,
};
use crate::ccl::load::{EdgeKind, LoadedProgram};
use crate::ccl::names::QualifiedName;
use crate::ccl::uniquify;
use crate::ccl::{Expr, Label, Name, TypedExprNode};
use crate::chl_parser::ast::{
    AssignTarget, Module as ChlModule, QualifiedName as ParserQualifiedName, Span, Spanned,
    Stmt as ChlStmt,
};
use crate::chl_parser::{FileId, ModulePath};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
