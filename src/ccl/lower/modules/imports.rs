//! The shared run each `import` reaches, decided by its module and its arguments
//! (`docs/modules.md`, "Imports").

use super::*;

/// The `import` statement a shared run is created for: the first, in file
/// order, of those that reach it.
#[derive(Debug, Clone)]
pub(super) struct ImportSite {
    pub(super) statement: Span,
    /// Each argument, by its parameter: its span and its value.
    pub(super) arguments: HashMap<SmolStr, (Span, Lit)>,
}

/// The constant `expr` spells, if it is one: a literal, or a negated integer
/// literal.
pub(super) fn constant(expr: &ChlExpr) -> Option<Lit> {
    match expr {
        ChlExpr::Lit(ChlLit::Int(n)) => Some(Lit::Int(*n)),
        ChlExpr::Lit(ChlLit::String(s)) => Some(Lit::String(s.clone())),
        ChlExpr::Lit(ChlLit::Bool(b)) => Some(Lit::Bool(*b)),
        ChlExpr::UnaryOp {
            op: UnaryOp::Neg,
            operand,
        } => match &operand.node {
            ChlExpr::Lit(ChlLit::Int(n)) => Some(Lit::Int(-n)),
            _ => None,
        },
        _ => None,
    }
}
