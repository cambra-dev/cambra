//! The `requires` and `causes` clauses of a `def` and of a written function type, lowered to
//! the [`Written`] clauses a [`Type::Fun`](crate::ccl::Type::Fun) carries into inference
//! (`docs/chl-spec.md`, "Writing requirements and effects").
//!
//! A `requires` clause holds trait requirements beside context requirements. The trait ones
//! are a polymorphic definition's, lowered with its type parameters
//! (`super::stmts::lower_named_requirements`); the rest are what a call's context supplies.
//! A name in `Write(x)`, `Append(x)` or `Read(x)` is lowered raw, and `uniquify` resolves it
//! against the scope the clause is written in.

use chl_parser::ast::{
    Clause, Expr as ChlExpr, Requirement as ChlRequirement, Span, Spanned, TraitType,
};

use super::LoweringError;
use crate::ccl::Name;
use crate::ccl::effects::{Effect, EffectSet, Requirement, Written};
use crate::ccl::infer::solver::traits::Trait;

/// Whether a `requires` item names a context trait, or is `_`, rather than a trait instance
/// search answers.
pub(super) fn is_context_item(item: &ChlRequirement) -> bool {
    match item {
        ChlRequirement::Trait { ty, .. } => {
            ty.name == "_" || Trait::context_named(&ty.name).is_some()
        }
        ChlRequirement::Bound { .. } => false,
    }
}

/// Where a pair of clauses is written: what a clause without `only` admits beyond its items.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Site {
    /// A `def`: a clause without `only` is a lower bound.
    Def,
    /// A written function type: each clause is exact, and only `_` admits more.
    Type,
}

/// The clauses `requires` (its context items) and `causes` state at `site`. A `requires`
/// clause's trait requirements are not read here.
///
/// A `def` with neither clause written states nothing, `None`. A function type with neither
/// requires nothing and causes nothing, exactly, and `written_at` is where it is written.
pub(super) fn lower_clauses(
    requires: &Clause<ChlRequirement>,
    causes: &Clause<TraitType>,
    site: Site,
    written_at: Span,
) -> Result<Option<Written>, LoweringError> {
    let at = match (requires.span, causes.span) {
        (None, None) if site == Site::Def => return Ok(None),
        (None, None) => written_at,
        (Some(r), Some(c)) => r.join(c),
        (Some(at), None) | (None, Some(at)) => at,
    };
    let mut set = EffectSet::default();
    let mut hole_requires = false;
    for item in requires.items.iter().filter(|r| is_context_item(&r.node)) {
        match context_requirement(item)? {
            Some(r) => {
                set.requires.insert(r);
            }
            None => hole_requires = true,
        }
    }
    let mut hole_causes = false;
    for item in &causes.items {
        match effect(item)? {
            Some(e) => {
                set.causes.insert(e);
            }
            None => hole_causes = true,
        }
    }
    let open_requires = bound(requires, hole_requires, site)?;
    let open_causes = bound(causes, hole_causes, site)?;
    Ok(Some(Written {
        set,
        open_requires,
        open_causes,
        at,
        of_def: site == Site::Def,
    }))
}

/// Whether `clause` admits what inference adds, given whether it lists `_`.
fn bound<T>(clause: &Clause<T>, hole: bool, site: Site) -> Result<bool, LoweringError> {
    match clause.only {
        Some(only) if hole => Err(LoweringError::unsupported(
            only,
            "`only` makes a clause an upper bound, and `_` leaves it open to what inference \
             adds; write one of them",
        )),
        Some(only) if site == Site::Type && !clause.items.is_empty() => {
            Err(LoweringError::unsupported(
                only,
                "a function type's clauses are exact, so `only` belongs to a `def`",
            ))
        }
        Some(_) => Ok(false),
        None => Ok(hole || site == Site::Def),
    }
}

/// The context requirement `item` names, or `None` for `_`.
fn context_requirement(
    item: &Spanned<ChlRequirement>,
) -> Result<Option<Requirement>, LoweringError> {
    let ChlRequirement::Trait { binder, ty } = &item.node else {
        unreachable!("a bound is no context requirement");
    };
    if let Some(binder) = binder {
        return Err(LoweringError::unsupported(
            binder.span,
            format!(
                "a context requirement binds no instance: `{}` is supplied by its context",
                ty.name
            ),
        ));
    }
    match (ty.name.as_str(), ty.args.as_slice()) {
        ("_", []) => Ok(None),
        ("Ext", []) => Ok(Some(Requirement::ext())),
        ("Read", [x]) => Ok(Some(Requirement::read(variable(x, "Read")?))),
        ("Transaction", _) => Err(LoweringError::unsupported(
            ty.name_span,
            "`Transaction` is not supported yet: transactions as contextual parameters are \
             not implemented",
        )),
        (name, _) => Err(arity(item.span, name)),
    }
}

/// The effect `item` names, or `None` for `_`.
fn effect(item: &Spanned<TraitType>) -> Result<Option<Effect>, LoweringError> {
    let ty = &item.node;
    match (ty.name.as_str(), ty.args.as_slice()) {
        ("_", []) => Ok(None),
        ("Write", [x]) => Ok(Some(Effect::Write(variable(x, "Write")?))),
        ("Append", [f]) => Ok(Some(Effect::Append(variable(f, "Append")?))),
        ("Commit", []) => Ok(Some(Effect::Commit)),
        ("Emit", []) => Ok(Some(Effect::Emit)),
        ("Raise", _) => Err(LoweringError::unsupported(
            ty.name_span,
            "`Raise` is not supported yet: exceptions are not implemented",
        )),
        ("Write" | "Append" | "Commit" | "Emit" | "_", _) => Err(arity(item.span, &ty.name)),
        (name, _) => Err(LoweringError::unsupported(
            ty.name_span,
            format!(
                "`{name}` is not an effect; a `causes` clause lists `Write(x)`, `Append(f)`, \
                 `Commit`, `Emit` and `_`, and a variable standing for effects is not \
                 supported yet"
            ),
        )),
    }
}

/// The variable `arg` names, raw: `uniquify` resolves it where the clause is written.
fn variable(arg: &Spanned<ChlExpr>, item: &str) -> Result<Name, LoweringError> {
    match &arg.node {
        ChlExpr::Name(name) => Ok(Name::raw(name.clone())),
        _ => Err(LoweringError::unsupported(
            arg.span,
            format!("`{item}` takes the name of a variable"),
        )),
    }
}

fn arity(span: Span, name: &str) -> LoweringError {
    let expected = match name {
        "_" | "Ext" | "Commit" | "Emit" => "no argument",
        _ => "one variable",
    };
    LoweringError::unsupported(span, format!("`{name}` takes {expected}"))
}
