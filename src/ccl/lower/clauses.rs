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

use super::{LoweringContext, LoweringError};
use crate::ccl::Name;
use crate::ccl::effects::{ClauseParam, Effect, EffectSet, Requirement, Written};
use crate::ccl::infer::solver::traits::Trait;

/// Whether a `requires` item names a context trait or a parameter bounded by `Context`, or
/// is `_`, rather than a trait instance search answers.
pub(super) fn is_context_item(item: &Spanned<ChlRequirement>, ctx: &LoweringContext) -> bool {
    match &item.node {
        ChlRequirement::Trait { ty, .. } => {
            ty.name == "_"
                || ty.instance.is_some()
                || Trait::context_named(&ty.name).is_some()
                || ctx.clause_param(&ty.name, item.span).is_some()
        }
        ChlRequirement::Bound { .. } => false,
    }
}

/// One clause item, lowered.
enum Lowered<T> {
    Item(T),
    Param(ClauseParam),
    /// `_`.
    Hole,
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
    ctx: &LoweringContext,
) -> Result<Option<Written>, LoweringError> {
    let at = match (requires.span, causes.span) {
        (None, None) if site == Site::Def => return Ok(None),
        (None, None) => written_at,
        (Some(r), Some(c)) => r.join(c),
        (Some(at), None) | (None, Some(at)) => at,
    };
    let mut set = EffectSet::default();
    let mut hole_requires = false;
    for item in requires.items.iter().filter(|r| is_context_item(r, ctx)) {
        match context_requirement(item, ctx)? {
            Lowered::Item(r) => {
                set.requires.insert(r);
            }
            Lowered::Param(p) => {
                set.params.insert(p);
            }
            Lowered::Hole => hole_requires = true,
        }
    }
    let mut hole_causes = false;
    for item in &causes.items {
        match effect(item, ctx)? {
            Lowered::Item(e) => {
                set.causes.insert(e);
            }
            Lowered::Param(p) => {
                set.params.insert(p);
            }
            Lowered::Hole => hole_causes = true,
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
        of_instance: false,
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

/// The context requirement or the parameter `item` names.
fn context_requirement(
    item: &Spanned<ChlRequirement>,
    ctx: &LoweringContext,
) -> Result<Lowered<Requirement>, LoweringError> {
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
    if let Some(param) = associated(ty, ctx)? {
        return clause_param(param, false, ty, item.span);
    }
    if let Some(param) = ctx.clause_param(&ty.name, item.span) {
        return clause_param(param, false, ty, item.span);
    }
    match (ty.name.as_str(), ty.args.as_slice()) {
        ("_", []) => Ok(Lowered::Hole),
        ("Ext", []) => Ok(Lowered::Item(Requirement::ext())),
        ("Read", [x]) => Ok(Lowered::Item(Requirement::read(variable(x, "Read")?))),
        ("Transaction", _) => Err(LoweringError::unsupported(
            ty.name_span,
            "`Transaction` is not supported yet: transactions as contextual parameters are \
             not implemented",
        )),
        (name, _) => Err(arity(item.span, name)),
    }
}

/// The effect or the parameter `item` names.
fn effect(
    item: &Spanned<TraitType>,
    ctx: &LoweringContext,
) -> Result<Lowered<Effect>, LoweringError> {
    let ty = &item.node;
    if let Some(param) = associated(ty, ctx)? {
        return clause_param(param, true, ty, item.span);
    }
    if let Some(param) = ctx.clause_param(&ty.name, item.span) {
        return clause_param(param, true, ty, item.span);
    }
    match (ty.name.as_str(), ty.args.as_slice()) {
        ("_", []) => Ok(Lowered::Hole),
        ("Write", [x]) => Ok(Lowered::Item(Effect::Write(variable(x, "Write")?))),
        ("Append", [f]) => Ok(Lowered::Item(Effect::Append(variable(f, "Append")?))),
        ("Commit", []) => Ok(Lowered::Item(Effect::Commit)),
        ("Emit", []) => Ok(Lowered::Item(Effect::Emit)),
        ("Raise", _) => Err(LoweringError::unsupported(
            ty.name_span,
            "`Raise` is not supported yet: exceptions are not implemented",
        )),
        ("Write" | "Append" | "Commit" | "Emit" | "_", _) => Err(arity(item.span, &ty.name)),
        (name, _) => Err(LoweringError::unsupported(
            ty.name_span,
            format!(
                "`{name}` is not an effect; a `causes` clause lists `Write(x)`, `Append(f)`, \
                 `Commit`, `Emit`, `_`, and a type parameter bounded by `Effect`"
            ),
        )),
    }
}

/// The parameter a requirement in scope gives the associated effect type `ty` names, `s::Writes`,
/// or `None` for an item no requirement qualifies.
fn associated(ty: &TraitType, ctx: &LoweringContext) -> Result<Option<ClauseParam>, LoweringError> {
    let Some(instance) = &ty.instance else {
        return Ok(None);
    };
    let Some(requirement) = ctx.named_requirement(&instance.node) else {
        return Err(LoweringError::unsupported(
            instance.span,
            format!(
                "`{}` names no requirement in scope; `{}::{}` is an associated effect type of \
                 the instance a `requires` clause names",
                instance.node, instance.node, ty.name
            ),
        ));
    };
    let found = requirement.effect_assoc.iter().find(|(id, _)| {
        requirement
            .trait_
            .effect_assocs
            .iter()
            .any(|p| p.param.id == *id && p.param.spelling == ty.name)
    });
    match found {
        Some((_, param)) => Ok(Some(param.clone())),
        None => Err(LoweringError::unsupported(
            ty.name_span,
            format!(
                "`{}` declares no associated type `{}` bounded by `Effect` or `Context`",
                requirement.trait_, ty.name
            ),
        )),
    }
}

/// `param` as an item of the clause that `in_causes` says it stands in.
fn clause_param<T>(
    param: ClauseParam,
    in_causes: bool,
    ty: &TraitType,
    span: Span,
) -> Result<Lowered<T>, LoweringError> {
    if !ty.args.is_empty() {
        return Err(LoweringError::unsupported(
            span,
            format!("`{}` is a type parameter and takes no argument", ty.name),
        ));
    }
    if param.of_causes != in_causes {
        let (bound, clause) = if param.of_causes {
            ("Effect", "causes")
        } else {
            ("Context", "requires")
        };
        return Err(LoweringError::unsupported(
            ty.name_span,
            format!(
                "`{}` is bounded by `{bound}`, so it stands in a `{clause}` clause",
                ty.name
            ),
        ));
    }
    Ok(Lowered::Param(param))
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
