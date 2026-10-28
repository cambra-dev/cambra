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

use super::modules::QualifierKind;
use super::{LoweringContext, LoweringError};
use crate::ccl::Name;
use crate::ccl::effects::{
    ClauseParam, Effect, EffectSet, Every, Family, Item, Owner, Requirement, Written, pruned,
};
use crate::ccl::infer::solver::traits::Trait;

/// Whether a `requires` item names a context trait or a parameter bounded by `Context`, or
/// is `_`, rather than a trait instance search answers.
pub(super) fn is_context_item(item: &Spanned<ChlRequirement>, ctx: &LoweringContext) -> bool {
    match &item.node {
        ChlRequirement::Trait { ty, .. } => {
            ty.name == "_"
                || ty.instance.is_some()
                || ty.name == "Context"
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
    /// A top: `Effect` or `Context`, every capability of the clause's direction, or a family's,
    /// `Write(_)`, or a run's, `WriteTxn(inv::_)`.
    Every(Every),
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
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
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
            Lowered::Every(top) => set.add_every(top),
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
            Lowered::Every(top) => set.add_every(top),
        }
    }
    // A top or a clause variable in parentheses takes its own `except` away, from it alone.
    for (item, own) in &requires.scoped {
        let lowered = is_context_item(item, ctx)
            .then(|| context_requirement(item, ctx))
            .transpose()?
            .ok_or_else(|| not_scoped(item.span))?;
        let own = own
            .iter()
            .map(|e| Ok((e.span, requirement_taken(e, ctx)?)))
            .collect::<Result<Vec<_>, LoweringError>>()?;
        scope(&mut set, lowered, own, item.span)?;
    }
    for (item, own) in &causes.scoped {
        let lowered = effect(item, ctx)?;
        let own = own
            .iter()
            .map(|e| Ok((e.span, effect_taken(e, ctx)?)))
            .collect::<Result<Vec<_>, LoweringError>>()?;
        scope(&mut set, lowered, own, item.span)?;
    }
    // `except` takes capabilities out of the clause's variables and its tops, so a clause with
    // neither has nothing for it to take from, and an item no top of a clause without variables
    // holds any of takes nothing.
    let mut except = std::collections::BTreeSet::new();
    let has_params =
        |of_causes: bool, set: &EffectSet| set.params.iter().any(|p| p.of_causes == of_causes);
    let takes_from = |of_causes: bool, set: &EffectSet| {
        has_params(of_causes, set) || set.tops_of(of_causes).next().is_some()
    };
    if let Some(first) = requires.except.first() {
        if !takes_from(false, &set) {
            return Err(nothing_to_take(first.span));
        }
        for item in &requires.except {
            let taken = requirement_taken(item, ctx)?;
            if !has_params(false, &set) && !set.tops_of(false).any(|t| t.overlaps(&taken)) {
                return Err(takes_nothing(item.span, &taken));
            }
            except.insert(taken);
        }
    }
    if let Some(first) = causes.except.first() {
        if !takes_from(true, &set) {
            return Err(nothing_to_take(first.span));
        }
        for item in &causes.except {
            let taken = effect_taken(item, ctx)?;
            if !has_params(true, &set) && !set.tops_of(true).any(|t| t.overlaps(&taken)) {
                return Err(takes_nothing(item.span, &taken));
            }
            except.insert(taken);
        }
    }
    let tops = std::mem::take(&mut set.tops);
    for t in tops {
        let taken = except
            .iter()
            .filter(|i| i.of_causes() == t.of_causes)
            .cloned();
        set.add_every(t.less(taken));
    }
    set.params = std::mem::take(&mut set.params)
        .into_iter()
        .map(|p| {
            let taken = except.iter().filter(|i| i.of_causes() == p.of_causes);
            ClauseParam {
                except: pruned(p.except.iter().chain(taken).cloned()),
                ..p
            }
        })
        .collect();
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

/// What a clause variable's bound takes away, `except RunTransaction` in
/// `E <: Effect except RunTransaction`: capabilities of the bound's direction
/// (`docs/chl-spec.md`, "Kinds and bounds").
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub(super) fn bound_except(
    items: &[Spanned<TraitType>],
    of_causes: bool,
    ctx: &mut LoweringContext,
) -> Result<std::collections::BTreeSet<Item>, LoweringError> {
    let mut out = std::collections::BTreeSet::new();
    for item in items {
        let taken = if of_causes {
            effect_taken(item, ctx)?
        } else {
            let requirement = Spanned::new(
                item.span,
                ChlRequirement::Trait {
                    binder: None,
                    ty: item.node.clone(),
                },
            );
            requirement_taken(&requirement, ctx)?
        };
        out.insert(taken);
    }
    Ok(out)
}

/// What one `except` item of a `requires` clause takes away: a requirement, or `Read(_)`.
fn requirement_taken(
    item: &Spanned<ChlRequirement>,
    ctx: &LoweringContext,
) -> Result<Item, LoweringError> {
    if !is_context_item(item, ctx) {
        return Err(not_taken(item.span));
    }
    match context_requirement(item, ctx)? {
        Lowered::Item(r) => Ok(Item::Requires(r)),
        Lowered::Every(top) if top.family.is_some() => Ok(Item::Every(top)),
        _ => Err(not_taken(item.span)),
    }
}

/// What one `except` item of a `causes` clause takes away: an effect, or a family's top.
fn effect_taken(item: &Spanned<TraitType>, ctx: &LoweringContext) -> Result<Item, LoweringError> {
    match effect(item, ctx)? {
        Lowered::Item(e) => Ok(Item::Causes(e)),
        Lowered::Every(top) if top.family.is_some() => Ok(Item::Every(top)),
        _ => Err(not_taken(item.span)),
    }
}

/// `taken`, which a top's own `except` takes from `top`, written at `span`, if `top` holds any
/// of it.
fn taken_from(top: &Every, span: Span, taken: Item) -> Result<Item, LoweringError> {
    if top.overlaps(&taken) {
        Ok(taken)
    } else {
        Err(takes_nothing(span, &taken))
    }
}

/// Hold `lowered`, a parenthesized item of the clause `of_causes` gives, written at `span`, less
/// `own`, its own `except`: a top, which must hold some of each, or a clause variable.
fn scope(
    set: &mut EffectSet,
    lowered: Lowered<impl Sized>,
    own: Vec<(Span, Item)>,
    span: Span,
) -> Result<(), LoweringError> {
    match lowered {
        Lowered::Every(scoped) => {
            let own = own
                .into_iter()
                .map(|(at, taken)| taken_from(&scoped, at, taken))
                .collect::<Result<Vec<_>, _>>()?;
            set.add_every(scoped.less(own));
        }
        Lowered::Param(p) => {
            set.params.insert(ClauseParam {
                except: pruned(
                    p.except
                        .iter()
                        .cloned()
                        .chain(own.into_iter().map(|(_, i)| i)),
                ),
                ..p
            });
        }
        Lowered::Item(_) | Lowered::Hole => return Err(not_scoped(span)),
    }
    Ok(())
}

/// A parenthesized clause item that is neither a top nor a clause variable.
fn not_scoped(span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        "parentheses give a top or a clause variable an `except` of its own, as \
         `(Write(_) except Write(x))` does",
    )
}

/// An `except` in a clause holding neither a clause variable nor a top.
fn nothing_to_take(span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        "`except` takes capabilities out of a clause's variables and its tops, such as `Effect` or \
         `Write(_)`, and this clause holds none of them",
    )
}

/// An `except` item that is not one capability or a family's top.
fn not_taken(span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        "`except` takes capabilities away, such as `RunTransaction` or `Write(_)`, not a clause \
         variable, `Effect`, `Context` or `_`",
    )
}

/// An `except` item no top of its clause holds any of, in a clause without variables.
fn takes_nothing(span: Span, taken: &Item) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!("`except {taken}` takes nothing away: no top of this clause holds any of it"),
    )
}

/// The run `arg`, `inv::_`, holds the state of, or `None` for an argument that names none:
/// a run, a Module-typed parameter or a member bound to a module, by how this module spells
/// it, or `Module::_` in a Module type's entry, the module the type describes.
fn owner(arg: &Spanned<ChlExpr>, ctx: &LoweringContext) -> Result<Option<Owner>, LoweringError> {
    let ChlExpr::Qualified(q) = &arg.node else {
        return Ok(None);
    };
    if q.name.node != "_" {
        return Ok(None);
    }
    if let [module] = q.qualifier.as_slice()
        && module.node == "Module"
    {
        return if ctx.in_module_type > 0 {
            Ok(Some(Owner::Module))
        } else {
            Err(LoweringError::unsupported(
                arg.span,
                "`Module::_` is the state of the module a Module type describes, so it stands in \
                 an entry of a `Module{…}` type",
            ))
        };
    }
    let [run] = q.qualifier.as_slice() else {
        return Err(LoweringError::unsupported(
            arg.span,
            "a run's state is written through the name of the run or of a Module-typed \
             parameter, `inv::_`; reaching a run through a member bound to a module is not \
             supported yet",
        ));
    };
    let qualifier = ctx.qualifier_path(&q.qualifier, arg.span)?;
    if !matches!(
        qualifier.kind,
        QualifierKind::Run | QualifierKind::Parameter
    ) {
        return Err(LoweringError::unsupported(
            arg.span,
            format!(
                "`{}::_` is the state of a run, so `{}` names a run or a Module-typed parameter",
                run.node, run.node
            ),
        ));
    }
    Ok(Some(Owner::Qualifier(run.node.clone())))
}

/// Whether `arg` is `_`, which makes `Write(_)` a family's top.
fn is_hole(arg: &Spanned<ChlExpr>) -> bool {
    matches!(&arg.node, ChlExpr::Name(n) if n == "_")
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
        ("Context", []) => Ok(Lowered::Every(Every::of_direction(false))),
        ("Read", [x]) if is_hole(x) => Ok(Lowered::Every(Family::Read.top())),
        ("ReadTxn", [x]) if is_hole(x) => Ok(Lowered::Every(Family::ReadTxn.top())),
        ("ReadTxn", [x]) if let Some(owner) = owner(x, ctx)? => {
            Ok(Lowered::Every(Family::ReadTxn.owned_top(owner)))
        }
        ("ObserveWorld", []) => Ok(Lowered::Item(Requirement::observe_world())),
        ("Read", [x]) => Ok(Lowered::Item(Requirement::read(variable(x, "Read", ctx)?))),
        ("ReadTxn", [x]) => Ok(Lowered::Item(Requirement::read_txn(variable(
            x, "ReadTxn", ctx,
        )?))),
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
        ("Effect", []) => Ok(Lowered::Every(Every::of_direction(true))),
        ("Write", [x]) if is_hole(x) => Ok(Lowered::Every(Family::Write.top())),
        ("WriteTxn", [x]) if is_hole(x) => Ok(Lowered::Every(Family::WriteTxn.top())),
        ("WriteTxn", [x]) if let Some(owner) = owner(x, ctx)? => {
            Ok(Lowered::Every(Family::WriteTxn.owned_top(owner)))
        }
        ("Append", [f]) if is_hole(f) => Ok(Lowered::Every(Family::Append.top())),
        ("Write", [x]) => Ok(Lowered::Item(Effect::Write(variable(x, "Write", ctx)?))),
        ("WriteTxn", [x]) => Ok(Lowered::Item(Effect::WriteTxn(variable(
            x, "WriteTxn", ctx,
        )?))),
        ("Append", [f]) => Ok(Lowered::Item(Effect::Append(variable(f, "Append", ctx)?))),
        ("RunTransaction", []) => Ok(Lowered::Item(Effect::RunTransaction)),
        ("AffectWorld", []) => Ok(Lowered::Item(Effect::AffectWorld)),
        ("Raise", _) => Err(LoweringError::unsupported(
            ty.name_span,
            "`Raise` is not supported yet: exceptions are not implemented",
        )),
        (
            "Write" | "WriteTxn" | "Append" | "RunTransaction" | "AffectWorld" | "Effect" | "_",
            _,
        ) => Err(arity(item.span, &ty.name)),
        (name, _) => Err(LoweringError::unsupported(
            ty.name_span,
            format!(
                "`{name}` is not an effect; a `causes` clause lists `Write(x)`, `WriteTxn(x)`, \
                 `Append(f)`, `RunTransaction`, `AffectWorld`, the tops `Effect`, `Write(_)`, \
                 `WriteTxn(_)` and `Append(_)`, `_`, and a type parameter bounded by `Effect`"
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

/// The variable `arg` names, raw: `uniquify` resolves it where the clause is written. Another
/// module's member, `inv::count`, is named as a reference to it is.
fn variable(
    arg: &Spanned<ChlExpr>,
    item: &str,
    ctx: &LoweringContext,
) -> Result<Name, LoweringError> {
    match &arg.node {
        ChlExpr::Name(name) => Ok(Name::raw(name.clone())),
        ChlExpr::Qualified(q) => Ok(match ctx.member(q, arg.span)? {
            Some(member) => member.name.raw(),
            None => Name::raw(q.name.node.clone()),
        }),
        _ => Err(LoweringError::unsupported(
            arg.span,
            format!("`{item}` takes the name of a variable"),
        )),
    }
}

fn arity(span: Span, name: &str) -> LoweringError {
    let expected = match name {
        "_" | "ObserveWorld" | "RunTransaction" | "AffectWorld" | "Effect" | "Context" => {
            "no argument"
        }
        _ => "one variable",
    };
    LoweringError::unsupported(span, format!("`{name}` takes {expected}"))
}
