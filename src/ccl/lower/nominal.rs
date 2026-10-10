//! Lowering `type` declarations and the names their constructors bind
//! (`docs/chl-spec.md`, "6.8 Nominal types and methods \[Decided\]").
//!
//! A module's declarations lower in two steps around its type aliases, since an alias
//! may name a nominal type and a constructor's parameter type may name an alias.
//! [`declare_nominal_types`] gives each declaration a [`NominalDecl`] head, and
//! [`define_nominal_types`] lowers the constructors once the aliases are declared.
//!
//! A constructor that declares parameters is a function, bound around the whole module
//! as `Shape::rect` by [`bind_constructors`]. Its parameter carries the declared type as
//! an annotation, so a call discharges the type's refinements as any annotated
//! parameter's are discharged, and a parameterised type's constructor is polymorphic
//! through the `Poly` annotation a `def` with type parameters carries. A constructor
//! that declares none is a value, built where it is named.

use std::collections::HashSet;
use std::rc::Rc;

use smol_str::SmolStr;

use super::stmts::{is_builtin_type_name, lower_type_expr};
use super::{LoweringContext, LoweringError};
use crate::ccl::nominal::{NominalCtor, NominalDecl};
use crate::ccl::ty::{PolyParam, PolyType, TypeKind, TypeParam};
use crate::ccl::{Expr, Lit, Pattern, Type, TypedBinding, TypedExprNode};
use crate::chl_parser::ast::{
    AnnotationMode, ArmPattern, ConstructorPattern, Expr as ChlExpr, ImplBlock, MatchArm, Param,
    QualifiedName, Requirement, Span, Spanned, Stmt as ChlStmt, TypeAnnotation, TypeDecl,
    TypeDeclBody, TypeParam as ChlTypeParam,
};

/// The name the constructor function of `ctor` is bound to.
fn constructor_binding(decl: &NominalDecl, ctor: &str) -> String {
    format!("{}::{ctor}", decl.name)
}

fn type_decls(stmts: &[Spanned<ChlStmt>]) -> impl Iterator<Item = (&TypeDecl, Span)> {
    stmts.iter().filter_map(|s| match &s.node {
        ChlStmt::TypeDecl(decl) => Some((decl, s.span)),
        _ => None,
    })
}

/// Declare the head of each `type` among the module's top-level `stmts`.
pub(super) fn declare_nominal_types(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for (decl, _) in type_decls(stmts) {
        let name = &decl.name;
        if is_builtin_type_name(&name.node) {
            errors.push(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is a built-in type and cannot be given another meaning",
                    name.node
                ),
            ));
            continue;
        }
        if ctx.nominal_type(&name.node).is_some() {
            errors.push(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is declared twice in this module; a `type` binds its name once",
                    name.node
                ),
            ));
            continue;
        }
        let mut params: Vec<Rc<TypeParam>> = Vec::new();
        for param in &decl.params {
            if is_builtin_type_name(&param.node) {
                errors.push(LoweringError::unsupported(
                    param.span,
                    format!(
                        "`{}` is a built-in type and cannot name a type parameter",
                        param.node
                    ),
                ));
            } else if params.iter().any(|p| p.spelling == param.node) {
                errors.push(LoweringError::unsupported(
                    param.span,
                    format!("type parameter `{}` is declared twice", param.node),
                ));
            } else {
                params.push(TypeParam::declared(param.node.clone()));
            }
        }
        ctx.nominal_types.push(NominalDecl::declared(
            name.node.clone(),
            params,
            name.span,
            matches!(decl.body, TypeDeclBody::Single(_)),
        ));
    }
    errors
}

/// Lower the constructors of each `type` among the module's top-level `stmts`, whose
/// heads [`declare_nominal_types`] declared, and define every declaration.
///
/// A declaration is defined only after every declaration its constructors name, so
/// [`NominalDecl::define`] can read their variances. One that reaches itself is refused
/// before any declaration is defined, which keeps the `Rc` graph acyclic.
pub(super) fn define_nominal_types(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    let mut lowered: Vec<(Rc<NominalDecl>, Vec<NominalCtor>)> = Vec::new();
    for (decl, _) in type_decls(stmts) {
        let Some(head) = ctx.nominal_type(&decl.name.node) else {
            continue;
        };
        if lowered.iter().any(|(d, _)| *d == head) {
            continue;
        }
        match lower_constructors(decl, &head, ctx) {
            Ok(ctors) => lowered.push((head, ctors)),
            Err(e) => errors.push(e),
        }
    }
    if !errors.is_empty() {
        return errors;
    }
    let edges: Vec<Vec<usize>> = lowered
        .iter()
        .map(|(_, ctors)| {
            NominalDecl::references(ctors)
                .iter()
                .filter_map(|r| lowered.iter().position(|(d, _)| d == r))
                .collect()
        })
        .collect();
    if let Some(cycle) = find_cycle(&edges) {
        let names: Vec<&str> = cycle.iter().map(|&i| lowered[i].0.name.as_str()).collect();
        let first = &lowered[cycle[0]].0;
        return vec![LoweringError::unsupported(
            first.span,
            format!(
                "`{}` reaches itself through its constructors' parameter types ({}); a \
                 recursive nominal type is not supported yet",
                first.name,
                names
                    .iter()
                    .chain(std::iter::once(&names[0]))
                    .copied()
                    .collect::<Vec<_>>()
                    .join(" → ")
            ),
        )];
    }
    let mut defined = vec![false; lowered.len()];
    let mut slots: Vec<Option<Vec<NominalCtor>>> = lowered
        .iter_mut()
        .map(|(_, c)| Some(std::mem::take(c)))
        .collect();
    for i in 0..lowered.len() {
        define_after_references(i, &lowered, &edges, &mut slots, &mut defined, &mut errors);
    }
    errors
}

/// Define declaration `i` after every declaration it references.
fn define_after_references(
    i: usize,
    lowered: &[(Rc<NominalDecl>, Vec<NominalCtor>)],
    edges: &[Vec<usize>],
    slots: &mut [Option<Vec<NominalCtor>>],
    defined: &mut [bool],
    errors: &mut Vec<LoweringError>,
) {
    if defined[i] {
        return;
    }
    defined[i] = true;
    for &j in &edges[i] {
        define_after_references(j, lowered, edges, slots, defined, errors);
    }
    let decl = &lowered[i].0;
    let ctors = slots[i].take().expect("each declaration is defined once");
    if let Err(unused) = decl.define(ctors) {
        errors.push(LoweringError::unsupported(
            decl.span,
            format!(
                "type parameter `{}` of `{}` appears in no constructor's parameter type",
                unused.spelling, decl.name
            ),
        ));
    }
}

/// A cycle in the directed graph `edges`, as the nodes along it in order.
fn find_cycle(edges: &[Vec<usize>]) -> Option<Vec<usize>> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Unvisited,
        OnPath,
        Done,
    }
    fn visit(
        i: usize,
        edges: &[Vec<usize>],
        marks: &mut [Mark],
        path: &mut Vec<usize>,
    ) -> Option<Vec<usize>> {
        marks[i] = Mark::OnPath;
        path.push(i);
        for &j in &edges[i] {
            match marks[j] {
                Mark::OnPath => {
                    let start = path.iter().position(|&k| k == j).expect("on the path");
                    return Some(path[start..].to_vec());
                }
                Mark::Unvisited => {
                    if let Some(cycle) = visit(j, edges, marks, path) {
                        return Some(cycle);
                    }
                }
                Mark::Done => {}
            }
        }
        path.pop();
        marks[i] = Mark::Done;
        None
    }
    let mut marks = vec![Mark::Unvisited; edges.len()];
    (0..edges.len()).find_map(|i| {
        (marks[i] == Mark::Unvisited)
            .then(|| visit(i, edges, &mut marks, &mut Vec::new()))
            .flatten()
    })
}

/// Lower `decl`'s constructors, with its type parameters in scope.
fn lower_constructors(
    decl: &TypeDecl,
    head: &Rc<NominalDecl>,
    ctx: &mut LoweringContext,
) -> Result<Vec<NominalCtor>, LoweringError> {
    let aliases = ctx.snapshot_type_aliases();
    let scoped = ctx.type_params_in_scope.len();
    for param in &head.params {
        ctx.declare_type_alias(param.spelling.as_str(), Type::Param(Rc::clone(param)));
        ctx.type_params_in_scope.push(param.spelling.to_string());
    }
    let result = (|| {
        let mut ctors: Vec<NominalCtor> = Vec::new();
        match &decl.body {
            TypeDeclBody::Single(ty) => ctors.push(NominalCtor {
                name: SmolStr::new_static("new"),
                span: decl.name.span,
                params: vec![(None, lower_parameter_type(ty, ctx)?)],
            }),
            TypeDeclBody::Constructors(lines) => {
                let mut seen: HashSet<&str> = HashSet::new();
                for line in lines {
                    if !seen.insert(line.name.node.as_str()) {
                        return Err(LoweringError::unsupported(
                            line.name.span,
                            format!(
                                "`{}` declares the constructor `{}` twice",
                                decl.name.node, line.name.node
                            ),
                        ));
                    }
                    let params = line
                        .params
                        .iter()
                        .map(|p| {
                            let name = p.name.as_ref().map(|n| n.node.clone());
                            Ok((name, lower_parameter_type(&p.ty, ctx)?))
                        })
                        .collect::<Result<Vec<_>, LoweringError>>()?;
                    ctors.push(NominalCtor {
                        name: line.name.node.clone(),
                        span: line.name.span,
                        params,
                    });
                }
            }
        }
        Ok(ctors)
    })();
    ctx.type_params_in_scope.truncate(scoped);
    ctx.restore_type_aliases(aliases);
    result
}

/// Lower a constructor's parameter type, which is written in full: nothing infers a
/// declaration's types.
fn lower_parameter_type(
    ty: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let lowered = lower_type_expr(ty, ctx)?;
    fn has_hole(ty: &Type) -> bool {
        let mut found = matches!(ty, Type::Hole | Type::BoundedHole(_));
        ty.walk_children(|c| found |= has_hole(c));
        found
    }
    if has_hole(&lowered) {
        return Err(LoweringError::unsupported(
            ty.span,
            "a constructor's parameter type is written in full; `_` leaves part of it to \
             inference, which no declaration has",
        ));
    }
    // The constructor functions are bound around the whole module (`bind_constructors`),
    // where no module binding is in scope.
    if let Some(name) = crate::ccl::subst::type_free_vars(&lowered).first() {
        return Err(LoweringError::unsupported(
            ty.span,
            format!(
                "a refinement in a constructor's parameter type names `{}`; naming a module \
                 binding there is not supported yet",
                name.base()
            ),
        ));
    }
    Ok(lowered)
}

/// Wrap `body` in the binding of each function the module's declarations declare: each
/// constructor that declares parameters, and the `extract` of a single-constructor form.
pub(super) fn bind_constructors(body: Expr, ctx: &mut LoweringContext) -> Expr {
    let decls = ctx.nominal_types.clone();
    let mut acc = body;
    for decl in decls.iter().rev() {
        if decl.declares_extract {
            acc = bind_extract(decl, acc, ctx);
        }
        for ctor in decl.body().ctors.iter().rev() {
            if ctor.params.is_empty() {
                continue;
            }
            let label = "lower.nominal_ctor";
            let arg = "__ctor_arg";
            let payload = ctx.tag_machinery(Expr::var(arg), ctor.span, label);
            let value = ctx.tag_machinery(
                Expr::nominal_ctor(Rc::clone(decl), ctor.name.as_str(), payload),
                ctor.span,
                label,
            );
            let name = constructor_binding(decl, &ctor.name);
            acc = bind_function(
                decl,
                name,
                arg,
                ctor.payload(),
                value,
                acc,
                ctor.span,
                label,
                ctx,
            );
        }
    }
    acc
}

/// `N::extract`, the function `λ n → match n: case N::new(r): r` that the
/// single-constructor form declares (`docs/chl-spec.md`, "The single-constructor form").
fn bind_extract(decl: &Rc<NominalDecl>, acc: Expr, ctx: &mut LoweringContext) -> Expr {
    let label = "lower.nominal_extract";
    let span = decl.span;
    let arg = "__extract_arg";
    let payload = ctx.fresh_ignored_payload();
    let scrutinee = ctx.tag_machinery(Expr::var(arg), span, label);
    let read = ctx.tag_machinery(Expr::var(payload.as_str()), span, label);
    let guard = ctx.tag_machinery(Expr::lit(Lit::Bool(true)), span, label);
    let case = Expr::match_expr(
        scrutinee,
        vec![crate::ccl::Branch {
            pattern: Some(Pattern {
                tag: "new".to_string(),
                binding: TypedBinding::new_unannotated(payload),
                empty_payload: false,
                nominal: Some(Rc::clone(decl)),
            }),
            guard,
            body: read,
        }],
    );
    let case = ctx.tag_machinery(case, span, label);
    let name = constructor_binding(decl, "extract");
    let self_ty = decl.applied_to_params();
    bind_function(decl, name, arg, self_ty, case, acc, span, label, ctx)
}

/// `let name = λ arg : param_ty → value in acc`, polymorphic over the declaration's type
/// parameters when it has any, as a `def` with type parameters is.
#[allow(clippy::too_many_arguments)]
fn bind_function(
    decl: &NominalDecl,
    name: String,
    arg: &str,
    param_ty: Type,
    value: Expr,
    acc: Expr,
    span: Span,
    label: crate::ccl::provenance::RewriteLabel,
    ctx: &mut LoweringContext,
) -> Expr {
    let mut function = Expr::lambda(arg, Type::Hole, value);
    if let TypedExprNode::Lambda { param, .. } = &mut function.node {
        param.declare(param_ty);
    }
    let function = ctx.tag_machinery(function, span, label);
    let binding = if decl.params.is_empty() {
        Expr::let_bind(name, function, acc)
    } else {
        let poly = Type::Poly(Rc::new(PolyType {
            params: decl
                .params
                .iter()
                .map(|p| PolyParam {
                    param: Rc::clone(p),
                    kind: TypeKind::Type,
                    bound_at: None,
                })
                .collect(),
            requires: Vec::new(),
            body: Type::Hole,
        }));
        Expr::let_bind_annotated(name, function, acc, poly)
    };
    ctx.tag_machinery(binding, span, label)
}

/// The declaration whose constructor `q` names, `Shape::circle`.
fn resolve_constructor(
    q: &QualifiedName,
    span: Span,
    ctx: &LoweringContext,
) -> Result<Rc<NominalDecl>, LoweringError> {
    let [ty] = q.qualifier.as_slice() else {
        unreachable!("`refuse_module_syntax` lets through only a name qualified by one type")
    };
    let Some(decl) = ctx.nominal_types.iter().find(|d| d.name == ty.node) else {
        return Err(LoweringError::unsupported(
            ty.span,
            format!(
                "`{}` is not a nominal type this module declares, so `{}::{}` names nothing",
                ty.node, ty.node, q.name.node
            ),
        ));
    };
    match decl.ctor(&q.name.node) {
        Some(_) => Ok(Rc::clone(decl)),
        None if is_extract(decl, &q.name.node) => Ok(Rc::clone(decl)),
        None if associated_arity(ctx, decl, &q.name.node).is_some() => Ok(Rc::clone(decl)),
        None => Err(LoweringError::unsupported(
            span,
            format!(
                "`{}` declares no constructor or function `{}`",
                decl.name, q.name.node
            ),
        )),
    }
}

/// The number of value parameters of `decl`'s associated function `name`, if it declares
/// one.
fn associated_arity(ctx: &LoweringContext, decl: &Rc<NominalDecl>, name: &str) -> Option<usize> {
    ctx.associated_functions
        .iter()
        .find(|f| f.decl == *decl && f.name == name)
        .map(|f| f.arity)
}

/// Whether `name` is the `extract` a declaration declares.
fn is_extract(decl: &NominalDecl, name: &str) -> bool {
    decl.declares_extract && name == "extract"
}

/// Lower a name qualified by a type, `Shape::circle`: the constructor function, the
/// value a constructor without parameters builds, or `extract`.
pub(super) fn lower_member(
    q: &QualifiedName,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let decl = resolve_constructor(q, span, ctx)?;
    if is_extract(&decl, &q.name.node) || associated_arity(ctx, &decl, &q.name.node).is_some() {
        return Ok(Expr::var(constructor_binding(&decl, &q.name.node)));
    }
    let ctor = decl.ctor(&q.name.node).expect("resolved above");
    if !ctor.params.is_empty() {
        return Ok(Expr::var(constructor_binding(&decl, &ctor.name)));
    }
    let name = ctor.name.clone();
    let unit = ctx.tag_machinery(Expr::lit(Lit::Unit), span, "lower.nominal_ctor_unit");
    Ok(Expr::nominal_ctor(Rc::clone(&decl), name.as_str(), unit))
}

/// Lower a call of a name qualified by a type, `Shape::circle(1)`.
pub(super) fn lower_member_call(
    q: &QualifiedName,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let decl = resolve_constructor(q, span, ctx)?;
    let arity = match decl.ctor(&q.name.node) {
        Some(ctor) => ctor.params.len(),
        None => associated_arity(ctx, &decl, &q.name.node).unwrap_or(1),
    };
    let ctor_name = q.name.node.clone();
    if arity == 0 {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{0}::{1}` declares no parameters, so it is a value and not a function: \
                 write `{0}::{1}`",
                decl.name, ctor_name
            ),
        ));
    }
    if args.len() != arity {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{}` takes {} argument{}, got {}",
                decl.name,
                ctor_name,
                arity,
                if arity == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    let name = constructor_binding(&decl, &ctor_name);
    super::exprs::apply_named(&name, span, args, ctx)
}

/// Refuse a `type` declared anywhere but a module's top level.
pub(super) fn refuse_nested(span: Span, decl: &TypeDecl) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!(
            "`type {}` is declared inside a block; a `type` is declared at a module's top \
             level",
            decl.name.node
        ),
    )
}

/// The nominal type a `match`'s constructor arms name, once each arm is checked against
/// it: every arm names a constructor of that one type and binds one name per declared
/// parameter, and without a `case _:` every constructor has an arm
/// (`docs/chl-spec.md`, "4.10 `match` — tag dispatch").
pub(super) fn constructor_arms_type(
    match_span: Span,
    arms: &[MatchArm],
    has_default: bool,
    ctx: &LoweringContext,
) -> Result<Rc<NominalDecl>, LoweringError> {
    let mut found: Option<Rc<NominalDecl>> = None;
    for arm in arms {
        let Some(ArmPattern::Constructor(pattern)) = &arm.pattern else {
            continue;
        };
        let decl = resolve_pattern_type(pattern, ctx)?;
        match &found {
            Some(first) if *first != decl => {
                return Err(LoweringError::unsupported(
                    pattern.type_path[0].span.join(pattern.ctor.span),
                    format!(
                        "`match` names constructors of `{}` and of `{}`; the arms of one `match` \
                         name constructors of one type",
                        first.name, decl.name
                    ),
                ));
            }
            Some(_) => {}
            None => found = Some(Rc::clone(&decl)),
        }
        check_binders(&decl, pattern)?;
    }
    let decl = found.expect("`constructor_arms_type` is called with a constructor arm");
    if !has_default {
        let named: HashSet<&str> = arms
            .iter()
            .filter_map(|a| match &a.pattern {
                Some(ArmPattern::Constructor(p)) => Some(p.ctor.node.as_str()),
                _ => None,
            })
            .collect();
        let missing: Vec<String> = decl
            .body()
            .ctors
            .iter()
            .filter(|c| !named.contains(c.name.as_str()))
            .map(|c| format!("`{}::{}`", decl.name, c.name))
            .collect();
        if !missing.is_empty() {
            return Err(LoweringError::unsupported(
                match_span,
                format!(
                    "`match` over `{}` has no arm for {}; each constructor is handled by an \
                     arm, or `case _:` covers the rest",
                    decl.name,
                    missing.join(", ")
                ),
            ));
        }
    }
    Ok(decl)
}

/// The declaration a constructor pattern's type path names, with the constructor it
/// names checked to exist.
fn resolve_pattern_type(
    pattern: &ConstructorPattern,
    ctx: &LoweringContext,
) -> Result<Rc<NominalDecl>, LoweringError> {
    let [ty] = pattern.type_path.as_slice() else {
        unreachable!("`refuse_module_syntax` refuses a constructor pattern qualified by a module")
    };
    let Some(decl) = ctx.nominal_type(&ty.node) else {
        return Err(LoweringError::unsupported(
            ty.span,
            format!("`{}` is not a nominal type this module declares", ty.node),
        ));
    };
    if decl.ctor(&pattern.ctor.node).is_none() {
        return Err(LoweringError::unsupported(
            ty.span.join(pattern.ctor.span),
            format!(
                "`{}` declares no constructor `{}`",
                decl.name, pattern.ctor.node
            ),
        ));
    }
    Ok(decl)
}

/// A constructor pattern binds one name or `_` per declared parameter, and takes no
/// parentheses for a constructor that declares none.
fn check_binders(decl: &NominalDecl, pattern: &ConstructorPattern) -> Result<(), LoweringError> {
    let ctor = decl
        .ctor(&pattern.ctor.node)
        .expect("resolved by `resolve_pattern_type`");
    let span = pattern.type_path[0].span.join(pattern.ctor.span);
    match (&pattern.binders, ctor.params.len()) {
        (None, 0) => Ok(()),
        (Some(_), 0) => Err(LoweringError::unsupported(
            span,
            format!(
                "`{0}::{1}` declares no parameters, so its pattern takes no parentheses: \
                 `{0}::{1}`",
                decl.name, ctor.name
            ),
        )),
        (Some(binders), n) if binders.len() == n => Ok(()),
        (binders, n) => Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{}` declares {n} parameter{}, so its pattern binds {n}; this one binds {}",
                decl.name,
                ctor.name,
                if n == 1 { "" } else { "s" },
                binders.as_ref().map_or(0, Vec::len)
            ),
        )),
    }
}

/// The [`Pattern`] a checked constructor pattern lowers to, and the parameters to bind
/// from its payload by position.
///
/// The pattern binds the constructor's payload ([`NominalCtor::payload`]). For one
/// parameter that is the parameter, so the pattern binds it under the user's name. For
/// several it is their tuple, which the pattern binds under a minted name, and each named
/// parameter is projected out of it ([`bind_parameters`]).
pub(super) fn constructor_arm_pattern(
    decl: &Rc<NominalDecl>,
    pattern: &ConstructorPattern,
    ctx: &mut LoweringContext,
) -> (Pattern, Vec<(String, usize)>) {
    let binders = pattern.binders.as_deref().unwrap_or(&[]);
    let (payload, binds) = match binders {
        [] => (ctx.fresh_ignored_payload(), Vec::new()),
        [only] => match &only.node {
            Some(name) => (name.to_string(), Vec::new()),
            None => (ctx.fresh_ignored_payload(), Vec::new()),
        },
        many => {
            let binds = many
                .iter()
                .enumerate()
                .filter_map(|(i, b)| b.node.as_ref().map(|n| (n.to_string(), i)))
                .collect();
            (ctx.fresh_ignored_payload(), binds)
        }
    };
    let pattern = Pattern {
        tag: pattern.ctor.node.to_string(),
        binding: TypedBinding::new_unannotated(payload),
        empty_payload: binders.is_empty(),
        nominal: Some(Rc::clone(decl)),
    };
    (pattern, binds)
}

/// `body` with each of `binds` replaced by its position of the tuple `payload` names.
///
/// Substituted rather than bound, as a multi-parameter function's parameters are
/// (`functions::uncurry_params`): an arm whose body is a bare feed keeps that shape, which
/// the feed fan-out over a loop's `match` reads (`channelize`'s
/// `try_extract_fanout_feed`). The payload's name is minted, so no binder in `body` can
/// capture it.
pub(super) fn bind_parameters(
    payload: &crate::ccl::Name,
    binds: Vec<(String, usize)>,
    body: Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let label = "lower.constructor_pattern";
    binds.into_iter().fold(body, |acc, (name, i)| {
        let read = ctx.tag_machinery(Expr::var(payload.clone()), span, label);
        let proj = ctx.tag_machinery(Expr::proj_index(i), span, label);
        let field = ctx.tag_machinery(Expr::apply(read, proj), span, label);
        super::functions::substitute_param_in_body(
            acc,
            &crate::ccl::Name::raw(name.as_str()),
            &field,
            label,
        )
    })
}

/// `pattern = value` followed by `body`: a `Case` over `value` with the pattern's one arm.
///
/// A constructor pattern can fail to match, so an assignment takes apart only a type that
/// declares one constructor, where the match is exhaustive (`docs/chl-spec.md`, "4.3.1
/// Destructuring patterns").
pub(super) fn lower_constructor_assignment(
    pattern: &ConstructorPattern,
    value: Expr,
    body: Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let checked = check_constructor_assignment(pattern, span, ctx)?;
    Ok(checked.wrap(value, body, span, ctx))
}

/// A constructor pattern checked for an assignment, ready to take a value apart.
pub(super) struct ConstructorAssignment {
    pattern: Pattern,
    binds: Vec<(String, usize)>,
}

impl ConstructorAssignment {
    /// The names the assignment binds.
    pub(super) fn names(&self) -> Vec<String> {
        let mut out: Vec<String> = self.binds.iter().map(|(n, _)| n.clone()).collect();
        if self.binds.is_empty() {
            out.push(self.pattern.binding.name.base().to_string());
        }
        out
    }

    /// `body` with the assignment's names bound from `value`.
    pub(super) fn wrap(
        self,
        value: Expr,
        body: Expr,
        span: Span,
        ctx: &mut LoweringContext,
    ) -> Expr {
        let body = bind_parameters(&self.pattern.binding.name, self.binds, body, span, ctx);
        let guard = ctx.tag_machinery(Expr::lit(Lit::Bool(true)), span, "lower.match_guard");
        ctx.tag_image(
            Expr::match_expr(
                value,
                vec![crate::ccl::Branch {
                    pattern: Some(self.pattern),
                    guard,
                    body,
                }],
            ),
            span,
        )
    }
}

/// Check that `pattern` can stand on the left of `=`: its type declares one constructor.
pub(super) fn check_constructor_assignment(
    pattern: &ConstructorPattern,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<ConstructorAssignment, LoweringError> {
    let decl = resolve_pattern_type(pattern, ctx)?;
    check_binders(&decl, pattern)?;
    let ctors = decl.body().ctors.len();
    if ctors != 1 {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}` declares {ctors} constructors, so a pattern naming one of them can fail \
                 to match; take it apart with `match`",
                decl.name
            ),
        ));
    }
    let (pattern, binds) = constructor_arm_pattern(&decl, pattern, ctx);
    Ok(ConstructorAssignment { pattern, binds })
}

/// An associated function a module declares: `def N::f`, or a `def` in `impl N:`
/// (`docs/chl-spec.md`, "Associated functions and methods").
#[derive(Clone)]
pub(crate) struct AssociatedFunction {
    pub decl: Rc<NominalDecl>,
    pub name: SmolStr,
    /// Its number of value parameters.
    pub arity: usize,
    /// Whether its first value parameter is `self`, which makes it a method.
    pub is_method: bool,
}

/// Record the associated functions among the module's top-level `stmts`, checking each
/// against the type it names: the type is declared here, the name is free in the type's
/// namespace, and the function declares a value parameter.
pub(super) fn declare_associated_functions(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for stmt in stmts {
        match &stmt.node {
            ChlStmt::FunctionDef {
                owner: Some(owner),
                name,
                params,
                ..
            } => {
                if let Err(e) = declare_one(owner, name, params, None, stmt.span, ctx) {
                    errors.push(e);
                }
            }
            ChlStmt::Impl(block) => {
                for def in &block.defs {
                    let ChlStmt::FunctionDef {
                        owner,
                        name,
                        params,
                        ..
                    } = &def.node
                    else {
                        unreachable!("the parser builds an `impl` block of `def`s")
                    };
                    let result = match owner {
                        Some(other) => Err(LoweringError::unsupported(
                            other.span,
                            format!(
                                "a `def` in `impl {}:` belongs to `{}` and names no type of \
                                 its own; write `def {name}(…)`",
                                block.ty.node, block.ty.node
                            ),
                        )),
                        None => declare_one(&block.ty, name, params, Some(block), def.span, ctx),
                    };
                    if let Err(e) = result {
                        errors.push(e);
                    }
                }
            }
            _ => {}
        }
    }
    errors
}

fn declare_one(
    owner: &Spanned<SmolStr>,
    name: &SmolStr,
    params: &[Param],
    block: Option<&ImplBlock>,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    let Some(decl) = ctx.nominal_type(&owner.node) else {
        return Err(LoweringError::unsupported(
            owner.span,
            format!(
                "`{}` is not a nominal type this module declares, so `{}::{name}` has no \
                 type to belong to",
                owner.node, owner.node
            ),
        ));
    };
    if let Some(block) = block
        && block.params.len() != decl.params.len()
    {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`{}` takes {} type parameter{}, and `impl {}` names {}",
                decl.name,
                decl.params.len(),
                if decl.params.len() == 1 { "" } else { "s" },
                decl.name,
                block.params.len()
            ),
        ));
    }
    let taken = decl.ctor(name).is_some()
        || (decl.declares_extract && name == "extract")
        || ctx
            .associated_functions
            .iter()
            .any(|f| f.decl == decl && f.name == *name);
    if taken {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{name}` is already declared; a type's constructors and associated \
                 functions share one namespace",
                decl.name
            ),
        ));
    }
    let Some(first) = params.first() else {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{name}` declares no parameters; a function of no argument is a constant, \
                 and an associated value has no spelling yet",
                decl.name
            ),
        ));
    };
    if let Some(p) = params.iter().find(|p| {
        p.annotation
            .as_ref()
            .is_some_and(|a| matches!(&a.ty.node, ChlExpr::Call { func, .. } if matches!(&func.node, ChlExpr::Name(n) if n == "Mut")))
    }) {
        return Err(LoweringError::unsupported(
            p.name_span,
            format!(
                "`{}::{name}` takes a `Mut` parameter `{}`; an associated function with a \
                 pass-by-reference parameter is not supported yet",
                decl.name, p.name
            ),
        ));
    }
    let is_method = first.name == "self";
    if is_method && first.annotation.is_none() && !decl.params.is_empty() && block.is_none() {
        return Err(LoweringError::unsupported(
            first.name_span,
            format!(
                "`self` of `{0}::{name}` needs its type, since `{0}` takes type parameters: \
                 `self: {0}(…)` over the function's own, or declare it in `impl {0}(…):`",
                decl.name
            ),
        ));
    }
    ctx.associated_functions.push(AssociatedFunction {
        decl,
        name: name.clone(),
        arity: params.len(),
        is_method,
    });
    Ok(())
}

/// Lower the associated function `def N::name(params)` of `decl` to its binding's name and
/// value, as a `def` with type parameters is lowered: an `impl` block's parameters come
/// first, and a method's `self` without an annotation is annotated with the declaration
/// at those parameters (`docs/chl-spec.md`, "Associated functions and methods").
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_associated_def(
    decl: &Rc<NominalDecl>,
    impl_params: &[Spanned<SmolStr>],
    name: &str,
    type_params: &[ChlTypeParam],
    params: &[Param],
    output: Option<&Spanned<ChlExpr>>,
    requires: &[Spanned<Requirement>],
    body: &[Spanned<ChlStmt>],
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(String, Expr, Option<Type>), LoweringError> {
    let mut all_type_params: Vec<ChlTypeParam> = impl_params
        .iter()
        .map(|p| ChlTypeParam {
            name: p.node.clone(),
            name_span: p.span,
            annotation: None,
        })
        .collect();
    all_type_params.extend(type_params.iter().cloned());
    let mut params = params.to_vec();
    if let Some(first) = params.first_mut()
        && first.name == "self"
        && first.annotation.is_none()
    {
        let head = Spanned::new(first.name_span, ChlExpr::Name(decl.name.clone()));
        let ty = if impl_params.is_empty() {
            head
        } else {
            let args = impl_params
                .iter()
                .map(|p| Spanned::new(p.span, ChlExpr::Name(p.node.clone())))
                .collect();
            Spanned::new(
                first.name_span,
                ChlExpr::Call {
                    func: Box::new(head),
                    args,
                },
            )
        };
        first.annotation = Some(TypeAnnotation {
            mode: AnnotationMode::Exact,
            ty,
        });
    }
    let (func, annotation) =
        super::functions::lower_def(span, &all_type_params, &params, output, requires, body, ctx)?;
    Ok((constructor_binding(decl, name), func, annotation))
}

/// Lower a method call `receiver.method(args)`: the application of a [`TypedExprNode::Method`]
/// placeholder over every type that declares the method, to the receiver and the arguments
/// (`src/ccl/design/nominal-types.md`, "Method calls").
pub(super) fn lower_method_call(
    receiver: &Spanned<ChlExpr>,
    method: &Spanned<SmolStr>,
    args: &[Spanned<ChlExpr>],
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let mut owners: Vec<Rc<NominalDecl>> = ctx
        .associated_functions
        .iter()
        .filter(|f| f.is_method && f.name == method.node)
        .map(|f| Rc::clone(&f.decl))
        .collect();
    if method.node == "extract" {
        owners.extend(
            ctx.nominal_types
                .iter()
                .filter(|d| d.declares_extract)
                .cloned(),
        );
    }
    if owners.is_empty() {
        return Err(LoweringError::unsupported(
            method.span,
            format!(
                "no type this module declares has a method `{}`",
                method.node
            ),
        ));
    }
    let candidates = owners
        .into_iter()
        .map(|decl| {
            let reference = Expr::var(constructor_binding(&decl, &method.node));
            let reference = ctx.tag_image(reference, method.span);
            (decl, reference)
        })
        .collect();
    let placeholder = ctx.tag_image(
        Expr::new(TypedExprNode::Method {
            name: method.node.to_string(),
            with_args: !args.is_empty(),
            candidates,
        }),
        method.span,
    );
    let receiver = super::lower_expr(receiver, ctx)?;
    let argument = if args.is_empty() {
        receiver
    } else {
        let mut parts = vec![receiver];
        for a in args {
            parts.push(super::lower_expr(a, ctx)?);
        }
        ctx.tag_machinery(Expr::tuple(parts), span, "lower.call_tuple")
    };
    Ok(Expr::apply(argument, placeholder))
}

/// One `def` of an `impl` block, lowered: its binding's name, value and annotation.
pub(super) struct LoweredDef {
    pub name: String,
    pub func: Expr,
    pub annotation: Option<Type>,
    pub span: Span,
}

/// `defs`, the `impl` block's functions, ordered so each is bound after the block's
/// functions it names, so the block's functions reach each other in any order
/// (`docs/chl-spec.md`, "Associated functions and methods"). The order is otherwise the
/// source order.
///
/// A function names another through `N::g` or `self.g(…)`, both of which leave the
/// reference `N::g` free in its lowered value: a method call's placeholder holds every
/// candidate as a reference. A cycle between two functions is refused, since a function
/// does not reach itself. A function's reference to its own name is no edge: a method call
/// on another type's value names every type declaring the method, the function's own type
/// among them.
pub(super) fn order_by_reference(
    defs: Vec<LoweredDef>,
    block_span: Span,
) -> Result<Vec<LoweredDef>, LoweringError> {
    let names: Vec<String> = defs.iter().map(|d| d.name.clone()).collect();
    let edges: Vec<Vec<usize>> = defs
        .iter()
        .enumerate()
        .map(|(at, d)| {
            let free = crate::ccl::ccl_utils::free_names_in_value(&d.func);
            let mut out: Vec<usize> = names
                .iter()
                .enumerate()
                .filter(|&(i, n)| i != at && free.iter().any(|f| f.base() == n.as_str()))
                .map(|(i, _)| i)
                .collect();
            out.sort_unstable();
            out
        })
        .collect();
    if let Some(cycle) = find_cycle(&edges) {
        let spelled: Vec<&str> = cycle.iter().map(|&i| names[i].as_str()).collect();
        return Err(LoweringError::unsupported(
            block_span,
            format!(
                "the functions {} call each other in a cycle; a function does not reach \
                 itself",
                spelled
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    }
    let mut placed = vec![false; defs.len()];
    let mut order: Vec<usize> = Vec::with_capacity(defs.len());
    fn place(i: usize, edges: &[Vec<usize>], placed: &mut [bool], order: &mut Vec<usize>) {
        if placed[i] {
            return;
        }
        placed[i] = true;
        for &j in &edges[i] {
            place(j, edges, placed, order);
        }
        order.push(i);
    }
    for i in 0..defs.len() {
        place(i, &edges, &mut placed, &mut order);
    }
    let mut slots: Vec<Option<LoweredDef>> = defs.into_iter().map(Some).collect();
    Ok(order
        .into_iter()
        .map(|i| slots[i].take().expect("each placed once"))
        .collect())
}
