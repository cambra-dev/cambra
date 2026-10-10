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
use crate::ccl::{Expr, Lit, Type, TypedExprNode};
use crate::chl_parser::ast::{
    Expr as ChlExpr, QualifiedName, Span, Spanned, Stmt as ChlStmt, TypeDecl, TypeDeclBody,
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
        ctx.nominal_types
            .push(NominalDecl::declared(name.node.clone(), params, name.span));
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

/// Wrap `body` in the binding of each constructor function the module declares.
pub(super) fn bind_constructors(body: Expr, ctx: &mut LoweringContext) -> Expr {
    let decls = ctx.nominal_types.clone();
    let mut acc = body;
    for decl in decls.iter().rev() {
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
            let mut function = Expr::lambda(arg, Type::Hole, value);
            if let TypedExprNode::Lambda { param, .. } = &mut function.node {
                param.declare(ctor.payload());
            }
            let function = ctx.tag_machinery(function, ctor.span, label);
            let name = constructor_binding(decl, &ctor.name);
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
            acc = ctx.tag_machinery(binding, ctor.span, label);
        }
    }
    acc
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
        None => Err(LoweringError::unsupported(
            span,
            format!("`{}` declares no constructor `{}`", decl.name, q.name.node),
        )),
    }
}

/// Lower a name qualified by a type, `Shape::circle`: the constructor function, or the
/// value a constructor without parameters builds.
pub(super) fn lower_member(
    q: &QualifiedName,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let decl = resolve_constructor(q, span, ctx)?;
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
    let ctor = decl.ctor(&q.name.node).expect("resolved above");
    if ctor.params.is_empty() {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{0}::{1}` declares no parameters, so it is a value and not a function: \
                 write `{0}::{1}`",
                decl.name, ctor.name
            ),
        ));
    }
    if args.len() != ctor.params.len() {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{}` takes {} argument{}, got {}",
                decl.name,
                ctor.name,
                ctor.params.len(),
                if ctor.params.len() == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    let name = constructor_binding(&decl, &ctor.name);
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
