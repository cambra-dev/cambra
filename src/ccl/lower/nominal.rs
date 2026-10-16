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

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use super::stmts::{is_mut_annotation, lower_type_expr, reserved_name};
use super::{LoweringContext, LoweringError};
use crate::ccl::nominal::{NominalCtor, NominalDecl};
use crate::ccl::ty::{PolyParam, PolyType, TypeKind, TypeParam};
use crate::ccl::{
    Expr, Lit, MethodCandidate, MethodOwner, Pattern, PatternHead, Type, TypedBinding,
    TypedExprNode,
};
use crate::ccl::{V_NONE, V_SOME};
use crate::chl_parser::ast::{
    AnnotationMode, ArmPattern, ConstructorPattern, Expr as ChlExpr, ImplBlock, MatchArm, Param,
    QualifiedName, Requirement, Span, Spanned, Stmt as ChlStmt, TypeAnnotation, TypeDecl,
    TypeDeclBody, TypeParam as ChlTypeParam,
};

/// The name the function a declaration's member `name` declares is bound to, `Shape::rect`.
fn member_binding(decl: &NominalDecl, name: &str) -> String {
    format!("{}::{name}", decl.name)
}

fn type_decls(stmts: &[Spanned<ChlStmt>]) -> impl Iterator<Item = (&TypeDecl, Span)> {
    stmts.iter().filter_map(|s| match &s.node {
        ChlStmt::TypeDecl(decl) => Some((decl, s.span)),
        _ => None,
    })
}

/// A `def` declaring an associated function: `def N::f(…)`, or a `def f(…)` in `impl N(𝑃…):`.
pub(super) struct AssociatedDef<'a> {
    /// The type it belongs to: its qualifier, or the block's type.
    pub owner: &'a Spanned<SmolStr>,
    /// The qualifier a `def` in a block carries, `def M::f` in `impl N:`, which names no type
    /// of its own.
    pub stray_owner: Option<&'a Spanned<SmolStr>>,
    pub name: &'a Spanned<SmolStr>,
    pub type_params: &'a [ChlTypeParam],
    pub params: &'a [Param],
    pub output: Option<&'a Spanned<ChlExpr>>,
    pub requires: &'a [Spanned<Requirement>],
    pub body: &'a [Spanned<ChlStmt>],
    /// The block declaring it, if it is in one.
    pub block: Option<&'a ImplBlock>,
    /// The type parameters the block binds, none outside a block (`inherent_params`).
    pub block_params: Vec<Spanned<SmolStr>>,
    /// The `def`.
    pub span: Span,
}

/// The associated functions `stmt` declares: the one `def N::f(…)` declares, and each `def` of
/// an inherent `impl` block, a `pub def` as its `def`. An instance of a trait declares none.
pub(super) fn associated_defs<'a>(
    stmt: &'a Spanned<ChlStmt>,
    ctx: &LoweringContext,
) -> Result<Vec<AssociatedDef<'a>>, LoweringError> {
    fn view<'a>(
        def: &'a Spanned<ChlStmt>,
        block: Option<&'a ImplBlock>,
        block_params: Vec<Spanned<SmolStr>>,
    ) -> AssociatedDef<'a> {
        let def = match &def.node {
            ChlStmt::Pub { stmt, .. } => stmt.as_ref(),
            _ => def,
        };
        let ChlStmt::FunctionDef {
            owner,
            name,
            type_params,
            params,
            output,
            requires,
            body,
        } = &def.node
        else {
            unreachable!("the parser builds an `impl` block of `def`s")
        };
        let (owner, stray_owner) = match (block, owner) {
            (Some(block), owner) => (&block.ty, owner.as_ref()),
            (None, Some(owner)) => (owner, None),
            (None, None) => unreachable!("a `def` outside a block is viewed with its owner"),
        };
        AssociatedDef {
            owner,
            stray_owner,
            name,
            type_params,
            params,
            output: output.as_ref(),
            requires,
            body,
            block,
            block_params,
            span: def.span,
        }
    }
    Ok(match &stmt.node {
        ChlStmt::FunctionDef { owner: Some(_), .. } => vec![view(stmt, None, Vec::new())],
        // An instance of a trait is `traits::declare_instances`'s.
        ChlStmt::Impl(block) if ctx.trait_named(&block.ty.node).is_some() => Vec::new(),
        ChlStmt::Impl(block) => {
            let params = inherent_params(block)?;
            block
                .defs
                .iter()
                .map(|d| view(d, Some(block), params.clone()))
                .collect()
        }
        _ => Vec::new(),
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
        if let Some(what) = reserved_name(&name.node) {
            errors.push(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is a built-in {what} and cannot be given another meaning",
                    name.node
                ),
            ));
            continue;
        }
        if let Some(first) = ctx.nominal_type(&name.node) {
            errors.push(
                LoweringError::unsupported(
                    name.span,
                    format!(
                        "`{}` is declared twice in this module; a `type` binds its name once",
                        name.node
                    ),
                )
                .with_related(first.span, "first declared here"),
            );
            continue;
        }
        let mut params: Vec<Rc<TypeParam>> = Vec::new();
        for param in &decl.params {
            if let Some(what) = reserved_name(&param.node) {
                errors.push(LoweringError::unsupported(
                    param.span,
                    format!(
                        "`{}` is a built-in {what} and cannot name a type parameter",
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
        let head = ctx
            .nominal_type(&decl.name.node)
            .expect("`declare_nominal_types` declared every head, or lowering stopped");
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
    let mut defined = vec![Progress::Pending; lowered.len()];
    let mut slots: Vec<Option<Vec<NominalCtor>>> = lowered
        .iter_mut()
        .map(|(_, c)| Some(std::mem::take(c)))
        .collect();
    for i in 0..lowered.len() {
        define_after_references(i, &lowered, &edges, &mut slots, &mut defined, &mut errors);
    }
    errors
}

/// How far [`define_after_references`] has taken a declaration.
#[derive(Clone, Copy, PartialEq)]
enum Progress {
    Pending,
    Defined,
    /// Its `define` failed, or one it references failed, so it has no body to read.
    Failed,
}

/// Define declaration `i` after every declaration it references.
///
/// A declaration referencing one that failed is left undefined: `define` reads the variances
/// of the declarations it names, and a failed one has none. Its own error would only repeat
/// the first.
fn define_after_references(
    i: usize,
    lowered: &[(Rc<NominalDecl>, Vec<NominalCtor>)],
    edges: &[Vec<usize>],
    slots: &mut [Option<Vec<NominalCtor>>],
    defined: &mut [Progress],
    errors: &mut Vec<LoweringError>,
) {
    if defined[i] != Progress::Pending {
        return;
    }
    defined[i] = Progress::Defined;
    for &j in &edges[i] {
        define_after_references(j, lowered, edges, slots, defined, errors);
    }
    if edges[i].iter().any(|&j| defined[j] == Progress::Failed) {
        defined[i] = Progress::Failed;
        return;
    }
    let decl = &lowered[i].0;
    let ctors = slots[i].take().expect("each declaration is defined once");
    if let Err(unused) = decl.define(ctors) {
        defined[i] = Progress::Failed;
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
                let mut seen: HashMap<&str, Span> = HashMap::new();
                for line in lines {
                    if let Some(&first) = seen.get(line.name.node.as_str()) {
                        return Err(LoweringError::unsupported(
                            line.name.span,
                            format!(
                                "`{}` declares the constructor `{}` twice",
                                decl.name.node, line.name.node
                            ),
                        )
                        .with_related(first, "first declared here"));
                    }
                    seen.insert(line.name.node.as_str(), line.name.span);
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
            if !ctor.params.is_empty() {
                acc = bind_constructor(decl, ctor, acc, ctx);
            }
        }
    }
    // A compiler-provided declaration's members are bound only where the module names them
    // (`LoweringContext::builtin_members_used`).
    let used = std::mem::take(&mut ctx.builtin_members_used);
    for (decl, name) in used.into_values().rev() {
        acc = match decl.ctor(&name) {
            Some(ctor) => bind_constructor(&decl, ctor, acc, ctx),
            None if name == IS_NONE => bind_is_none(&decl, acc, ctx),
            None => unreachable!("`{}` provides no function `{name}`", decl.name),
        };
    }
    acc
}

/// `N::c`, the function `λ __ctor_arg : payload → N::c(__ctor_arg)` a constructor that
/// declares parameters is.
fn bind_constructor(
    decl: &Rc<NominalDecl>,
    ctor: &NominalCtor,
    acc: Expr,
    ctx: &mut LoweringContext,
) -> Expr {
    let label = "lower.nominal_ctor";
    let arg = "__ctor_arg";
    let payload = ctx.tag_machinery(Expr::var(arg), ctor.span, label);
    let value = ctx.tag_machinery(
        Expr::nominal_ctor(Rc::clone(decl), ctor.name.as_str(), payload),
        ctor.span,
        label,
    );
    let name = member_binding(decl, &ctor.name);
    bind_function(
        decl,
        name,
        arg,
        ctor.payload(),
        value,
        acc,
        ctor.span,
        label,
        ctx,
    )
}

/// The method `Option::is_none` that the compiler provides with `Option`.
const IS_NONE: &str = "is_none";

/// `Option::is_none`, the function `λ o → match o: case Option::some(_): False; case
/// Option::none: True` (`docs/chl-spec.md`, "Subscript and unwrap syntax \[Decided\]").
fn bind_is_none(decl: &Rc<NominalDecl>, acc: Expr, ctx: &mut LoweringContext) -> Expr {
    let label = "lower.option_is_none";
    let span = decl.span;
    let arg = "__is_none_arg";
    let scrutinee = ctx.tag_machinery(Expr::var(arg), span, label);
    let mut arms = Vec::new();
    for (tag, empty_payload, answer) in [(V_SOME, false, false), (V_NONE, true, true)] {
        let payload = ctx.fresh_ignored_payload();
        arms.push(crate::ccl::Branch {
            pattern: Some(Pattern {
                head: PatternHead::Constructor {
                    decl: Rc::clone(decl),
                    ctor: tag.to_string(),
                },
                binding: TypedBinding::new_unannotated(payload),
                empty_payload,
            }),
            guard: ctx.tag_machinery(Expr::lit(Lit::Bool(true)), span, label),
            body: ctx.tag_machinery(Expr::lit(Lit::Bool(answer)), span, label),
        });
    }
    let case = ctx.tag_machinery(Expr::match_expr(scrutinee, arms), span, label);
    let name = member_binding(decl, IS_NONE);
    let self_ty = decl.applied_to_params();
    bind_function(decl, name, arg, self_ty, case, acc, span, label, ctx)
}

/// The name a reference to `decl`'s member `name` reads, recording the member as used when
/// the compiler provides `decl`.
fn member_reference(decl: &Rc<NominalDecl>, name: &str, ctx: &mut LoweringContext) -> String {
    let binding = member_binding(decl, name);
    if decl.is_builtin() {
        ctx.builtin_members_used
            .entry(binding.clone())
            .or_insert_with(|| (Rc::clone(decl), SmolStr::from(name)));
    }
    binding
}

/// The associated functions the compiler provides with its declarations.
fn builtin_functions() -> [AssociatedFunction; 1] {
    let option = crate::ccl::nominal::option();
    let span = option.span;
    [AssociatedFunction {
        decl: option,
        name: SmolStr::new_static(IS_NONE),
        arity: 1,
        is_method: true,
        span,
    }]
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
    let [ctor] = decl.body().ctors.as_slice() else {
        unreachable!(
            "`{}` declares `extract`, so it is the single-constructor form, which declares one \
             constructor",
            decl.name
        )
    };
    let case = Expr::match_expr(
        scrutinee,
        vec![crate::ccl::Branch {
            pattern: Some(Pattern {
                head: PatternHead::Constructor {
                    decl: Rc::clone(decl),
                    ctor: ctor.name.to_string(),
                },
                binding: TypedBinding::new_unannotated(payload),
                empty_payload: false,
            }),
            guard,
            body: read,
        }],
    );
    let case = ctx.tag_machinery(case, span, label);
    let name = member_binding(decl, "extract");
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

/// A name in a nominal type's namespace, which its constructors, the single-constructor
/// form's `extract` and its associated functions share (`docs/chl-spec.md`, "Associated
/// functions and methods").
#[derive(Clone, Copy)]
enum Member {
    /// A constructor, with its number of parameters.
    Constructor { arity: usize },
    /// The `extract` of the single-constructor form.
    Extract,
    /// An associated function, with its number of value parameters.
    Associated { arity: usize },
}

impl Member {
    /// The number of arguments a call of the member passes.
    fn arity(self) -> usize {
        match self {
            Member::Constructor { arity } | Member::Associated { arity } => arity,
            Member::Extract => 1,
        }
    }
}

/// The member of `decl` named `name`, if it declares one, with the span that declares it.
fn member(decl: &NominalDecl, name: &str, ctx: &LoweringContext) -> Option<(Member, Span)> {
    if let Some(ctor) = decl.ctor(name) {
        let arity = ctor.params.len();
        return Some((Member::Constructor { arity }, ctor.span));
    }
    if decl.declares_extract && name == "extract" {
        return Some((Member::Extract, decl.span));
    }
    ctx.associated_functions
        .iter()
        .cloned()
        .chain(builtin_functions())
        .find(|f| *f.decl == *decl && f.name == name)
        .map(|f| (Member::Associated { arity: f.arity }, f.span))
}

/// Where `decl` declares a member named `name`, if it declares one: for the namespace a
/// type's own functions share with its instances' methods.
pub(super) fn member_span(decl: &NominalDecl, name: &str, ctx: &LoweringContext) -> Option<Span> {
    member(decl, name, ctx).map(|(_, span)| span)
}

/// The type parameters an inherent `impl N(P…):` head binds: its arguments, each a name.
/// An associated type or a `requires` clause belongs to an instance of a trait.
pub(super) fn inherent_params(block: &ImplBlock) -> Result<Vec<Spanned<SmolStr>>, LoweringError> {
    let ty = &block.ty.node;
    if let Some(v) = block.vars.first() {
        return Err(LoweringError::unsupported(
            v.span,
            format!(
                "`impl {ty}(…)` declares functions of the type `{ty}`, whose head names its \
                 parameters; `forall` declares the type variables of an instance of a trait"
            ),
        ));
    }
    if let Some(a) = block.assoc.first() {
        return Err(LoweringError::unsupported(
            a.name_span,
            format!(
                "`impl {ty}(…)` declares functions of the type `{ty}`, and `{}=…` fixes an \
                 associated type, which only an instance of a trait does",
                a.name
            ),
        ));
    }
    if let Some(r) = block.requires.first() {
        return Err(LoweringError::unsupported(
            r.span,
            format!(
                "`impl {ty}(…)` declares functions of the type `{ty}`, and a `requires` clause \
                 on the block belongs to an instance of a trait"
            ),
        ));
    }
    block
        .args
        .iter()
        .map(|a| match &a.node {
            ChlExpr::Name(n) => Ok(Spanned::new(a.span, n.clone())),
            _ => Err(LoweringError::unsupported(
                a.span,
                format!(
                    "`impl {ty}(…)` binds the parameters of the type `{ty}`, each a name, as in \
                     `impl Option(T):`"
                ),
            )),
        })
        .collect()
}

/// The declaration and member `q` names, `Shape::circle`.
fn resolve_member(
    q: &QualifiedName,
    span: Span,
    ctx: &LoweringContext,
) -> Result<(Rc<NominalDecl>, Member), LoweringError> {
    let [ty] = q.qualifier.as_slice() else {
        unreachable!("`refuse_module_syntax` lets through only a name qualified by one type")
    };
    let Some(decl) = ctx.nominal_type(&ty.node) else {
        return Err(LoweringError::unsupported(
            ty.span,
            format!(
                "`{}` is not a nominal type this module declares, so `{}::{}` names nothing",
                ty.node, ty.node, q.name.node
            ),
        ));
    };
    match member(&decl, &q.name.node, ctx) {
        Some((m, _)) => Ok((decl, m)),
        None => Err(LoweringError::unsupported(
            span,
            format!(
                "`{}` declares no constructor or function `{}`",
                decl.name, q.name.node
            ),
        )),
    }
}

/// Lower a name qualified by a type, `Shape::circle`: the value a constructor without
/// parameters builds, or the function any other member is.
pub(super) fn lower_member(
    q: &QualifiedName,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let (decl, member) = resolve_member(q, span, ctx)?;
    match member {
        Member::Constructor { arity: 0 } => {
            let unit = ctx.tag_machinery(Expr::lit(Lit::Unit), span, "lower.nominal_ctor_unit");
            Ok(Expr::nominal_ctor(decl, q.name.node.as_str(), unit))
        }
        _ => Ok(Expr::var(member_reference(&decl, &q.name.node, ctx))),
    }
}

/// Lower a call of a name qualified by a type, `Shape::circle(1)`.
pub(super) fn lower_member_call(
    q: &QualifiedName,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let (decl, member) = resolve_member(q, span, ctx)?;
    let name = &q.name.node;
    match member.arity() {
        0 => Err(LoweringError::unsupported(
            span,
            format!(
                "`{0}::{name}` declares no parameters, so it is a value and not a function: \
                 write `{0}::{name}`",
                decl.name
            ),
        )),
        arity if arity != args.len() => Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{name}` takes {arity} argument{}, got {}",
                decl.name,
                if arity == 1 { "" } else { "s" },
                args.len()
            ),
        )),
        _ => {
            let binding = member_reference(&decl, name, ctx);
            super::exprs::apply_named(&binding, span, args, ctx)
        }
    }
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
        // Each name binds one parameter: a repeated one would say two values are one name.
        (Some(binders), n) if binders.len() == n => {
            let mut seen: HashMap<&str, Span> = HashMap::new();
            for b in binders {
                let Some(name) = &b.node else { continue };
                if let Some(first) = seen.insert(name.as_str(), b.span) {
                    return Err(LoweringError::unsupported(
                        b.span,
                        format!(
                            "`{name}` is bound twice in the pattern `{}::{}(…)`; a pattern \
                             binds each name once",
                            decl.name, ctor.name
                        ),
                    )
                    .with_related(first, "first bound here"));
                }
            }
            Ok(())
        }
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
/// parameter that is the parameter, so the pattern binds it under the parameter's own
/// name. For several it is their tuple, which the pattern binds under a minted name, and
/// each named parameter is projected out of it: by [`bind_parameters`] in a `match` arm,
/// and by [`ConstructorAssignment::bindings`] in an assignment.
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
        head: PatternHead::Constructor {
            decl: Rc::clone(decl),
            ctor: pattern.ctor.node.to_string(),
        },
        binding: TypedBinding::new_unannotated(payload),
        empty_payload: binders.is_empty(),
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

/// A constructor pattern checked for an assignment `N::c(𝑎…) = 𝑣`, ready to take a value
/// apart.
///
/// The assignment means plain bindings ([`bindings`](Self::bindings)), so each statement
/// site lowers it as it lowers `𝑥 = 𝑒`, once per binding. The payload binds to the one-arm
/// `Case` over `𝑣` that answers it, `𝑝 = match 𝑣 { c(𝑝) → 𝑝 }`, and each named parameter
/// of several binds to its projection of the payload, `𝑎ᵢ = 𝑝.𝑖`. `𝑝` is the parameter's
/// own name for a constructor of one parameter, and a minted name otherwise.
pub(super) struct ConstructorAssignment {
    pattern: Pattern,
    binds: Vec<(String, usize)>,
}

impl ConstructorAssignment {
    /// The names the assignment binds, in binding order: the payload's first, then each
    /// named parameter's. For a constructor of several parameters the payload's name is
    /// minted ([`constructor_arm_pattern`]), so no program names it, and it is bound all the
    /// same, which a caller tracking the names in scope needs.
    pub(super) fn names(&self) -> Vec<String> {
        std::iter::once(self.pattern.binding.name.base().to_string())
            .chain(self.binds.iter().map(|(name, _)| name.clone()))
            .collect()
    }

    /// The bindings the assignment means, in order, each a name and its value.
    pub(super) fn bindings(
        self,
        value: Expr,
        span: Span,
        ctx: &mut LoweringContext,
    ) -> Vec<(String, Expr)> {
        let label = "lower.constructor_assignment";
        let payload = self.pattern.binding.name.clone();
        let read = ctx.tag_machinery(Expr::var(payload.clone()), span, label);
        let guard = ctx.tag_machinery(Expr::lit(Lit::Bool(true)), span, "lower.match_guard");
        let case = Expr::match_expr(
            value,
            vec![crate::ccl::Branch {
                pattern: Some(self.pattern),
                guard,
                body: read,
            }],
        );
        let mut out = vec![(
            payload.base().to_string(),
            ctx.tag_machinery(case, span, label),
        )];
        for (name, i) in self.binds {
            let read = ctx.tag_machinery(Expr::var(payload.clone()), span, label);
            let proj = ctx.tag_machinery(Expr::proj_index(i), span, label);
            out.push((
                name,
                ctx.tag_machinery(Expr::apply(read, proj), span, label),
            ));
        }
        out
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
    /// The `def` that declares it.
    pub span: Span,
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
        match associated_defs(stmt, ctx) {
            Ok(defs) => errors.extend(defs.iter().filter_map(|def| declare_one(def, ctx).err())),
            Err(e) => errors.push(e),
        }
    }
    errors
}

fn declare_one(def: &AssociatedDef, ctx: &mut LoweringContext) -> Result<(), LoweringError> {
    let AssociatedDef {
        owner,
        name,
        params,
        block,
        span,
        ..
    } = *def;
    let name = &name.node;
    if let Some(other) = def.stray_owner {
        return Err(LoweringError::unsupported(
            other.span,
            format!(
                "a `def` in `impl {0}:` belongs to `{0}` and names no type of its own; write \
                 `def {name}(…)`",
                owner.node
            ),
        ));
    }
    let Some(decl) = ctx.nominal_type(&owner.node) else {
        return Err(LoweringError::unsupported(
            owner.span,
            format!(
                "`{}` is not a nominal type{} this module declares, so `{}::{name}` has no \
                 type to belong to",
                owner.node,
                if block.is_some() { " or a trait" } else { "" },
                owner.node
            ),
        ));
    };
    // Whether another module may declare a type's associated functions is open, and the
    // compiler provides `Option` from no module (`docs/chl-spec.md`, "Associated functions
    // and methods").
    if decl.is_builtin() {
        return Err(LoweringError::unsupported(
            owner.span,
            format!(
                "`{}` is a built-in type, so this module declares no associated function of it",
                decl.name
            ),
        ));
    }
    if block.is_some() && def.block_params.len() != decl.params.len() {
        return Err(LoweringError::unsupported(
            owner.span,
            format!(
                "`{}` takes {} type parameter{}, and `impl {}` names {}",
                decl.name,
                decl.params.len(),
                if decl.params.len() == 1 { "" } else { "s" },
                decl.name,
                def.block_params.len()
            ),
        ));
    }
    if let Some((_, first)) = member(&decl, name, ctx) {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{name}` is already declared; a type's constructors and associated \
                 functions share one namespace",
                decl.name
            ),
        )
        .with_related(first, "first declared here"));
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
    if let Some(p) = params
        .iter()
        .find(|p| p.annotation.as_ref().is_some_and(is_mut_annotation))
    {
        return Err(LoweringError::unsupported(
            p.name_span,
            format!(
                "`{}::{name}` takes a `Mut` parameter `{}`; an associated function with a \
                 pass-by-reference parameter is not supported yet",
                decl.name, p.name
            ),
        ));
    }
    if let Some(p) = params.iter().skip(1).find(|p| p.name == "self") {
        return Err(LoweringError::unsupported(
            p.name_span,
            format!(
                "`self` of `{}::{name}` is not its first parameter; a method takes its \
                 receiver first",
                decl.name
            ),
        ));
    }
    let is_method = first.name == "self";
    if is_method && let Some(annotation) = &first.annotation {
        check_self_annotation(&decl, name, annotation, def)?;
    }
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
        span,
    });
    Ok(())
}

/// Check the annotation on the `self` of `decl`'s method `name`: `self` is the declaration at
/// type parameters (`docs/chl-spec.md`, "Associated functions and methods"). In an `impl` block
/// and for a type without parameters it takes no annotation, and outside a block a
/// parameterised type's `self` is the type applied to the function's own type parameters, each
/// named once.
fn check_self_annotation(
    decl: &NominalDecl,
    name: &str,
    annotation: &TypeAnnotation,
    def: &AssociatedDef,
) -> Result<(), LoweringError> {
    let qualified = format!("{}::{name}", decl.name);
    if def.block.is_some() {
        let params = def
            .block_params
            .iter()
            .map(|p| p.node.as_str())
            .collect::<Vec<_>>();
        let ty = if params.is_empty() {
            decl.name.to_string()
        } else {
            format!("{}({})", decl.name, params.join(", "))
        };
        return Err(LoweringError::unsupported(
            annotation.ty.span,
            format!(
                "`self` of `{qualified}` is the `{ty}` the block declares functions of, and \
                 takes no annotation"
            ),
        ));
    }
    if decl.params.is_empty() {
        return Err(LoweringError::unsupported(
            annotation.ty.span,
            format!(
                "`self` of `{qualified}` is a `{}`, and takes no annotation",
                decl.name
            ),
        ));
    }
    let own: Vec<&str> = def.type_params.iter().map(|p| p.name.as_str()).collect();
    let args = match &annotation.ty.node {
        ChlExpr::Call { func, args } if matches!(&func.node, ChlExpr::Name(n) if *n == decl.name) => {
            Some(args)
        }
        _ => None,
    };
    let at_own_params = args.is_some_and(|args| {
        let names: Vec<&str> = args
            .iter()
            .filter_map(|a| match &a.node {
                ChlExpr::Name(n) => Some(n.as_str()),
                _ => None,
            })
            .collect();
        names.len() == args.len()
            && names.len() == decl.params.len()
            && names.iter().all(|n| own.contains(n))
            && names.iter().collect::<HashSet<_>>().len() == names.len()
    });
    if annotation.mode != AnnotationMode::Exact || !at_own_params {
        let params = decl
            .params
            .iter()
            .map(|p| p.spelling.as_str())
            .collect::<Vec<_>>();
        return Err(LoweringError::unsupported(
            annotation.ty.span,
            format!(
                "`self` of `{qualified}` is `{0}` at type parameters of the function's own, \
                 each named once: `self: {0}({1})` for `def {0}::{name}({1}, self: …)`",
                decl.name,
                params.join(", ")
            ),
        ));
    }
    Ok(())
}

/// Lower the associated function `def N::name(params)` of `decl` to its binding's name and
/// value, as a `def` with type parameters is lowered: an `impl` block's parameters come
/// first, and a method's `self` without an annotation is annotated with the declaration
/// at those parameters (`docs/chl-spec.md`, "Associated functions and methods").
pub(super) fn lower_associated_def(
    decl: &Rc<NominalDecl>,
    def: &AssociatedDef,
    ctx: &mut LoweringContext,
) -> Result<(String, Expr, Option<Type>), LoweringError> {
    let impl_params = def.block_params.as_slice();
    let AssociatedDef {
        name,
        type_params,
        params,
        output,
        requires,
        body,
        span,
        ..
    } = *def;
    let name = name.node.as_str();
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
    Ok((member_binding(decl, name), func, annotation))
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
    // A position is spelled as digits, which no method's name is.
    if method.node.bytes().all(|b| b.is_ascii_digit()) {
        return Err(LoweringError::unsupported(
            method.span,
            format!(
                "`.{0}(…)` calls a method, and `{0}` is a position, which names no method; the \
                 function element {0} holds is called as `(t.{0})(…)`",
                method.node
            ),
        ));
    }
    // Each type declaring the method, with the parameters the method takes after `self`.
    let mut owners: Vec<(Rc<NominalDecl>, usize)> = ctx
        .associated_functions
        .iter()
        .cloned()
        .chain(builtin_functions())
        .filter(|f| f.is_method && f.name == method.node)
        .map(|f| (Rc::clone(&f.decl), f.arity - 1))
        .collect();
    if method.node == "extract" {
        owners.extend(
            ctx.nominal_types
                .iter()
                .filter(|d| d.declares_extract)
                .map(|d| (Rc::clone(d), 0)),
        );
    }
    let traits = super::traits::methods_named(&method.node, ctx);
    if owners.is_empty() && traits.is_empty() {
        return Err(LoweringError::unsupported(
            method.span,
            format!(
                "no type this module declares and no trait has a method `{0}`; the function a \
                 field holds is called as `(r.{0})(…)`",
                method.node
            ),
        ));
    }
    let mut candidates: Vec<MethodCandidate> = owners
        .into_iter()
        .map(|(decl, params)| {
            let reference = Expr::var(member_reference(&decl, &method.node, ctx));
            let function = ctx.tag_image(reference, method.span);
            MethodCandidate {
                owner: MethodOwner::Type(decl),
                params,
                function,
            }
        })
        .collect();
    candidates.extend(traits.into_iter().map(|(trait_, declared)| {
        let function = super::traits::trait_function(&trait_, &declared.name, method.span, ctx);
        MethodCandidate {
            owner: MethodOwner::Trait(trait_),
            params: declared.params_after_self,
            function,
        }
    }));
    let placeholder = ctx.tag_image(
        Expr::new(TypedExprNode::Method {
            name: method.node.to_string(),
            args: args.len(),
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
