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

use super::constants::Refused;
use super::stmts::{is_mut_annotation, lower_type_expr, reserved_name};
use super::{LoweringContext, LoweringError};
use crate::ccl::ccl_utils::strip_refinements;
use crate::ccl::nominal::{NominalCtor, NominalDecl, WrittenOrder};
use crate::ccl::ty::{PolyParam, PolyType, TypeKind, TypeParam, TypeParamId};
use crate::ccl::{
    Expr, FieldKey, Lit, MethodCandidate, Name, Pattern, PatternHead, Type, TypedBinding,
    TypedExprNode,
};
use crate::ccl::{V_NONE, V_SOME};
use crate::chl_parser::ast::{
    AnnotationMode, ArmPattern, Clause, ConstructorPattern, Expr as ChlExpr, ImplBlock, MatchArm,
    Param, QualifiedName, Requirement, Span, Spanned, Stmt as ChlStmt, TraitType, TypeAnnotation,
    TypeDecl, TypeDeclBody, TypeParam as ChlTypeParam,
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
    pub requires: &'a Clause<Requirement>,
    pub causes: &'a Clause<TraitType>,
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
            causes,
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
            causes,
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
        ChlStmt::Impl(block) if block.defs.is_empty() => {
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`impl {}` defines no function; a type's `impl` block declares its \
                     associated functions, and only an instance of a trait that declares none \
                     is written without a block",
                    block.ty.node
                ),
            ));
        }
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
        // A declaration is at its module's path, and the root's at the empty one.
        let module = ctx
            .module
            .labels
            .as_ref()
            .map_or_else(Vec::new, |path| path.segments().to_vec());
        ctx.nominal_types.push(NominalDecl::declared_in(
            module,
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
        ctx.declare_type_throughout(
            param.spelling.as_str(),
            crate::ccl::module_type::AliasType::Type(Type::Param(Rc::clone(param))),
        );
        ctx.type_params_in_scope.push(param.spelling.to_string());
    }
    let result = (|| {
        let mut ctors: Vec<NominalCtor> = Vec::new();
        match &decl.body {
            TypeDeclBody::Single(ty) => {
                let lowered = lower_parameter_type(ty, ctx)?;
                ctors.push(NominalCtor {
                    name: SmolStr::new_static("new"),
                    span: decl.name.span,
                    orders: vec![written_order(ty, &lowered)],
                    params: vec![(None, lowered)],
                })
            }
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
                    let orders = line
                        .params
                        .iter()
                        .zip(&params)
                        .map(|(p, (_, ty))| written_order(&p.ty, ty))
                        .collect();
                    ctors.push(NominalCtor {
                        name: line.name.node.clone(),
                        span: line.name.span,
                        params,
                        orders,
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

/// The order of the parameter type `ty` the declaration writes as `written`: each record it
/// writes by its fields as written, and what it names through an alias as
/// [`WrittenOrder::of_type`] reads it.
fn written_order(written: &Spanned<ChlExpr>, ty: &Type) -> WrittenOrder {
    match (&written.node, ty.peel_refinements()) {
        (ChlExpr::BraceRefinement { base, .. }, _) => written_order(base, ty),
        (ChlExpr::BraceRecord(fields), Type::Record(types)) => WrittenOrder::Fields(
            fields
                .iter()
                .map(|f| {
                    let field = types.iter().find(|(n, _)| n.name() == f.name.as_str());
                    let order =
                        field.map_or(WrittenOrder::Whole, |(_, t)| written_order(&f.value, t));
                    let label = field.map_or_else(|| f.name.as_str().into(), |(n, _)| n.clone());
                    (FieldKey::Name(label), order)
                })
                .collect(),
        ),
        (ChlExpr::BraceGroup(parts), Type::Tuple(elems)) if parts.len() == elems.len() => {
            WrittenOrder::Fields(
                parts
                    .iter()
                    .zip(elems)
                    .enumerate()
                    .map(|(i, (p, t))| (FieldKey::Index(i), written_order(p, t)))
                    .collect(),
            )
        }
        _ => WrittenOrder::of_type(ty),
    }
}

/// Lower a constructor's parameter type, which is written in full: nothing infers a
/// declaration's types.
fn lower_parameter_type(
    ty: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let lowered = lower_type_expr(ty, ctx)?;
    if lowered.holds_type(&|ty| matches!(ty, Type::Hole | Type::BoundedHole(_))) {
        return Err(LoweringError::unsupported(
            ty.span,
            "a constructor's parameter type is written in full; `_` leaves part of it to \
             inference, which no declaration has",
        ));
    }
    // A refinement in a declaration names only `_` and constants (`docs/chl-spec.md`, "6.4
    // Refinement syntax"). Each constant it names is replaced by its term, so the type reads
    // only the module's `const` parameters, which the constructor functions are bound below
    // (`bind_constructors`).
    let mut lowered = lowered;
    for name in crate::ccl::subst::type_free_vars(&lowered) {
        let base = SmolStr::from(name.base());
        if ctx.constants.param(&base).is_some() {
            continue;
        }
        let term = match base.split_once("::") {
            // Another module's constant, as this module writes it.
            Some((qualifier, member)) => ctx.qualified_const(qualifier, member, ty.span),
            // A binding of the module, or another module's constant through a `use` name.
            None => ctx.declared_const(&base, ty.span),
        };
        let term = match term {
            Ok(term) => term,
            Err(Refused(Some(error))) => return Err(error),
            // A member of a module with errors of its own, which those errors account for:
            // the type keeps no refinement, and reports nothing more.
            Err(Refused(None)) => return Ok(strip_refinements(&lowered)),
        };
        if !predicate_holds(&term) {
            return Err(LoweringError::unsupported(
                ty.span,
                format!(
                    "this refinement reads `{base}`, whose value is `{term}`; a tuple, a \
                     record or a list constant in a declaration's refinement is not \
                     supported yet"
                ),
            ));
        }
        replace_in_predicates(&mut lowered, &base, &mut || {
            predicate_term(
                &term,
                &|param| Name::raw(param.spelling.as_str()),
                ty.span,
                ctx,
            )
        });
    }
    Ok(lowered)
}

/// Whether a predicate can hold `term` ([`predicate_term`]).
pub(in crate::ccl::lower) fn predicate_holds(term: &crate::ccl::constant::ConstTerm) -> bool {
    use crate::ccl::constant::ConstTerm;
    match term {
        ConstTerm::Lit(_) | ConstTerm::Param(_) => true,
        ConstTerm::BinOp(_, l, r) => predicate_holds(l) && predicate_holds(r),
        ConstTerm::Neg(t) | ConstTerm::Not(t) => predicate_holds(t),
        ConstTerm::If(c, t, e) => predicate_holds(c) && predicate_holds(t) && predicate_holds(e),
        ConstTerm::Tuple(_) | ConstTerm::Record(_) | ConstTerm::List(_) => false,
        // A field or an element of a constant reads a tuple, a record or a list.
        ConstTerm::Field(..) | ConstTerm::Element(..) => false,
    }
}

/// `term`, which [`predicate_holds`], as a predicate reads it, with each `const` parameter
/// read through the name `param` gives it, each node an image of `span`.
pub(in crate::ccl::lower) fn predicate_term(
    term: &crate::ccl::constant::ConstTerm,
    param: &dyn Fn(&crate::ccl::constant::ConstParam) -> Name,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    use crate::ccl::UnaryOpKind;
    use crate::ccl::constant::ConstTerm;
    let expr = match term {
        ConstTerm::Lit(lit) => Expr::lit(lit.clone()),
        ConstTerm::Param(p) => Expr::var(param(p)),
        ConstTerm::BinOp(op, l, r) => {
            let l = predicate_term(l, param, span, ctx);
            let r = predicate_term(r, param, span, ctx);
            Expr::binop(l, *op, r)
        }
        ConstTerm::Neg(t) => Expr::unary(UnaryOpKind::Neg, predicate_term(t, param, span, ctx)),
        ConstTerm::Not(t) => Expr::unary(UnaryOpKind::Not, predicate_term(t, param, span, ctx)),
        // As a ternary lowers: the first branch whose guard holds.
        ConstTerm::If(c, t, e) => {
            let guard = predicate_term(c, param, span, ctx);
            let then = predicate_term(t, param, span, ctx);
            let otherwise = predicate_term(e, param, span, ctx);
            let always = ctx.tag_machinery(Expr::lit(Lit::Bool(true)), span, "lower.ternary_else");
            Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    crate::ccl::Branch {
                        pattern: None,
                        guard,
                        body: then,
                    },
                    crate::ccl::Branch {
                        pattern: None,
                        guard: always,
                        body: otherwise,
                    },
                ],
            })
        }
        _ => unreachable!("a predicate holds `{term}`"),
    };
    ctx.tag_image(expr, span)
}

/// `ty` with each free reference to the raw name `name` in its predicates replaced by a
/// term `with` builds. Rebuilding a predicate copies it, and a copy mints nothing, so every
/// term is built before the rebuild that places it.
fn replace_in_predicates(ty: &mut Type, name: &str, with: &mut dyn FnMut() -> Expr) {
    use crate::ccl::scope::{
        ScopedItem, ScopedItemMut, for_each_scoped_item, for_each_scoped_item_mut,
    };
    let name = Name::raw(name);
    fn count(expr: &Expr, name: &Name) -> usize {
        if matches!(&expr.node, TypedExprNode::Var(n) if n == name) {
            return 1;
        }
        let mut n = 0;
        for_each_scoped_item(expr, &mut |item| {
            if let ScopedItem::Child { expr, binders } = item
                && !binders.shadows(name)
            {
                n += count(expr, name);
            }
        });
        n
    }
    fn replace(expr: &mut Expr, name: &Name, terms: &mut Vec<Expr>) {
        if matches!(&expr.node, TypedExprNode::Var(n) if n == name) {
            *expr = terms.pop().expect("a term is built for each reference");
            return;
        }
        let mut shadowed = false;
        for_each_scoped_item_mut(expr, &mut |item| match item {
            ScopedItemMut::VarRef(_) | ScopedItemMut::KeyRef(_) => {}
            ScopedItemMut::Scope(binders) => shadowed = binders.iter().any(|b| b == name),
            ScopedItemMut::Child(child) if !shadowed => replace(child, name, terms),
            ScopedItemMut::Child(_) => {}
        });
    }
    let mut occurrences = 0;
    crate::ccl::ccl_utils::walk_refined_predicates(ty, &mut HashSet::new(), &mut |predicate, _| {
        occurrences += count(predicate, &name);
    });
    let mut terms: Vec<Expr> = (0..occurrences).map(|_| with()).collect();
    crate::ccl::ccl_utils::walk_refined_predicates_mut(
        ty,
        &crate::ccl::ccl_utils::PredMemo::new(),
        &(),
        &mut |predicate, _| {
            replace(predicate, &name, &mut terms);
            true
        },
    );
    debug_assert!(terms.is_empty(), "every term built is placed");
}

/// Record on each nominal type the module declares the module's type parameters and `const`
/// parameters it reaches ([`NominalDecl::implicit`], [`NominalDecl::implicit_consts`]): those
/// its constructors' parameter types name, those its associated functions reach (`reached`,
/// from [`associated_reach`]), and those each nominal type either names reaches,
/// transitively. Each type keeps the parameters in the order the module declares them, so
/// every instance lines its arguments up alike.
pub(super) fn settle_implicit(
    reached_by: &HashMap<String, AssociatedReach>,
    ctx: &LoweringContext,
) {
    let module_params = module_type_params(ctx);
    let module_consts = module_const_params(ctx);
    let is_module_const = |id: TypeParamId| module_consts.iter().any(|p| p.id == id);
    let decls = &ctx.nominal_types;
    let local = |d: &NominalDecl| {
        decls
            .iter()
            .position(|l| l.module == d.module && l.name == d.name)
    };
    // What each declaration names directly: the module's parameters, and the local
    // declarations whose parameters it reaches in turn.
    let mut reached: Vec<HashSet<TypeParamId>> = vec![HashSet::new(); decls.len()];
    let mut names: Vec<HashSet<usize>> = vec![HashSet::new(); decls.len()];
    // The `const` parameters each declaration reaches, by id, tracked as `reached` is.
    let mut consts: Vec<HashSet<TypeParamId>> = vec![HashSet::new(); decls.len()];
    let mut visit = |i: usize,
                     ty: &Type,
                     reached: &mut Vec<HashSet<TypeParamId>>,
                     consts: &mut Vec<HashSet<TypeParamId>>| {
        for name in crate::ccl::subst::type_free_vars(ty) {
            if let Some(param) = ctx.constants.param(name.base()) {
                consts[i].insert(param.id);
            }
        }
        each_param_and_decl(ty, &mut |found| match found {
            Found::Param(id) if module_params.iter().any(|p| p.id == id) => {
                reached[i].insert(id);
            }
            Found::Param(_) => {}
            Found::Decl(d) => match local(d) {
                Some(j) if j != i => {
                    names[i].insert(j);
                }
                Some(_) => {}
                None => {
                    for arg in d.implicit_args() {
                        each_param_and_decl(&arg, &mut |inner| {
                            if let Found::Param(id) = inner
                                && module_params.iter().any(|p| p.id == id)
                            {
                                reached[i].insert(id);
                            }
                        });
                    }
                    for arg in d.const_args() {
                        for param in arg.params() {
                            if is_module_const(param.id) {
                                consts[i].insert(param.id);
                            }
                        }
                    }
                }
            },
        });
    };
    for (i, decl) in decls.iter().enumerate() {
        for ctor in &decl.body().ctors {
            for (_, ty) in &ctor.params {
                visit(i, ty, &mut reached, &mut consts);
            }
        }
    }
    for function in &ctx.associated_functions {
        let (Some(i), Some(reach)) = (
            local(&function.decl),
            reached_by.get(&member_binding(&function.decl, &function.name)),
        ) else {
            continue;
        };
        for ty in &reach.types {
            visit(i, ty, &mut reached, &mut consts);
        }
        consts[i].extend(reach.consts.iter().copied());
    }
    loop {
        let mut changed = false;
        for i in 0..decls.len() {
            for j in names[i].clone() {
                let inherited: Vec<TypeParamId> = reached[j].iter().copied().collect();
                for id in inherited {
                    changed |= reached[i].insert(id);
                }
                let inherited: Vec<TypeParamId> = consts[j].iter().copied().collect();
                for id in inherited {
                    changed |= consts[i].insert(id);
                }
            }
        }
        if !changed {
            break;
        }
    }
    for ((decl, reached), consts) in decls.iter().zip(reached).zip(consts) {
        decl.set_implicit(
            module_params
                .iter()
                .filter(|p| reached.contains(&p.id))
                .cloned()
                .collect(),
        );
        decl.set_implicit_consts(
            module_consts
                .iter()
                .filter(|p| consts.contains(&p.id))
                .cloned()
                .collect(),
        );
    }
}

/// The `const` parameters of the module, in the order it declares them.
fn module_const_params(ctx: &LoweringContext) -> Vec<crate::ccl::constant::ConstParam> {
    let mut parameters: Vec<&super::modules::Parameter> = ctx.parameters.iter().collect();
    parameters.sort_by_key(|p| p.declared.start);
    parameters
        .iter()
        .filter_map(|p| Some(p.constant()?.param.clone()))
        .collect()
}

/// One error per associated function of the module that reaches, through the bindings and
/// functions of the module's top level, its state, a source, a value parameter without
/// `const`, a value member of a Module-typed parameter, or a member of a run the module
/// declares. Every import and run of a module shares a type that reaches no parameter, so
/// each copy of the type's functions must be the same function (`docs/chl-spec.md`,
/// "Associated functions and methods"). `chain` is the module's lowered top level.
///
/// With the errors, what each associated function reaches that joins its type's identity
/// ([`settle_implicit`]), by its binding.
pub(super) fn associated_reach(
    chain: &Expr,
    ctx: &LoweringContext,
) -> (Vec<LoweringError>, HashMap<String, AssociatedReach>) {
    let mut reached_by = HashMap::new();
    if ctx.associated_functions.is_empty() {
        return (Vec::new(), reached_by);
    }
    // A copy with every binder minted, so a reference reads the binder it resolves to.
    let chain = crate::ccl::uniquify::run_in(chain.clone_preserving_ids(), &HashMap::new(), None);
    let value_params: HashMap<&str, Option<TypeParamId>> = ctx
        .parameters
        .iter()
        .filter(|p| matches!(p.kind, super::modules::ParameterKind::Value { .. }))
        .map(|p| (p.name.as_str(), p.constant().map(|c| c.param.id)))
        .collect();
    let module_params: Vec<&str> = ctx
        .parameters
        .iter()
        .filter(|p| matches!(p.kind, super::modules::ParameterKind::Module { .. }))
        .map(|p| p.name.as_str())
        .collect();
    let mut top: HashMap<Name, TopLevel<'_>> = HashMap::new();
    let mut at = &chain;
    loop {
        match &at.node {
            TypedExprNode::MutDecl { binding, body, .. } => {
                top.insert(binding.name.clone(), TopLevel::Is(Forbidden::State));
                at = body;
            }
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                let base = binding.name.base();
                let kind = if let Some(constant) = value_params.get(base) {
                    match constant {
                        Some(id) => TopLevel::Const(*id),
                        None => TopLevel::Is(Forbidden::ValueParameter),
                    }
                } else if let Some(parameter) = module_params.iter().find(|p| {
                    base.strip_prefix(**p)
                        .is_some_and(|rest| rest.starts_with("::"))
                }) {
                    TopLevel::Is(Forbidden::ModuleParameter(parameter))
                } else if matches!(bound_expr.node, TypedExprNode::Defer) {
                    TopLevel::Is(Forbidden::Feed)
                } else {
                    TopLevel::Defined(binding, bound_expr)
                };
                top.insert(binding.name.clone(), kind);
                at = body;
            }
            TypedExprNode::DefGroup { bindings, body } => {
                for (binding, def) in bindings {
                    top.insert(binding.name.clone(), TopLevel::Defined(binding, def));
                }
                at = body;
            }
            TypedExprNode::ExprStmt { body, .. }
            | TypedExprNode::LetType { body, .. }
            | TypedExprNode::Run { body, .. } => at = body,
            _ => break,
        }
    }
    let runs: HashSet<&str> = ctx
        .module
        .qualifiers
        .iter()
        .filter(|(_, q)| q.kind == super::modules::QualifierKind::Run)
        .map(|(name, _)| name.as_str())
        .collect();
    let mut errors = Vec::new();
    for function in &ctx.associated_functions {
        let binding = member_binding(&function.decl, &function.name);
        let Some((_, TopLevel::Defined(typed, def))) =
            top.iter().find(|(name, _)| name.base() == binding)
        else {
            continue;
        };
        let mut seen: HashSet<Name> = HashSet::new();
        let mut through: Vec<String> = Vec::new();
        let mut reach = AssociatedReach::default();
        reach.definition(typed, def);
        let found = first_reached(def, &top, &runs, &mut seen, &mut through, &mut reach);
        reached_by.insert(binding.clone(), reach);
        if let Some((what, reached)) = found {
            let through = match through.as_slice() {
                [] => String::new(),
                path => format!(", through `{}`", path.join("` → `")),
            };
            errors.push(LoweringError::unsupported(
                function.span,
                format!(
                    "the associated function `{binding}` reads {}{through}; an associated \
                     function reaches no state, no source, and no value an import or a run \
                     gives its module other than a `const` parameter's, since every copy of \
                     the module shares the type",
                    reached.describe(&what)
                ),
            ));
        }
    }
    (errors, reached_by)
}

/// What an associated function reaches through its definition and the definitions it
/// follows, which joins its type's identity ([`associated_reach`]).
#[derive(Default)]
pub(super) struct AssociatedReach {
    /// The types of each definition followed, the function's own included: a type parameter
    /// or a `const` parameter one names is reached.
    types: Vec<Type>,
    /// Each `const` parameter read, by id.
    consts: HashSet<TypeParamId>,
}

impl AssociatedReach {
    /// Record the types `binding`, bound to `def`, carries: its own and each type in `def`.
    fn definition(&mut self, binding: &TypedBinding, def: &Expr) {
        self.types.push(binding.ty.clone());
        self.types.extend(binding.user_annotation.clone());
        for_each_type_in(def, &mut |ty| self.types.push(ty.clone()));
    }
}

/// A top-level binding, as [`associated_reach`] follows it.
enum TopLevel<'a> {
    /// A binding an associated function may not reach.
    Is(Forbidden<'a>),
    /// A `const` parameter, by id, which an associated function may reach.
    Const(TypeParamId),
    /// A value or a function whose definition is followed: its binding and its definition.
    Defined(&'a TypedBinding, &'a Expr),
}

/// What an associated function may not reach.
#[derive(Clone, Copy)]
enum Forbidden<'a> {
    State,
    Feed,
    Source,
    ValueParameter,
    /// A value member of the Module-typed parameter named.
    ModuleParameter(&'a str),
    /// A member of the run named, which the module declares.
    Run(&'a str),
}

impl Forbidden<'_> {
    /// How a diagnostic names `what`, which is one of these.
    fn describe(self, what: &str) -> String {
        match self {
            Forbidden::State => format!("`{what}`, a mutable variable of its module"),
            Forbidden::Feed => format!("`{what}`, a feed of its module"),
            Forbidden::Source => format!("the source `{what}`"),
            Forbidden::ValueParameter => {
                format!("`{what}`, a value parameter of its module without `const`")
            }
            Forbidden::ModuleParameter(p) => {
                format!("`{what}`, a member of the Module-typed parameter `{p}`")
            }
            Forbidden::Run(run) => format!("`{what}`, a member of the run `{run}`"),
        }
    }
}

/// The first thing `expr` reaches that an associated function may not, with how it is
/// spelled, following each top-level definition it reads once. `through` collects the
/// definitions followed on the way, and `reach` each definition's types and each `const`
/// parameter read.
fn first_reached<'a>(
    expr: &'a Expr,
    top: &'a HashMap<Name, TopLevel<'a>>,
    runs: &HashSet<&'a str>,
    seen: &mut HashSet<Name>,
    through: &mut Vec<String>,
    reach: &mut AssociatedReach,
) -> Option<(String, Forbidden<'a>)> {
    let read = match &expr.node {
        TypedExprNode::Source(name, _) => return Some((name.clone(), Forbidden::Source)),
        TypedExprNode::Var(name)
        | TypedExprNode::MutWrite { name, .. }
        | TypedExprNode::Feed { name, .. }
        | TypedExprNode::Define { name, .. } => Some(name),
        _ => None,
    };
    if let Some(name) = read {
        if name.is_raw()
            && let Some((qualifier, _)) = name.base().split_once("::")
            && let Some(run) = runs.get(qualifier)
        {
            return Some((name.base().to_string(), Forbidden::Run(run)));
        }
        match top.get(name) {
            Some(TopLevel::Is(reached)) => return Some((name.base().to_string(), *reached)),
            Some(TopLevel::Const(id)) => {
                reach.consts.insert(*id);
            }
            Some(TopLevel::Defined(binding, def)) if seen.insert(name.clone()) => {
                through.push(name.base().to_string());
                reach.definition(binding, def);
                if let Some(found) = first_reached(def, top, runs, seen, through, reach) {
                    return Some(found);
                }
                through.pop();
            }
            _ => {}
        }
    }
    let mut found = None;
    expr.walk_children(|child| {
        if found.is_none() {
            found = first_reached(child, top, runs, seen, through, reach);
        }
    });
    found
}

/// The type parameters at the module's top level, in the order it declares them: each
/// `param T`, then the abstract type members of each Module-typed parameter.
fn module_type_params(ctx: &LoweringContext) -> Vec<Rc<TypeParam>> {
    let mut parameters: Vec<&super::modules::Parameter> = ctx.parameters.iter().collect();
    parameters.sort_by_key(|p| p.declared.start);
    let mut params: Vec<Rc<TypeParam>> = parameters
        .iter()
        .filter_map(|p| match &p.kind {
            super::modules::ParameterKind::Type { param, .. } => Some(Rc::clone(param)),
            _ => None,
        })
        .collect();
    let mut viewed: Vec<(String, Rc<TypeParam>)> = Vec::new();
    for qualifier in ctx.module.qualifiers.values() {
        if qualifier.kind != super::modules::QualifierKind::Parameter {
            continue;
        }
        if let Some(view) = &qualifier.view {
            collect_view_params(&qualifier.name.to_string(), view, &mut viewed);
        }
    }
    viewed.sort_by(|a, b| a.0.cmp(&b.0));
    for (_, param) in viewed {
        if !params.iter().any(|p| p.id == param.id) {
            params.push(param);
        }
    }
    params
}

/// Each abstract type member of `view`, at every depth, spelled under `prefix`.
fn collect_view_params(
    prefix: &str,
    view: &super::modules::ModuleView,
    out: &mut Vec<(String, Rc<TypeParam>)>,
) {
    for (name, ty) in &view.types {
        if let Type::Param(param) = ty {
            out.push((format!("{prefix}::{name}"), Rc::clone(param)));
        }
    }
    for (name, inner) in &view.modules {
        collect_view_params(&format!("{prefix}::{name}"), inner, out);
    }
}

/// What [`each_param_and_decl`] finds in a type.
enum Found<'a> {
    Param(TypeParamId),
    Decl(&'a NominalDecl),
}

/// Call `f` on each type parameter and each nominal declaration `ty` names, at any depth.
fn each_param_and_decl<'a>(ty: &'a Type, f: &mut dyn FnMut(Found<'a>)) {
    match ty {
        Type::Param(param) => f(Found::Param(param.id)),
        Type::Nominal(decl, _) => f(Found::Decl(decl)),
        _ => {}
    }
    ty.walk_children(|child| each_param_and_decl(child, f));
}

/// Call `f` on every type `expr` carries at any depth: its nodes' type slots and its
/// binders' types.
fn for_each_type_in(expr: &Expr, f: &mut dyn FnMut(&Type)) {
    expr.walk_type_slots(&mut *f);
    expr.walk_binders(|b| {
        f(&b.ty);
        if let Some(annotation) = &b.user_annotation {
            f(annotation);
        }
    });
    expr.walk_children(|child| for_each_type_in(child, f));
}

/// Wrap `body` in the binding of each function the module's declarations declare: each
/// constructor that declares parameters, and the `extract` of a single-constructor form.
pub(super) fn bind_constructors(body: Expr, ctx: &mut LoweringContext) -> Expr {
    let decls = ctx.nominal_types.clone();
    // A declaration whose refinements read a `const` parameter has its functions bound
    // below the parameter's `let`, where the name is in scope.
    let (reading, closed): (Vec<_>, Vec<_>) = decls
        .iter()
        .map(|decl| (decl, const_params_read(decl, ctx)))
        .partition(|(_, read)| !read.is_empty());
    let read: HashSet<String> = reading
        .iter()
        .flat_map(|(_, read)| read.iter().cloned())
        .collect();
    let mut acc = body;
    if !read.is_empty() {
        acc = below_last_let(acc, &read, &mut |mut acc| {
            for (decl, _) in reading.iter().rev() {
                acc = bind_functions(decl, acc, ctx);
            }
            acc
        });
    }
    for (decl, _) in closed.iter().rev() {
        acc = bind_functions(decl, acc, ctx);
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

/// `acc` in the binding of each function `decl` declares: each constructor that declares
/// parameters, and the `extract` of a single-constructor form.
fn bind_functions(decl: &Rc<NominalDecl>, mut acc: Expr, ctx: &mut LoweringContext) -> Expr {
    if decl.declares_extract {
        acc = bind_extract(decl, acc, ctx);
    }
    for ctor in decl.body().ctors.iter().rev() {
        if !ctor.params.is_empty() {
            acc = bind_constructor(decl, ctor, acc, ctx);
        }
    }
    acc
}

/// The `const` parameters of the module that `decl`'s constructors' refinements read.
fn const_params_read(decl: &NominalDecl, ctx: &LoweringContext) -> HashSet<String> {
    let mut read = HashSet::new();
    for ctor in &decl.body().ctors {
        for (_, ty) in &ctor.params {
            for name in crate::ccl::subst::type_free_vars(ty) {
                if ctx.constants.param(name.base()).is_some() {
                    read.insert(name.base().to_string());
                }
            }
        }
    }
    read
}

/// `chain` with the body of the last `let` on its spine that binds one of `names` replaced
/// by `wrap` of it, or all of `chain` by `wrap` of it when none does.
fn below_last_let(
    mut chain: Expr,
    names: &HashSet<String>,
    wrap: &mut dyn FnMut(Expr) -> Expr,
) -> Expr {
    // How many spine steps down the last such `let` stands.
    let mut last = None;
    let mut at = &chain;
    let mut depth = 0;
    loop {
        if let TypedExprNode::Let { binding, .. } = &at.node
            && names.contains(binding.name.base())
        {
            last = Some(depth);
        }
        match super::modules::spine_body(at) {
            Some(rest) => at = rest,
            None => break,
        }
        depth += 1;
    }
    let Some(last) = last else {
        return wrap(chain);
    };
    let mut at = &mut chain;
    for _ in 0..=last {
        at = super::modules::spine_body_mut(at).expect("the spine is as deep as walked");
    }
    let taken = std::mem::take(at);
    *at = wrap(taken);
    chain
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

/// `Option::is_none`, the function `λ 𝑜 → match 𝑜 { Option::some(_) → false; Option::none →
/// true }` (`docs/chl-spec.md`, "Subscript and unwrap syntax \[Decided\]"). The interpreter
/// provides the same method (`BuiltinMethod::IsNone` in `chl-interp/src/eval.rs`).
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
                    ctor: tag.name().into(),
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
                    ctor: ctor.name.clone(),
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

/// A nominal type as the module being lowered names it.
pub(super) struct Named {
    pub decl: Rc<NominalDecl>,
    /// For another module's type: how this module spells the qualifier its members are
    /// reached through, `shop`, and its associated functions as that module's interface
    /// records them.
    foreign: Option<(
        crate::ccl::names::QualifiedName,
        HashMap<SmolStr, super::modules::AssociatedMember>,
    )>,
}

impl Named {
    /// The member named `name`, if the type declares one this module may name: another
    /// module's private associated function is an error.
    fn member(
        &self,
        name: &str,
        span: Span,
        ctx: &LoweringContext,
    ) -> Result<Member, LoweringError> {
        let decl = &self.decl;
        let found = match &self.foreign {
            None => member(decl, name, ctx).map(|(m, _)| m),
            Some((qualifier, functions)) => match functions.get(name) {
                Some(function) if !function.public => {
                    return Err(LoweringError::unsupported(
                        span,
                        format!(
                            "`{qualifier}::{}::{name}` is private to its module",
                            decl.name
                        ),
                    )
                    .with_related(function.declared, "declared here without `pub`"));
                }
                Some(function) => Some(Member::Associated {
                    arity: function.arity,
                }),
                None => member(decl, name, ctx)
                    .map(|(m, _)| m)
                    .filter(|m| !matches!(m, Member::Associated { .. })),
            },
        };
        found.ok_or_else(|| {
            LoweringError::unsupported(
                span,
                format!(
                    "`{}` declares no constructor or function `{name}`",
                    decl.name
                ),
            )
        })
    }

    /// The name a reference to the member `name` reads: the binding its module's chain
    /// binds, spelled through the qualifier for another module's type.
    fn reference(&self, name: &str, ctx: &mut LoweringContext) -> String {
        match &self.foreign {
            None => member_reference(&self.decl, name, ctx),
            Some((qualifier, _)) => {
                format!("{qualifier}::{}", member_binding(&self.decl, name))
            }
        }
    }
}

/// The nominal type `path` names, `Shape` or `shop::Shape`: one the module declares or the
/// compiler provides, or a public one of the module its qualifier names. `None` when that
/// module has errors of its own, which are reported where they stand.
pub(super) fn resolve_type(
    path: &[Spanned<SmolStr>],
    ctx: &LoweringContext,
) -> Result<Option<Named>, LoweringError> {
    let (ty, qualifier) = path.split_last().expect("a type path names its type");
    let Some(first) = qualifier.first() else {
        if !ctx.nominal_types.iter().any(|d| d.name == ty.node)
            && let Some((found, qualifier)) = ctx.used_nominal.get(&ty.node)
        {
            return Ok(Some(Named {
                decl: Rc::clone(&found.decl),
                foreign: Some((qualifier.clone(), found.functions.clone())),
            }));
        }
        return match ctx.nominal_type(&ty.node) {
            Some(decl) => Ok(Some(Named {
                decl,
                foreign: None,
            })),
            None => Err(LoweringError::unsupported(
                ty.span,
                format!("`{}` is not a nominal type this module declares", ty.node),
            )),
        };
    };
    let reached = ctx.qualifier_path(qualifier, first.span.join(ty.span))?;
    let spelled = crate::ccl::names::QualifiedName::of_segments(qualifier);
    Ok(reached
        .reach_nominal(&spelled, &ty.node, first.span.join(ty.span))?
        .map(|found| Named {
            decl: found.decl,
            foreign: Some((reached.name.clone(), found.functions)),
        }))
}

/// Whether `q` is a name qualified by a type, `Shape::circle` or `shop::Shape::circle`: a
/// member of a nominal type rather than of a module. A module's name is lowercase, so the
/// type is the qualifier's last segment and the only capitalized one (`docs/chl-spec.md`,
/// "9.6 Qualified references").
pub(super) fn names_a_type_member(q: &QualifiedName) -> bool {
    matches!(
        q.qualifier.split_last(),
        Some((ty, modules))
            if chl_parser::ast::is_type_name(&ty.node)
                && !modules.iter().any(|m| chl_parser::ast::is_type_name(&m.node))
    )
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

/// The type and member `q` names, `Shape::circle`, or `None` when the type's module has
/// errors of its own.
fn resolve_member(
    q: &QualifiedName,
    span: Span,
    ctx: &LoweringContext,
) -> Result<Option<(Named, Member)>, LoweringError> {
    let Some(named) = resolve_type(&q.qualifier, ctx).map_err(|e| {
        if q.qualifier.len() == 1 {
            let ty = &q.qualifier[0];
            LoweringError::unsupported(
                ty.span,
                format!(
                    "`{}` is not a nominal type this module declares, so `{}::{}` names nothing",
                    ty.node, ty.node, q.name.node
                ),
            )
        } else {
            e
        }
    })?
    else {
        return Ok(None);
    };
    let member = named.member(&q.name.node, span, ctx)?;
    Ok(Some((named, member)))
}

/// Lower a name qualified by a type, `Shape::circle`: the value a constructor without
/// parameters builds, or the function any other member is.
pub(super) fn lower_member(
    q: &QualifiedName,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let Some((named, member)) = resolve_member(q, span, ctx)? else {
        return Ok(Expr::error());
    };
    match member {
        Member::Constructor { arity: 0 } => {
            let unit = ctx.tag_machinery(Expr::lit(Lit::Unit), span, "lower.nominal_ctor_unit");
            Ok(Expr::nominal_ctor(named.decl, q.name.node.as_str(), unit))
        }
        _ => Ok(Expr::var(named.reference(&q.name.node, ctx))),
    }
}

/// Lower a call of a name qualified by a type, `Shape::circle(1)`.
pub(super) fn lower_member_call(
    q: &QualifiedName,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let Some((named, member)) = resolve_member(q, span, ctx)? else {
        return Ok(Expr::error());
    };
    let decl = &named.decl;
    let name = &q.name.node;
    match member.arity() {
        0 if matches!(member, Member::Constructor { .. }) => Err(LoweringError::unsupported(
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
            let binding = named.reference(name, ctx);
            super::exprs::lower_application(Name::raw(&binding), span, args, ctx)
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
    let ty = pattern
        .type_path
        .last()
        .expect("a constructor pattern names its type");
    let Some(named) = resolve_type(&pattern.type_path, ctx)? else {
        return Err(LoweringError::unsupported(
            ty.span,
            format!(
                "`{}`'s module has errors of its own, so its constructors are unknown",
                ty.node
            ),
        ));
    };
    let decl = named.decl;
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
            ctor: pattern.ctor.node.clone(),
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
    payload: &Name,
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
        super::functions::substitute_param_in_body(acc, &Name::raw(name.as_str()), &field, label)
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
    let receiver = params.first().filter(|p| p.name == "self");
    let is_method = receiver.is_some();
    if let Some(annotation) = receiver.and_then(|p| p.annotation.as_ref()) {
        check_self_annotation(&decl, name, annotation, def)?;
    }
    if let Some(first) = receiver
        && first.annotation.is_none()
        && !decl.params.is_empty()
        && block.is_none()
    {
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
        causes,
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
    let (func, annotation) = super::functions::lower_def(
        span,
        &all_type_params,
        &params,
        output,
        requires,
        causes,
        body,
        ctx,
    )?;
    Ok((member_binding(decl, name), func, annotation))
}

type QualifiedNameOf = crate::ccl::names::QualifiedName;

/// Each public type of another module, reached through a qualifier of the module being
/// lowered, that declares the public method `method`: its declaration, the parameters the
/// method takes after `self`, and how this module spells the qualifier. An import's
/// qualifier comes before a run's, since a run's name is in scope only below its statement,
/// and each declaration is reached once.
fn foreign_methods(
    method: &str,
    ctx: &LoweringContext,
) -> Vec<(Rc<NominalDecl>, usize, QualifiedNameOf)> {
    let mut qualifiers: Vec<&super::modules::Qualifier> = ctx
        .module
        .qualifiers
        .values()
        .filter(|q| q.view.is_none())
        .collect();
    qualifiers.sort_by_key(|q| (q.kind.sequential(), q.name.to_string()));
    let mut found: Vec<(Rc<NominalDecl>, usize, QualifiedNameOf)> = Vec::new();
    for qualifier in qualifiers {
        let Some(interface) = qualifier.reachable() else {
            continue;
        };
        let mut types: Vec<&super::modules::NominalMember> =
            interface.nominal.values().filter(|ty| ty.public).collect();
        types.sort_by(|a, b| a.decl.name.cmp(&b.decl.name));
        for ty in types {
            let params = match ty.functions.get(method) {
                Some(function) if function.public && function.is_method => function.arity - 1,
                Some(_) => continue,
                None if method == "extract" && ty.decl.declares_extract => 0,
                None => continue,
            };
            let decl = qualifier.instance(&ty.decl);
            if !found.iter().any(|(owner, _, _)| *owner == decl) {
                found.push((decl, params, qualifier.name.clone()));
            }
        }
    }
    found
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
    // The receiver lowers first, so an error in it is reported rather than a method no type
    // in reach declares.
    let receiver = super::lower_expr(receiver, ctx)?;
    // A receiver read from a module with errors of its own lowers to an error, which those
    // errors account for, so the call reports nothing more.
    if matches!(receiver.node, TypedExprNode::Error) {
        return Ok(receiver);
    }
    // Each type declaring the method, with the parameters the method takes after `self`, and
    // the qualifier its binding is spelled through when another module declares it.
    let mut owners: Vec<(Rc<NominalDecl>, usize, Option<QualifiedNameOf>)> = ctx
        .associated_functions
        .iter()
        .cloned()
        .chain(builtin_functions())
        .filter(|f| f.is_method && f.name == method.node)
        .map(|f| (Rc::clone(&f.decl), f.arity - 1, None))
        .collect();
    if method.node == "extract" {
        owners.extend(
            ctx.nominal_types
                .iter()
                .filter(|d| d.declares_extract)
                .map(|d| (Rc::clone(d), 0, None)),
        );
    }
    for (decl, params, qualifier) in foreign_methods(&method.node, ctx) {
        if !owners.iter().any(|(owner, _, _)| *owner == decl) {
            owners.push((decl, params, Some(qualifier)));
        }
    }
    // A type another module declares that no qualifier reaches has its method found by
    // inference, from the copies linking adds (`modules::add_method_copies`).
    if owners.is_empty() && !ctx.reached_methods.contains(&method.node) {
        return Err(LoweringError::unsupported(
            method.span,
            format!(
                "no type this module declares or reaches has a method `{0}`; the function a \
                 field holds is called as `(r.{0})(…)`",
                method.node
            ),
        ));
    }
    let candidates = owners
        .into_iter()
        .map(|(decl, params, qualifier)| {
            let binding = match qualifier {
                None => member_reference(&decl, &method.node, ctx),
                Some(qualifier) => {
                    format!("{qualifier}::{}", member_binding(&decl, &method.node))
                }
            };
            let reference = Expr::var(binding);
            let function = ctx.tag_image(reference, method.span);
            MethodCandidate {
                decl,
                params,
                function,
                copy: false,
            }
        })
        .collect();
    let placeholder = ctx.tag_image(
        Expr::new(TypedExprNode::Method {
            name: method.node.to_string(),
            args: args.len(),
            candidates,
        }),
        method.span,
    );
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
