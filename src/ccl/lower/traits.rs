//! Lowering of traits: a module's `trait` declarations and `impl Trait(…)` instances, and
//! the calls `Trait::f(c)` and the trait methods a method call may resolve to
//! (`docs/chl-spec.md`, "Declaring a trait"; `src/ccl/design/type-inference.md`, "Trait
//! functions").
//!
//! A call lowers to a [`TypedExprNode::TraitFn`], which inference types by the trait's
//! signature and coalescing replaces with the function of the instance its operands match.
//! A declared trait becomes a [`TraitDecl`], and a declared instance a row of the program's
//! [`InstanceTable`]. An instance's `def`s lower where its `impl` block stands, each bound
//! to the name its row records, and each completed from its trait's signature at the
//! instance's types.

use std::collections::HashMap;
use std::rc::Rc;

use smol_str::SmolStr;

use super::*;
use crate::ccl::infer::solver::traits::{
    Assoc, DeclaredAt, InstanceHead, InstanceTable, Signature, Trait, TraitDecl, TraitFunction,
    TraitInstance, entailed, replace_params, unify_all,
};
use crate::ccl::ty::{PolyParam, TraitRequirement, TypeKind, TypeParam, TypeParamId};
use crate::ccl::{Expr, Name, Type, TypedBinding, TypedExprNode};
use crate::chl_parser::ast::{
    AnnotationMode, Expr as ChlExpr, FunctionSignature, ImplBlock, Param, QualifiedName, Spanned,
    Stmt as ChlStmt, TraitDecl as ChlTraitDecl, TraitItem, TypeAnnotation,
};

/// The trait function `trait_::function`, its instance not yet chosen: one hole per operand
/// of the trait, which emission replaces with the obligation's operand variables.
pub(super) fn trait_function(
    trait_: &Trait,
    function: &str,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let operands = (0..trait_.arity()).map(|_| Type::Hole).collect();
    let node = Expr::new(TypedExprNode::TraitFn {
        trait_: trait_.clone(),
        function: function.into(),
        operands,
    });
    ctx.tag_image(node, span)
}

/// The trait method a name qualified by a nominal type names, `Circle::area` for the `area`
/// of `impl Area(Circle)`, where the type declares no member of that name: the trait, the
/// function, and the type, which the call's receiver must be (`docs/chl-spec.md`,
/// "Associated functions and methods").
pub(super) fn type_qualified_method(
    q: &QualifiedName,
    ctx: &LoweringContext,
) -> Option<(Trait, TraitFunction, Type)> {
    let [segment] = q.qualifier.as_slice() else {
        return None;
    };
    let decl = ctx.nominal_type(&segment.node)?;
    if nominal::member_span(&decl, &q.name.node, ctx).is_some() {
        return None;
    }
    let (_, _, trait_, _) = ctx.instance_methods.iter().find(|(head, m, _, _)| {
        *m == q.name.node
            && match head {
                InstanceHead::Nominal(d) => *d == decl,
                InstanceHead::Any => true,
                InstanceHead::Base(_) => false,
            }
    })?;
    let function = trait_.function(&q.name.node)?.clone();
    let receiver = Type::Nominal(Rc::clone(&decl), vec![Type::Hole; decl.params.len()]);
    Some((trait_.clone(), function, receiver))
}

/// `N::m`, a trait method named by the nominal type `receiver` its `self` must be: the trait
/// function with that operand stated.
pub(super) fn type_qualified_function(
    trait_: &Trait,
    function: &TraitFunction,
    receiver: Type,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let at = function
        .receiver
        .expect("a type's method is a trait function with `self`") as usize;
    let mut operands = vec![Type::Hole; trait_.arity()];
    operands[at] = receiver;
    let node = Expr::new(TypedExprNode::TraitFn {
        trait_: trait_.clone(),
        function: function.name.clone(),
        operands,
    });
    ctx.tag_image(node, span)
}

/// `N::m(x, a…)`: the trait method `N` has through an instance, applied with `x` an `N`.
pub(super) fn lower_type_qualified_call(
    (trait_, function, receiver): (Trait, TraitFunction, Type),
    q: &QualifiedName,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let arity = function.params_after_self + 1;
    if arity != args.len() {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{}` takes {arity} argument{}, got {}",
                q.qualifier[0].node,
                function.name,
                if arity == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    let callee = type_qualified_function(&trait_, &function, receiver, q.name.span, ctx);
    apply_to_arguments(callee, span, args, ctx)
}

/// The trait a name qualified by one capitalized segment names, `Area` in `Area::area`,
/// if that segment is a trait rather than a type.
pub(super) fn qualifying_trait(q: &QualifiedName, ctx: &LoweringContext) -> Option<Trait> {
    let [segment] = q.qualifier.as_slice() else {
        return None;
    };
    ctx.trait_named(&segment.node)
}

/// The function `trait_` declares by `q`'s name.
fn declared_function(trait_: &Trait, q: &QualifiedName) -> Result<TraitFunction, LoweringError> {
    trait_.function(&q.name.node).cloned().ok_or_else(|| {
        LoweringError::unsupported(
            q.name.span,
            format!("`{trait_}` declares no function `{}`", q.name.node),
        )
    })
}

/// `Trait::f`, the trait function as a value.
pub(super) fn lower_trait_member(
    trait_: Trait,
    q: &QualifiedName,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let declared = declared_function(&trait_, q)?;
    Ok(trait_function(&trait_, &declared.name, span, ctx))
}

/// `Trait::f(a…)`: the trait function applied to its arguments, `self` first for a method.
pub(super) fn lower_trait_member_call(
    trait_: Trait,
    q: &QualifiedName,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let declared = declared_function(&trait_, q)?;
    let arity = declared.params_after_self + usize::from(declared.receiver.is_some());
    if arity != args.len() {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{trait_}::{}` takes {arity} argument{}, got {}",
                declared.name,
                if arity == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    let function = trait_function(&trait_, &declared.name, q.name.span, ctx);
    apply_to_arguments(function, span, args, ctx)
}

/// `function` applied to `args`: to the one argument, or to the tuple of several, as every
/// call lowers.
pub(super) fn apply_to_arguments(
    function: Expr,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let argument = match args {
        [one] => lower_expr(one, ctx)?,
        several => {
            let parts = several
                .iter()
                .map(|a| lower_expr(a, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            let args_span = several
                .first()
                .zip(several.last())
                .map_or(span, |(first, last)| first.span.join(last.span));
            ctx.tag_machinery(Expr::tuple(parts), args_span, "lower.call_tuple")
        }
    };
    Ok(Expr::apply(argument, function))
}

/// The traits that declare a method `name`, with the method: the compiler's, then the
/// module's.
pub(super) fn methods_named(name: &str, ctx: &LoweringContext) -> Vec<(Trait, TraitFunction)> {
    let mut out = Vec::new();
    for t in Trait::compiler_traits().iter().chain(&ctx.traits) {
        if let Some(f) = t.function(name).filter(|f| f.receiver.is_some()) {
            out.push((t.clone(), f.clone()));
        }
    }
    out
}

/// What lowering keeps of an instance a module declares, for its `impl` block's `def`s,
/// which lower where the block stands.
pub(crate) struct InstanceBlock {
    /// The block's statement.
    pub span: Span,
    pub trait_: Trait,
    pub instance: Rc<TraitInstance>,
    /// The head's type variables by the names the head writes them with.
    pub variables: Vec<(SmolStr, Rc<TypeParam>)>,
}

fn trait_decls(stmts: &[Spanned<ChlStmt>]) -> impl Iterator<Item = &ChlTraitDecl> {
    stmts.iter().filter_map(|s| match &s.node {
        ChlStmt::TraitDecl(decl) => Some(decl),
        _ => None,
    })
}

/// Declare each `trait` among the module's top-level `stmts`, in source order, lowering its
/// functions' signatures (`docs/chl-spec.md`, "Declaring a trait"). A signature names the
/// traits declared above its own and the compiler's, so no declaration reaches itself.
pub(super) fn declare_traits(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for decl in trait_decls(stmts) {
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let declared = declare_trait(decl, ctx);
        ctx.type_params_in_scope.truncate(scoped);
        ctx.restore_type_aliases(aliases);
        match declared {
            Ok(trait_) => ctx.traits.push(trait_),
            Err(e) => errors.push(e),
        }
    }
    errors
}

/// Why `name` cannot name a trait, a trait's operand or an associated type the module
/// declares, if it cannot.
fn taken_type_name(name: &str, ctx: &LoweringContext) -> Option<String> {
    if let Some(what) = reserved_name(name) {
        return Some(format!(
            "`{name}` is a built-in {what} and cannot be given another meaning"
        ));
    }
    if ctx.nominal_type(name).is_some() {
        return Some(format!("`{name}` is a nominal type this module declares"));
    }
    if ctx.type_alias(name).is_some() {
        return Some(format!("`{name}` is a type alias this module declares"));
    }
    None
}

fn declare_trait(decl: &ChlTraitDecl, ctx: &mut LoweringContext) -> Result<Trait, LoweringError> {
    let name = &decl.name;
    if let Some(why) = taken_type_name(&name.node, ctx) {
        return Err(LoweringError::unsupported(name.span, why));
    }
    if let Some(first) = ctx.trait_named(&name.node).filter(|t| !t.is_compiler()) {
        return Err(LoweringError::unsupported(
            name.span,
            format!(
                "`{}` is declared twice in this module; a `trait` binds its name once",
                name.node
            ),
        )
        .with_related(first.span, "first declared here"));
    }
    // The operands and associated types are the type parameters every signature names.
    let mut names: Vec<&Spanned<SmolStr>> = Vec::new();
    let mut operands: Vec<Rc<TypeParam>> = Vec::new();
    let mut assocs: Vec<(Assoc, Rc<TypeParam>)> = Vec::new();
    let assoc_names = decl.items.iter().filter_map(|i| match i {
        TraitItem::AssocType(a) => Some(a),
        TraitItem::Function(_) => None,
    });
    for (n, is_operand) in decl
        .params
        .iter()
        .map(|p| (p, true))
        .chain(assoc_names.map(|a| (a, false)))
    {
        if let Some(why) = taken_type_name(&n.node, ctx) {
            return Err(LoweringError::unsupported(n.span, why));
        }
        if n.node == name.node {
            return Err(LoweringError::unsupported(
                n.span,
                format!(
                    "`{}` names the trait, and cannot name a type inside it",
                    n.node
                ),
            ));
        }
        if let Some(first) = names.iter().find(|m| m.node == n.node) {
            return Err(LoweringError::unsupported(
                n.span,
                format!("`{}` is declared twice in `trait {}`", n.node, name.node),
            )
            .with_related(first.span, "first declared here"));
        }
        names.push(n);
        let param = TypeParam::declared(n.node.clone());
        ctx.declare_type_alias(n.node.as_str(), Type::Param(Rc::clone(&param)));
        ctx.type_params_in_scope.push(n.node.to_string());
        if is_operand {
            operands.push(param);
        } else {
            assocs.push((Assoc::Declared(n.node.clone()), param));
        }
    }
    // What every instance requires of the trait's types: requirements of the traits declared
    // above it.
    let requires = lower_requirements(&decl.requires, ctx)?;
    let mut functions: Vec<TraitFunction> = Vec::new();
    let mut function_spans: Vec<Span> = Vec::new();
    for item in &decl.items {
        let TraitItem::Function(sig) = item else {
            continue;
        };
        if let Some(i) = functions.iter().position(|f| f.name == sig.node.name.node) {
            return Err(LoweringError::unsupported(
                sig.node.name.span,
                format!("`{}::{}` is declared twice", name.node, sig.node.name.node),
            )
            .with_related(function_spans[i], "first declared here"));
        }
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let function = declare_function(&name.node, &decl.params, &names, sig, ctx);
        ctx.type_params_in_scope.truncate(scoped);
        ctx.restore_type_aliases(aliases);
        functions.push(function?);
        function_spans.push(sig.span);
    }
    Ok(Trait::declared(TraitDecl {
        module: Vec::new(),
        name: name.node.clone(),
        span: name.span,
        operands,
        assocs,
        functions,
        requires,
        structural: false,
    }))
}

/// Lower one signature of `trait T(operands…)`, with its operands and associated types in
/// scope, `names` naming them all.
fn declare_function(
    trait_name: &str,
    operands: &[Spanned<SmolStr>],
    names: &[&Spanned<SmolStr>],
    sig: &Spanned<FunctionSignature>,
    ctx: &mut LoweringContext,
) -> Result<TraitFunction, LoweringError> {
    let FunctionSignature {
        name,
        type_params,
        params,
        output,
        requires,
    } = &sig.node;
    let qualified = format!("{trait_name}::{}", name.node);
    for tp in type_params {
        if let Some(clash) = names.iter().find(|n| n.node == tp.name) {
            return Err(LoweringError::unsupported(
                tp.name_span,
                format!(
                    "`{}` names a type of `trait {trait_name}`, and cannot name a type \
                     parameter of `{qualified}`",
                    tp.name
                ),
            )
            .with_related(clash.span, "declared here"));
        }
        if tp.annotation.is_some() {
            return Err(LoweringError::internal(
                tp.name_span,
                format!(
                    "type parameter `{}` of `{qualified}` has a kind or a bound; a trait \
                     function's type parameter takes neither yet",
                    tp.name
                ),
            ));
        }
    }
    let own = declare_type_params(type_params, ctx)?;
    if params.is_empty() {
        return Err(LoweringError::unsupported(
            sig.span,
            format!(
                "`{qualified}` declares no parameters; a function of no argument is a \
                 constant, and a trait's constant has no spelling yet"
            ),
        ));
    }
    let mut receiver = None;
    let mut inputs = Vec::with_capacity(params.len());
    for (i, p) in params.iter().enumerate() {
        let Some(annotation) = &p.annotation else {
            let what = if p.name == "self" {
                format!(
                    "`self` of `{qualified}` names the operand it is: `self: {}`",
                    operands.first().map_or("C", |o| o.node.as_str())
                )
            } else {
                format!(
                    "parameter `{}` of `{qualified}` has no type; a trait declares each \
                     parameter's type",
                    p.name
                )
            };
            return Err(LoweringError::unsupported(p.name_span, what));
        };
        if annotation.mode != AnnotationMode::Exact {
            return Err(LoweringError::unsupported(
                annotation.ty.span,
                format!(
                    "parameter `{}` of `{qualified}` is annotated with `<:`; a trait \
                     declares a parameter's type exactly, with `:`",
                    p.name
                ),
            ));
        }
        if p.name == "self" {
            if i != 0 {
                return Err(LoweringError::unsupported(
                    p.name_span,
                    format!("`self` of `{qualified}` is not its first parameter"),
                ));
            }
            let position = match &annotation.ty.node {
                ChlExpr::Name(n) => operands.iter().position(|o| o.node == *n),
                _ => None,
            };
            let Some(position) = position else {
                return Err(LoweringError::unsupported(
                    annotation.ty.span,
                    format!(
                        "`self` of `{qualified}` is annotated with one of the trait's \
                         operands, {}, which names the type the method is on",
                        operands
                            .iter()
                            .map(|o| format!("`{}`", o.node))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            };
            receiver = Some(position as u8);
        }
        inputs.push(signature_type(&annotation.ty, &qualified, ctx)?);
    }
    let Some(output) = output else {
        return Err(LoweringError::unsupported(
            name.span,
            format!("`{qualified}` declares no result type; write `=> T` after its parameters"),
        ));
    };
    let output = signature_type(output, &qualified, ctx)?;
    let requires = lower_requirements(requires, ctx)?;
    // A call opens the function's own type parameters afresh, so its arguments determine
    // each: it appears in a parameter's type, or is the associated type of a requirement on
    // types they determine.
    let mut determined = HashSet::new();
    for t in &inputs {
        collect_params(t, &mut determined);
    }
    loop {
        let before = determined.len();
        for r in &requires {
            let mut in_operands = HashSet::new();
            for a in &r.args {
                collect_params(a, &mut in_operands);
            }
            if in_operands.is_subset(&determined) {
                for (_, t) in &r.assoc {
                    collect_params(t, &mut determined);
                }
            }
        }
        if determined.len() == before {
            break;
        }
    }
    if let Some((tp, _)) = type_params
        .iter()
        .zip(&own)
        .find(|(_, p)| !determined.contains(&p.param.id))
    {
        return Err(LoweringError::unsupported(
            tp.name_span,
            format!(
                "type parameter `{}` of `{qualified}` appears in no parameter's type, so no \
                 call's arguments determine it",
                tp.name
            ),
        ));
    }
    Ok(TraitFunction {
        name: name.node.clone(),
        receiver,
        params_after_self: params.len() - usize::from(receiver.is_some()),
        signature: Signature {
            params: own.into_iter().map(|p| p.param).collect(),
            inputs,
            output,
            requires,
        },
    })
}

/// A type a trait's signature states, lowered.
///
/// A refinement is refused: every call would share its predicate's term, which inference
/// types once per use.
fn signature_type(
    annotation: &Spanned<ChlExpr>,
    qualified: &str,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let ty = lower_type_expr(annotation, ctx)?;
    if mentions_refinement(&ty) {
        return Err(LoweringError::internal(
            annotation.span,
            format!("a refinement in the signature of `{qualified}` is not supported yet"),
        ));
    }
    Ok(ty)
}

fn mentions_refinement(ty: &Type) -> bool {
    if matches!(ty, Type::Refinement(..)) {
        return true;
    }
    let mut found = false;
    ty.walk_children(|c| found |= mentions_refinement(c));
    found
}

/// Declare the instance each `impl` among the module's top-level `stmts` whose head names a
/// trait declares, checking it against its trait and the instances before it
/// (`docs/chl-spec.md`, "Declaring an instance").
pub(super) fn declare_instances(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for stmt in stmts {
        let ChlStmt::Impl(block) = &stmt.node else {
            continue;
        };
        let Some(trait_) = ctx.trait_named(&block.ty.node) else {
            continue;
        };
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let declared = declare_instance(trait_, block, stmt.span, ctx);
        ctx.type_params_in_scope.truncate(scoped);
        ctx.restore_type_aliases(aliases);
        if let Err(e) = declared {
            errors.push(e);
        }
    }
    errors
}

/// An instance's head, `Container(Bag(T), Elem=T)`, for diagnostics.
fn head_spelling(trait_: &Trait, operands: &[Type], assoc: &[(Assoc, Type)]) -> String {
    let mut parts: Vec<String> = operands
        .iter()
        .map(crate::ccl::chl_print::chl_type)
        .collect();
    parts.extend(
        assoc
            .iter()
            .map(|(n, t)| format!("{n}={}", crate::ccl::chl_print::chl_type(t))),
    );
    format!("{trait_}({})", parts.join(", "))
}

fn declare_instance(
    trait_: Trait,
    block: &ImplBlock,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    let written = format!("{trait_}(…)");
    if trait_.is_compiler() {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`{trait_}` is an operator's trait, which declares no function an instance \
                 could define; an instance of one is not supported yet"
            ),
        ));
    }
    if block.args.len() != trait_.arity() {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`{trait_}` is over {} type{}, and `impl {written}` names {}",
                trait_.arity(),
                if trait_.arity() == 1 { "" } else { "s" },
                block.args.len()
            ),
        ));
    }
    // The head's type variables, which `forall` declares.
    let mut variables: Vec<(SmolStr, Rc<TypeParam>)> = Vec::new();
    for v in &block.vars {
        if let Some(why) = taken_type_name(&v.node, ctx) {
            return Err(LoweringError::unsupported(v.span, why));
        }
        if variables.iter().any(|(n, _)| *n == v.node) {
            return Err(LoweringError::unsupported(
                v.span,
                format!("`{}` is declared twice in `impl forall (…)`", v.node),
            ));
        }
        variables.push((v.node.clone(), TypeParam::declared(v.node.clone())));
    }
    // The head's operands: each a base type, a nominal type applied to patterns, or a
    // type variable.
    let mut operands: Vec<Type> = Vec::new();
    let mut heads: Vec<InstanceHead> = Vec::new();
    for arg in &block.args {
        let ty = instance_pattern(arg, &written, &variables, ctx)?;
        heads.push(InstanceHead::of_pattern(&ty));
        operands.push(ty);
    }
    if !heads.iter().any(|h| matches!(h, InstanceHead::Nominal(_))) {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`impl {}` names no nominal type; an instance is for a type the module \
                 declares, so one of its operands names one",
                head_spelling(&trait_, &operands, &[])
            ),
        ));
    }
    // Each variable stands for a type a call's operands determine.
    for (v, (_, param)) in block.vars.iter().zip(&variables) {
        let mut named = HashSet::new();
        for o in &operands {
            collect_params(o, &mut named);
        }
        let named = named.contains(&param.id);
        if !named {
            return Err(LoweringError::unsupported(
                v.span,
                format!(
                    "type variable `{}` appears in no operand of `impl {}`, so no call's types \
                     determine it",
                    v.node,
                    head_spelling(&trait_, &operands, &[])
                ),
            ));
        }
    }
    for (name, param) in &variables {
        ctx.declare_type_alias(name.as_str(), Type::Param(Rc::clone(param)));
        ctx.type_params_in_scope.push(name.to_string());
    }
    // Every associated type the trait declares is fixed in the head, once.
    let mut assoc: Vec<(Assoc, Type)> = Vec::new();
    for a in &block.assoc {
        let Some(name) = trait_.assoc_named(&a.name) else {
            return Err(LoweringError::unsupported(
                a.name_span,
                format!("`{trait_}` associates no type named `{}`", a.name),
            ));
        };
        if assoc.iter().any(|(n, _)| *n == name) {
            return Err(LoweringError::unsupported(
                a.name_span,
                format!("`{}` is fixed twice in `impl {written}`", a.name),
            ));
        }
        let ty = lower_type_expr(&a.value, ctx)?;
        if mentions_refinement(&ty) {
            return Err(LoweringError::internal(
                a.value.span,
                format!(
                    "a refinement in the associated type `{}` of `impl {written}` is not \
                     supported yet",
                    a.name
                ),
            ));
        }
        assoc.push((name, ty));
    }
    if let Some(missing) = trait_
        .assocs()
        .into_iter()
        .find(|n| !assoc.iter().any(|(m, _)| m == n))
    {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`impl {}` does not fix `{missing}`; an instance fixes each associated type \
                 its trait declares in its head, `{missing}=T`",
                head_spelling(&trait_, &operands, &assoc)
            ),
        ));
    }
    let head = head_spelling(&trait_, &operands, &assoc);
    let requires = lower_requirements(&block.requires, ctx)?;
    // What the trait requires of every instance holds at this one's types, by the instances
    // declared above it and what this one requires.
    let stated = TraitRequirement {
        trait_: trait_.clone(),
        args: operands.clone(),
        assoc: assoc.clone(),
        at: None,
    };
    for needed in trait_.implied_by(&stated) {
        if !entailed(&needed, &requires, &ctx.instances) {
            let needed = head_spelling(&needed.trait_, &needed.args, &needed.assoc);
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`impl {head}` needs `{needed}`, which `{trait_}` requires of every \
                     instance; declare that instance above this one, or require it with \
                     `requires`"
                ),
            ));
        }
    }
    // No other instance accepts what this one does: two heads overlap exactly when some
    // types are an instance of both.
    let existing = ctx.instances.instances(&trait_);
    let overlaps = |i: &TraitInstance| unify_all(&i.operands, &operands);
    if let Some(other) = existing.iter().find(|i| overlaps(i)) {
        let error = LoweringError::unsupported(
            block.ty.span,
            format!(
                "`impl {head}` overlaps another instance of `{trait_}`; a trait has one \
                 instance for a type"
            ),
        );
        return Err(match &other.declared {
            Some(d) => error.with_related(d.span, "the other instance"),
            None => error,
        });
    }
    // The block defines each of the trait's functions, and nothing else.
    let mut functions: Vec<(SmolStr, Name)> = Vec::new();
    for def in &block.defs {
        let (fname, fspan, owner) = match &def.node {
            ChlStmt::FunctionDef { name, owner, .. } => (&name.node, def.span, owner),
            ChlStmt::Pub { .. } => {
                return Err(LoweringError::unsupported(
                    def.span,
                    format!(
                        "an instance's functions are its trait's, so `pub` does not mark one \
                         in `impl {head}`"
                    ),
                ));
            }
            _ => unreachable!("the parser builds an `impl` block of `def`s"),
        };
        if let Some(other) = owner {
            return Err(LoweringError::unsupported(
                other.span,
                format!(
                    "a `def` in `impl {head}` defines a function of `{trait_}` and names no \
                     type of its own; write `def {fname}(…)`"
                ),
            ));
        }
        if trait_.function(fname).is_none() {
            return Err(LoweringError::unsupported(
                fspan,
                format!("`{trait_}` declares no function `{fname}` for `impl {head}` to define"),
            ));
        }
        if functions.iter().any(|(n, _)| n == fname) {
            return Err(LoweringError::unsupported(
                fspan,
                format!("`impl {head}` defines `{fname}` twice"),
            ));
        }
        functions.push((fname.clone(), Name::fresh(format!("{trait_}::{fname}"))));
    }
    if let Some(missing) = trait_
        .functions()
        .iter()
        .find(|f| !functions.iter().any(|(n, _)| *n == f.name))
    {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`impl {head}` does not define `{}`, which `{trait_}` declares",
                missing.name
            ),
        ));
    }
    // A type's methods and the methods of its instances share one namespace: a nominal type's
    // own functions, and the methods each instance gives a nominal or a base type. A method
    // on a type variable standing as the whole operand is a blanket method, every type's.
    for f in trait_.functions() {
        let Some(pos) = f.receiver else {
            continue;
        };
        let receiver = &heads[pos as usize];
        let ty = match receiver {
            InstanceHead::Any => "every type".to_string(),
            other => format!("`{}`", crate::ccl::chl_print::chl_type(&other.as_type())),
        };
        let owners: Vec<Rc<crate::ccl::nominal::NominalDecl>> = match receiver {
            InstanceHead::Nominal(decl) => vec![Rc::clone(decl)],
            InstanceHead::Any => ctx
                .nominal_types
                .iter()
                .cloned()
                .chain(std::iter::once(crate::ccl::nominal::option()))
                .collect(),
            InstanceHead::Base(_) => Vec::new(),
        };
        if let Some((decl, first)) = owners
            .iter()
            .find_map(|d| nominal::member_span(d, &f.name, ctx).map(|at| (d, at)))
        {
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`impl {head}` gives `{}` a method `{}`, which `{}` already declares; a \
                     type's own functions and its instances' methods share one namespace",
                    decl.name, f.name, decl.name
                ),
            )
            .with_related(first, "declared here"));
        }
        if let Some((other, at)) = ctx
            .instance_methods
            .iter()
            .find(|(h, m, t, _)| {
                (h.admits(receiver) || receiver.admits(h)) && *m == f.name && *t != trait_
            })
            .map(|(_, _, t, at)| (t.clone(), *at))
        {
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`impl {head}` gives {ty} a method `{}`, which an instance of `{other}` \
                     gives it too; a type's methods share one namespace",
                    f.name
                ),
            )
            .with_related(at, "the other instance"));
        }
    }
    for f in trait_.functions() {
        if let Some(pos) = f.receiver {
            ctx.instance_methods.push((
                heads[pos as usize].clone(),
                f.name.clone(),
                trait_.clone(),
                block.ty.span,
            ));
        }
    }
    let instance = Rc::new(TraitInstance {
        params: variables.iter().map(|(_, p)| Rc::clone(p)).collect(),
        operands,
        heads,
        assoc,
        requires,
        functions,
        declared: Some(DeclaredAt {
            head,
            span: block.ty.span,
        }),
    });
    ctx.instances.add(trait_.clone(), Rc::clone(&instance));
    ctx.instance_blocks.push(InstanceBlock {
        span,
        trait_,
        instance,
        variables,
    });
    Ok(())
}

/// A pattern of an instance's head: a type variable, a base type, or a nominal type applied
/// to patterns (`docs/chl-spec.md`, "Declaring an instance").
fn instance_pattern(
    arg: &Spanned<ChlExpr>,
    head: &str,
    variables: &[(SmolStr, Rc<TypeParam>)],
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let refuse = || {
        LoweringError::unsupported(
            arg.span,
            format!(
                "`impl {head}` names a type that is not a type variable, a base type or a \
                 nominal type; an instance's head is built from those"
            ),
        )
    };
    let (name, args): (&SmolStr, &[Spanned<ChlExpr>]) = match &arg.node {
        ChlExpr::Name(n) => (n, &[]),
        ChlExpr::Call { func, args } => match &func.node {
            ChlExpr::Name(n) => (n, args.as_slice()),
            _ => return Err(refuse()),
        },
        _ => return Err(refuse()),
    };
    if args.is_empty()
        && let Some((_, param)) = variables.iter().find(|(n, _)| n == name)
    {
        return Ok(Type::Param(Rc::clone(param)));
    }
    if args.is_empty()
        && let Some(base) = crate::ccl::BaseType::from_keyword(name)
    {
        return Ok(Type::Base(base));
    }
    let Some(decl) = ctx.nominal_type(name) else {
        if name.starts_with(char::is_uppercase)
            && ctx.type_alias(name).is_none()
            && reserved_name(name).is_none()
        {
            return Err(LoweringError::unsupported(
                arg.span,
                format!(
                    "`{name}` is no type; a type variable of an instance is declared before its \
                     head, `impl forall ({name}) {head}`"
                ),
            ));
        }
        return Err(refuse());
    };
    if args.len() != decl.params.len() {
        return Err(LoweringError::unsupported(
            arg.span,
            format!(
                "`{}` takes {} type parameter{}, and `impl {head}` applies it to {}",
                decl.name,
                decl.params.len(),
                if decl.params.len() == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    let applied = args
        .iter()
        .map(|a| instance_pattern(a, head, variables, ctx))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Nominal(decl, applied))
}

/// The name an instance's completed signature types are bound to in its `def`'s alias
/// scope. `·` is no identifier's character, so no program names one.
fn signature_alias(i: usize) -> String {
    format!("Signature·{i}")
}

/// One `def` of an instance, lowered: the name its binding records, and its value and
/// annotation.
type InstanceDef = (Name, Expr, Option<Type>);

/// Lower the `def`s of an instance's `impl` block where it stands: each a binding, under
/// the name the instance's row records, wrapped around `body`. The functions reach each
/// other in any order, as a type's own `impl` block's do: inference binds each after the
/// functions of this instance its calls are answered by (`TypedExprNode::DefGroup`).
pub(super) fn lower_instance(
    block: &ImplBlock,
    span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let at = ctx
        .instance_blocks
        .iter()
        .position(|b| b.span == span)
        .expect("`declare_instances` declared every instance block");
    let (trait_, instance, variables) = {
        let b = &ctx.instance_blocks[at];
        (
            b.trait_.clone(),
            Rc::clone(&b.instance),
            b.variables.clone(),
        )
    };
    let mut lowered = Vec::new();
    for def in &block.defs {
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let result = lower_instance_def(&trait_, &instance, &variables, def, ctx);
        ctx.type_params_in_scope.truncate(scoped);
        ctx.restore_type_aliases(aliases);
        let (name, func, annotation) = result?;
        let binding = match annotation {
            Some(poly) => TypedBinding::new_annotated(name, poly),
            None => TypedBinding::new_unannotated(name),
        };
        lowered.push((binding, func));
    }
    Ok(ctx.tag_image(Expr::def_group(lowered, body), span))
}

/// Lower one `def` of an instance, its signature completed from its trait's at the
/// instance's types: an annotation it leaves out is the trait's, and one it writes must be
/// the trait's (`docs/chl-spec.md`, "Declaring an instance").
fn lower_instance_def(
    trait_: &Trait,
    instance: &TraitInstance,
    variables: &[(SmolStr, Rc<TypeParam>)],
    def: &Spanned<ChlStmt>,
    ctx: &mut LoweringContext,
) -> Result<InstanceDef, LoweringError> {
    let ChlStmt::FunctionDef {
        name,
        type_params,
        params,
        output,
        requires,
        body,
        ..
    } = &def.node
    else {
        unreachable!("`declare_instances` admitted only `def`s")
    };
    let name = &name.node;
    let function = trait_
        .function(name)
        .cloned()
        .expect("`declare_instances` checked the instance's functions");
    let binding = instance
        .functions
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, b)| b.clone())
        .expect("`declare_instances` named each function's binding");
    let qualified = format!("{trait_}::{name}");
    let sig = &function.signature;
    // The head's variables, then the function's own type parameters: the instance's
    // spelling of them, or the trait's where it writes none.
    let mut declared: Vec<PolyParam> = Vec::new();
    // A call determines the head's variables through the trait's operands, so only the
    // function's own type parameters have to be determined by its arguments.
    let mut spans: Vec<Option<Span>> = Vec::new();
    for (n, p) in variables {
        ctx.declare_type_alias(n.as_str(), Type::Param(Rc::clone(p)));
        ctx.type_params_in_scope.push(n.to_string());
        declared.push(PolyParam {
            param: Rc::clone(p),
            kind: TypeKind::Type,
            bound_at: None,
        });
        spans.push(None);
    }
    let own: Vec<Rc<TypeParam>> = if type_params.is_empty() {
        sig.params
            .iter()
            .map(|p| {
                let mine = TypeParam::declared(p.spelling.clone());
                ctx.declare_type_alias(p.spelling.as_str(), Type::Param(Rc::clone(&mine)));
                ctx.type_params_in_scope.push(p.spelling.to_string());
                spans.push(Some(def.span));
                mine
            })
            .collect()
    } else {
        if type_params.len() != sig.params.len() {
            return Err(LoweringError::unsupported(
                def.span,
                format!(
                    "`{name}` declares {} type parameter{}, and `{qualified}` declares {}",
                    type_params.len(),
                    if type_params.len() == 1 { "" } else { "s" },
                    sig.params.len()
                ),
            ));
        }
        if let Some(tp) = type_params.iter().find(|tp| tp.annotation.is_some()) {
            return Err(LoweringError::internal(
                tp.name_span,
                format!(
                    "type parameter `{}` of `{name}` has a kind or a bound; a trait \
                     function's type parameter takes neither yet",
                    tp.name
                ),
            ));
        }
        spans.extend(type_params.iter().map(|tp| Some(tp.name_span)));
        declare_type_params(type_params, ctx)?
            .into_iter()
            .map(|p| p.param)
            .collect()
    };
    declared.extend(own.iter().map(|p| PolyParam {
        param: Rc::clone(p),
        kind: TypeKind::Type,
        bound_at: None,
    }));
    // The trait's signature at the instance's types.
    let mut at_instance: HashMap<TypeParamId, Type> = HashMap::new();
    for (p, t) in trait_.operands.iter().zip(&instance.operands) {
        at_instance.insert(p.id, t.clone());
    }
    for (name, p) in &trait_.assocs {
        if let Some((_, t)) = instance.assoc.iter().find(|(n, _)| n == name) {
            at_instance.insert(p.id, t.clone());
        }
    }
    for (p, mine) in sig.params.iter().zip(&own) {
        at_instance.insert(p.id, Type::Param(Rc::clone(mine)));
    }
    let inputs: Vec<Type> = sig
        .inputs
        .iter()
        .map(|t| replace_params(t, &at_instance))
        .collect();
    let output_ty = replace_params(&sig.output, &at_instance);
    if params.len() != inputs.len() {
        return Err(LoweringError::unsupported(
            def.span,
            format!(
                "`{name}` declares {} parameter{}, and `{qualified}` declares {}",
                params.len(),
                if params.len() == 1 { "" } else { "s" },
                inputs.len()
            ),
        ));
    }
    let is_method = params.first().is_some_and(|p| p.name == "self");
    if is_method != function.receiver.is_some() {
        return Err(LoweringError::unsupported(
            def.span,
            if is_method {
                format!("`{qualified}` is not a method, so `{name}` takes no `self`")
            } else {
                format!("`{qualified}` is a method, so `{name}`'s first parameter is `self`")
            },
        ));
    }
    let mut params: Vec<Param> = params.clone();
    for (i, (p, stated)) in params.iter_mut().zip(&inputs).enumerate() {
        match &p.annotation {
            None => {
                let alias = signature_alias(i);
                ctx.declare_type_alias(alias.as_str(), stated.clone());
                p.annotation = Some(TypeAnnotation {
                    mode: AnnotationMode::Exact,
                    ty: Spanned::new(p.name_span, ChlExpr::Name(alias.into())),
                });
            }
            Some(written) => {
                let ty = lower_type_expr(&written.ty, ctx)?;
                if written.mode != AnnotationMode::Exact || ty != *stated {
                    return Err(LoweringError::unsupported(
                        written.ty.span,
                        format!(
                            "parameter `{}` of `{name}` is annotated `{}`, and `{qualified}` \
                             declares it `{}` at this instance",
                            p.name,
                            crate::ccl::chl_print::chl_type(&ty),
                            crate::ccl::chl_print::chl_type(stated)
                        ),
                    ));
                }
            }
        }
    }
    let output = match output {
        None => {
            let alias = signature_alias(inputs.len());
            ctx.declare_type_alias(alias.as_str(), output_ty);
            Spanned::new(def.span, ChlExpr::Name(alias.into()))
        }
        Some(written) => {
            let ty = lower_type_expr(written, ctx)?;
            if ty != output_ty {
                return Err(LoweringError::unsupported(
                    written.span,
                    format!(
                        "`{name}` returns `{}`, and `{qualified}` declares `{}` at this \
                         instance",
                        crate::ccl::chl_print::chl_type(&ty),
                        crate::ccl::chl_print::chl_type(&output_ty)
                    ),
                ));
            }
            written.clone()
        }
    };
    let stated_requires: Vec<Rc<TraitRequirement>> = sig
        .requires
        .iter()
        .map(|r| Rc::new(r.map_types(|t| replace_params(t, &at_instance))))
        .collect();
    let requires = if requires.is_empty() {
        stated_requires
    } else {
        let written = lower_requirements(requires, ctx)?;
        let same = written.len() == stated_requires.len()
            && written.iter().all(|w| stated_requires.contains(w));
        if !same {
            return Err(LoweringError::unsupported(
                requires[0].span,
                format!(
                    "`{name}`'s `requires` clause is not `{qualified}`'s at this instance; \
                     leave it out to take the trait's"
                ),
            ));
        }
        written
    };
    // What the instance requires of its variables holds wherever its functions run.
    let mut requires = requires;
    for r in &instance.requires {
        if !requires.contains(r) {
            requires.push(Rc::clone(r));
        }
    }
    let (func, annotation) = lower_def_declared(
        def.span,
        declared,
        &spans,
        &params,
        Some(&output),
        requires,
        body,
        ctx,
    )?;
    Ok((binding, func, annotation))
}

impl LoweringContext {
    /// The trait `name` names: the compiler's, or one the module declares.
    pub(super) fn trait_named(&self, name: &str) -> Option<Trait> {
        Trait::compiler_named(name)
            .or_else(|| self.traits.iter().find(|t| t.name() == name).cloned())
    }

    /// The program's instances, for inference; the context keeps none.
    pub(crate) fn take_instances(&mut self) -> InstanceTable {
        std::mem::take(&mut self.instances)
    }
}
