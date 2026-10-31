//! Lowering of traits: a module's `trait` declarations and `instance Trait(…)` instances, and
//! the functions read from an instance, `summon(Area(_))::area` and `a::area` under
//! `requires a: Area(S)` (`docs/chl-spec.md`, "Summoning an instance";
//! `src/ccl/design/type-inference.md`, "Trait functions").
//!
//! A function of an instance lowers to a [`TypedExprNode::TraitFn`] at the instance's types,
//! which inference types by the trait's signature and coalescing replaces with the function
//! of the instance its operands match.
//! A declared trait becomes a [`TraitDecl`], and a declared instance a row of the program's
//! [`InstanceTable`]. An instance's `def`s lower where its `instance` block stands, each bound
//! to the name its row records, and each completed from its trait's signature at the
//! instance's types.

use crate::ccl::lower::modules::{Qualifier, Reached, top_level_nominal_types, top_level_traits};
use crate::ccl::module_type::AliasType;
use std::collections::HashMap;
use std::rc::Rc;

use smol_str::SmolStr;

use super::*;
use crate::ccl::infer::solver::traits::{
    Assoc, DeclaredAt, Implementation, InstanceHead, InstanceTable, ProductReading, Signature,
    Trait, TraitDecl, TraitFunction, TraitInstance, compares_by_value, entailed, replace_params,
    unify_all,
};
use crate::ccl::nominal::WrittenOrder;
use crate::ccl::ty::{FieldKey, PolyParam, TraitRequirement, TypeKind, TypeParam, TypeParamId};
use crate::ccl::{Expr, Name, Type, TypedBinding, TypedExprNode};
use crate::chl_parser::ast::{
    AnnotationMode, Expr as ChlExpr, FunctionSignature, ImplBlock, Param, QualifiedName, Spanned,
    Stmt as ChlStmt, TraitDecl as ChlTraitDecl, TraitItem, TypeAnnotation,
};

/// Whether the first segment qualifying `q` names a requirement in scope, `a` in `a::area`
/// under `requires a: Area(S)`, which shadows a module of that name (`docs/chl-spec.md`,
/// "Summoning an instance").
pub(super) fn reads_named_requirement(q: &QualifiedName, ctx: &LoweringContext) -> bool {
    q.qualifier
        .first()
        .is_some_and(|segment| ctx.named_requirement(&segment.node).is_some())
}

/// The requirement `q`'s qualifier names, where [`reads_named_requirement`] holds. An instance
/// shows only its own trait's functions, so `r::s::f` is an error, though `s` names a
/// requirement of `r`'s trait (`docs/chl-spec.md`, "Declaring a trait").
pub(super) fn named_requirement(
    q: &QualifiedName,
    ctx: &LoweringContext,
) -> Result<Rc<TraitRequirement>, LoweringError> {
    let instance = ctx
        .named_requirement(&q.qualifier[0].node)
        .expect("`reads_named_requirement` holds of `q`");
    if let [first, second, ..] = q.qualifier.as_slice() {
        return Err(LoweringError::unsupported(
            first.span.join(second.span),
            format!(
                "`{}` is an instance of `{}`, which shows only the functions `{}` declares, so \
                 `{}::{}` names nothing",
                first.node, instance.trait_, instance.trait_, first.node, second.node
            ),
        ));
    }
    Ok(instance)
}

/// The refusal of `Trait::f`: a trait's functions are read from an instance
/// (`docs/chl-spec.md`, "Summoning an instance").
pub(super) fn refuse_trait_member(trait_: &Trait, q: &QualifiedName, span: Span) -> LoweringError {
    let holes = vec!["_"; trait_.arity()].join(", ");
    // The trait as the program wrote it, `shapes::Area` included.
    let written = crate::ccl::names::QualifiedName::of_segments(&q.qualifier);
    LoweringError::unsupported(
        span,
        format!(
            "a trait's functions are read from an instance, not from the trait: write \
             `summon({written}({holes}))::{}`",
            q.name.node
        ),
    )
}

/// The function `function` of `instance`, the instance not yet chosen: a [`TraitFn`] at the
/// instance's types, and the number of arguments the function takes.
///
/// [`TraitFn`]: TypedExprNode::TraitFn
fn instance_function(
    instance: &TraitRequirement,
    function: &Spanned<SmolStr>,
    ctx: &mut LoweringContext,
) -> Result<(Expr, usize), LoweringError> {
    let trait_ = &instance.trait_;
    let Some(declared) = trait_.function(&function.node) else {
        return Err(LoweringError::unsupported(
            function.span,
            format!("`{trait_}` declares no function `{}`", function.node),
        ));
    };
    // A summon of a trait no instance of which exists is refused here, as `requires`
    // refuses it: left to inference, it is an obligation with nothing to accept.
    if ctx.instances_declared
        && ctx.instances.instances(trait_).is_empty()
        && !trait_.collection_rule_admits(&instance.args, &instance.assoc)
    {
        return Err(unsatisfiable_requirement(
            trait_,
            &instance.args,
            instance.at.unwrap_or(function.span),
        ));
    }
    let arity = declared.signature.inputs.len();
    let node = Expr::new(TypedExprNode::TraitFn {
        trait_: trait_.clone(),
        function: declared.name.clone(),
        operands: instance.args.clone(),
        assoc: instance.assoc.clone(),
    });
    Ok((ctx.tag_image(node, function.span), arity))
}

/// `i::f`, the function of an instance as a value.
pub(super) fn lower_instance_member(
    instance: &TraitRequirement,
    function: &Spanned<SmolStr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    instance_function(instance, function, ctx).map(|(f, _)| f)
}

/// `i::f(a…)`: the function of an instance applied to its arguments.
pub(super) fn lower_instance_member_call(
    instance: &TraitRequirement,
    function: &Spanned<SmolStr>,
    span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let (f, arity) = instance_function(instance, function, ctx)?;
    if arity != args.len() {
        return Err(LoweringError::unsupported(
            span,
            format!(
                "`{}::{}` takes {arity} argument{}, got {}",
                instance.trait_,
                function.node,
                if arity == 1 { "" } else { "s" },
                args.len()
            ),
        ));
    }
    apply_to_arguments(f, span, args, ctx)
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

/// What lowering keeps of an instance a module declares, for its `instance` block's `def`s,
/// which lower where the block stands.
pub(crate) struct InstanceBlock {
    /// The block's statement.
    pub span: Span,
    pub trait_: Trait,
    pub instance: Rc<TraitInstance>,
    /// The head's type variables by the names the head writes them with.
    pub variables: Vec<(SmolStr, Rc<TypeParam>)>,
    /// The requirements the block's `requires` clause names.
    pub named: Vec<NamedRequirement>,
    /// The associated types of those requirements, each a type parameter of every function
    /// in the block, bounded as the clause bounds it.
    pub members: Vec<PolyParam>,
}

fn trait_decls(stmts: &[Spanned<ChlStmt>]) -> impl Iterator<Item = &ChlTraitDecl> {
    stmts.iter().filter_map(|s| match &s.node {
        ChlStmt::TraitDecl(decl) => Some(decl),
        ChlStmt::Pub { stmt, .. } => match &stmt.node {
            ChlStmt::TraitDecl(decl) => Some(decl),
            _ => None,
        },
        _ => None,
    })
}

/// One error per `pub trait` among `stmts`, a module's top level as written with its `pub`
/// marks, once it is lowered, whose functions' signatures or `requires` clause name a type or
/// a trait the module keeps private: an importer could name the trait and not what its
/// contract states (`docs/chl-spec.md`, "Traits and instances
/// across modules \[Decided\]").
pub(super) fn private_names_in_public_traits(
    stmts: &[Spanned<ChlStmt>],
    ctx: &LoweringContext,
) -> Vec<LoweringError> {
    let types = top_level_nominal_types(stmts);
    let private_type = |decl: &NominalDecl| {
        let local = |d: &Rc<NominalDecl>| d.module == decl.module && d.name == decl.name;
        types
            .iter()
            .find(|t| t.name == decl.name && ctx.nominal_types.iter().any(local))
            .filter(|t| !t.public)
            .map(|t| (decl.name.clone(), t.span))
    };
    let traits = top_level_traits(stmts);
    let private_trait = |trait_: &Trait| {
        traits
            .iter()
            .find(|t| t.name == trait_.name())
            .filter(|t| !t.public)
            .map(|t| (t.name.clone(), t.span))
    };
    let mut errors = Vec::new();
    for public in traits.iter().filter(|t| t.public) {
        let name = &public.name;
        let Some(trait_) = ctx.traits.iter().find(|t| t.name() == name) else {
            continue;
        };
        let mut named: Vec<Type> = Vec::new();
        let mut requires: Vec<&TraitRequirement> = trait_.requires.iter().map(|r| &**r).collect();
        for function in &trait_.functions {
            named.extend(function.signature.inputs.iter().cloned());
            named.push(function.signature.output.clone());
            requires.extend(function.signature.requires.iter().map(|r| &**r));
        }
        named.extend(trait_.assoc_bounds.iter().map(|(_, bound)| bound.clone()));
        for r in &requires {
            named.extend(r.args.iter().cloned());
        }
        let mut found = requires
            .iter()
            .filter(|r| ctx.traits.contains(&r.trait_))
            .find_map(|r| private_trait(&r.trait_));
        for ty in &named {
            if found.is_some() {
                break;
            }
            each_nominal(ty, &mut |decl| {
                if found.is_none() {
                    found = private_type(decl);
                }
            });
        }
        if let Some((private, declared)) = found {
            errors.push(
                LoweringError::unsupported(
                    public.span,
                    format!(
                        "`pub trait {name}` names `{private}`, which is private to this module; \
                         a public trait's functions and `requires` clause name only public types \
                         and traits"
                    ),
                )
                .with_related(declared, "declared here without `pub`"),
            );
        }
    }
    errors
}

/// Call `f` on each nominal type `ty` names, at any depth.
fn each_nominal(ty: &Type, f: &mut dyn FnMut(&NominalDecl)) {
    if let Type::Nominal(decl, ..) = ty {
        f(decl);
    }
    ty.walk_children(|child| each_nominal(child, f));
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
        ctx.end_type_params(scoped);
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
    if ctx.type_aliases.contains_key(name) {
        return Some(format!("`{name}` is a type alias this module declares"));
    }
    None
}

fn declare_trait(decl: &ChlTraitDecl, ctx: &mut LoweringContext) -> Result<Trait, LoweringError> {
    let name = &decl.name;
    if let Some(why) = taken_type_name(&name.node, ctx) {
        return Err(LoweringError::unsupported(name.span, why));
    }
    if let Some(first) = ctx.traits.iter().find(|t| t.name() == name.node) {
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
        TraitItem::AssocType { name, .. } => Some(name),
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
        ctx.declare_type_throughout(
            n.node.as_str(),
            AliasType::Type(Type::Param(Rc::clone(&param))),
        );
        ctx.type_params_in_scope.push(n.node.to_string());
        if is_operand {
            operands.push(param);
        } else {
            assocs.push((Assoc::Declared(n.node.clone()), param));
        }
    }
    // Each associated type's bound, written as a type parameter's kind is. It may name the
    // operands and the other associated types, all in scope by now, but not the type it
    // bounds.
    let mut assoc_bounds: Vec<(Assoc, Type)> = Vec::new();
    for item in &decl.items {
        let TraitItem::AssocType {
            name: n,
            bound: Some(bound),
        } = item
        else {
            continue;
        };
        let assoc = Assoc::Declared(n.node.clone());
        let lowered = lower_type_expr(bound, ctx)?;
        let own = assocs
            .iter()
            .find(|(a, _)| *a == assoc)
            .map(|(_, p)| p.id)
            .expect("every associated type has a parameter");
        let mut named = HashSet::new();
        collect_params(&lowered, &mut named);
        if named.contains(&own) {
            return Err(LoweringError::unsupported(
                bound.span,
                format!(
                    "the bound on `{}` names `{}` itself; a bound names the operands and the \
                     other associated types",
                    n.node, n.node
                ),
            ));
        }
        assoc_bounds.push((assoc, lowered));
    }
    // What every instance requires of the trait's types: requirements of the traits declared
    // above it.
    let (requires, named) = lower_named_requirements(&decl.requires, None, ctx)?;
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
        let function = declare_function(&name.node, &names, sig, ctx);
        ctx.end_type_params(scoped);
        ctx.restore_type_aliases(aliases);
        functions.push(function?);
        function_spans.push(sig.span);
    }
    // A trait is a member of its module, and the root's is at the empty path.
    let module = ctx
        .module
        .labels
        .as_ref()
        .map_or_else(Vec::new, |path| path.segments().to_vec());
    Ok(Trait::declared(TraitDecl {
        module,
        name: name.node.clone(),
        span: name.span,
        operands,
        assocs,
        assoc_bounds,
        functions,
        requires,
        named,
        products: ProductReading::None,
        reads_collections: false,
    }))
}

/// Make every data-function type in `ty` whose funkind is a hole a plain collection. An
/// instance's associated type is one type at every use, and a funkind hole is a fresh kind per
/// use, which a sum could pin after inference has read the instance
/// (`docs/chl-spec.md`, "6.3 Direction: collection types [Decided]").
fn close_kind_holes(ty: &mut Type) {
    if let Type::Fun { fun_kind, .. } = ty
        && matches!(fun_kind, crate::ccl::FunKind::Var(v) if v.is_hole())
    {
        *fun_kind = crate::ccl::FunKind::Data(None);
    }
    ty.walk_children_mut(close_kind_holes);
}

/// Lower one signature of `trait T(…)`, with its operands and associated types in scope,
/// `names` naming them all.
fn declare_function(
    trait_name: &str,
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
    // The requirements come first: a parameter's type and the result read the associated
    // types of the ones the clause names, `r::Output`.
    let mut members = Vec::new();
    let (requires, named) = lower_named_requirements(requires, Some(&mut members), ctx)?;
    if let Some(bounded) = members.iter().find(|m| m.bound_at.is_some()) {
        return Err(LoweringError::internal(
            bounded.bound_at.unwrap_or(sig.span),
            format!(
                "`{}` is bounded in the `requires` clause of `{qualified}`; a trait function's \
                 type parameters take no bound yet",
                bounded.param.spelling
            ),
        ));
    }
    let in_scope = ctx.named_requirements.len();
    ctx.named_requirements.extend(named);
    let typed = signature_types(params, output.as_ref(), &qualified, trait_name, name, ctx);
    ctx.named_requirements.truncate(in_scope);
    let (inputs, output) = typed?;
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
        signature: Signature {
            params: own.into_iter().chain(members).map(|p| p.param).collect(),
            inputs,
            output,
            requires,
        },
    })
}

/// The value parameters' types and the result type of the trait function `qualified`'s
/// signature ([`declare_function`]).
fn signature_types(
    params: &[Param],
    output: Option<&Spanned<ChlExpr>>,
    qualified: &str,
    trait_name: &str,
    name: &Spanned<SmolStr>,
    ctx: &mut LoweringContext,
) -> Result<(Vec<Type>, Type), LoweringError> {
    let mut inputs = Vec::with_capacity(params.len());
    for p in params {
        if p.name == "self" {
            return Err(LoweringError::unsupported(
                p.name_span,
                format!(
                    "a trait's function is no method, so no parameter of `{qualified}` is \
                     `self`; name it, as in `def area(s: S) => Int`, and read the function \
                     from an instance, as `summon({trait_name}(…))::{}`",
                    name.node
                ),
            ));
        }
        let Some(annotation) = &p.annotation else {
            return Err(LoweringError::unsupported(
                p.name_span,
                format!(
                    "parameter `{}` of `{qualified}` has no type; a trait declares each \
                     parameter's type",
                    p.name
                ),
            ));
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
        inputs.push(signature_type(&annotation.ty, qualified, ctx)?);
    }
    let Some(output) = output else {
        return Err(LoweringError::unsupported(
            name.span,
            format!("`{qualified}` declares no result type; write `=> T` after its parameters"),
        ));
    };
    let output = signature_type(output, qualified, ctx)?;
    Ok((inputs, output))
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

/// Declare the instance each `instance` block among the module's top-level `stmts`
/// declares, checking it against its trait and the instances before it
/// (`docs/chl-spec.md`, "Declaring an instance").
pub(super) fn declare_instances(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for stmt in stmts {
        let ChlStmt::Instance(block) = &stmt.node else {
            continue;
        };
        let trait_ = match ctx.block_trait(block) {
            Ok(Some(trait_)) => trait_,
            Ok(None) => {
                errors.push(LoweringError::unsupported(
                    block.ty.span,
                    format!(
                        "`instance {}` names no trait; an instance is of a trait the module \
                         declares, reaches, or the compiler's, and a type's own block is written \
                         `impl`",
                        block.ty.node
                    ),
                ));
                continue;
            }
            Err(e) => {
                // A qualified head naming a type of its module is the type's own block, as
                // an unqualified one is above.
                let names_a_type = !block.qualifier.is_empty()
                    && ctx
                        .qualifier_path(&block.qualifier, block.ty.span)
                        .is_ok_and(|at| at.declares_nominal(&block.ty.node));
                errors.push(if names_a_type {
                    LoweringError::unsupported(
                        block.ty.span,
                        format!(
                            "module `{}` declares no trait `{}`; a type's own block is written \
                             `impl`",
                            crate::ccl::names::QualifiedName::of_segments(&block.qualifier),
                            block.ty.node
                        ),
                    )
                } else {
                    e
                });
                continue;
            }
        };
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let declared = declare_instance(trait_, block, stmt.span, ctx);
        ctx.end_type_params(scoped);
        ctx.restore_type_aliases(aliases);
        if let Err(e) = declared {
            errors.push(e);
        }
    }
    errors
}

/// Whether `ty`, an instance's choice of an associated type, is below `bound`, the trait's bound
/// on it, as far as their forms decide: a function where `bound` is one of its kind, through the
/// domain by its kind's variance and the codomain; the base or nominal type `bound` is; a type
/// of the form `bound` has. A hole or a type variable on either side could be anything. A
/// refinement `bound` states is one `ty` must state, so an unrefined `ty` is below a refined
/// `bound` in no case.
fn may_be_below(ty: &Type, bound: &Type) -> bool {
    use crate::ccl::FunKind;
    if matches!(bound, Type::Refinement(..)) && !matches!(ty, Type::Refinement(..)) {
        return false;
    }
    let (ty, bound) = (ty.peel_refinements(), bound.peel_refinements());
    match (ty, bound) {
        (Type::Hole | Type::Param(_), _) | (_, Type::Hole | Type::Param(_)) => true,
        (
            Type::Fun {
                fun_kind: k0,
                domain: d0,
                codomain: c0,
                ..
            },
            Type::Fun {
                fun_kind: k1,
                domain: d1,
                codomain: c1,
                ..
            },
        ) => {
            // A compute function's domain is contravariant, and a data function's invariant
            // (`src/ccl/design/type-inference.md`, "Data domains are invariant").
            let data = |k: &FunKind| !matches!(k, FunKind::Compute);
            let domains = if data(k0) {
                may_be_below(d0, d1) && may_be_below(d1, d0)
            } else {
                may_be_below(d1, d0)
            };
            data(k0) == data(k1) && domains && may_be_below(c0, c1)
        }
        (Type::Base(a), Type::Base(b)) => a == b,
        (Type::Nominal(d, xs), Type::Nominal(e, ys)) => {
            d == e && xs.iter().zip(ys).all(|(x, y)| may_be_below(x, y))
        }
        // Two types of different forms: no value of one is a value of the other.
        (a, b) => std::mem::discriminant(a) == std::mem::discriminant(b),
    }
}

/// A trait at its operands, `Container(Bag(T))`, for diagnostics: an instance's head, or a
/// requirement.
fn head_spelling(trait_: &Trait, operands: &[Type]) -> String {
    let parts: Vec<String> = operands
        .iter()
        .map(crate::ccl::chl_print::chl_type)
        .collect();
    format!("{trait_}({})", parts.join(", "))
}

fn declare_instance(
    trait_: Trait,
    block: &ImplBlock,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    let written = format!("{trait_}(…)");
    if block.args.len() != trait_.arity() {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`{trait_}` is over {} type{}, and `instance {written}` names {}",
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
                format!("`{}` is declared twice in `instance forall (…)`", v.node),
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
                "`instance {}` names no nominal type; an instance is for a type the module \
                 declares, so one of its operands names one",
                head_spelling(&trait_, &operands)
            ),
        ));
    }
    // An instance is declared in its trait's module or in the module of a type its head
    // names, and outside its trait's module no operand is a whole type variable
    // (`docs/chl-spec.md`, "Traits and instances across modules [Decided]"). The compiler's
    // traits belong to no module, so an instance of one is always outside it.
    if !ctx.traits.contains(&trait_) {
        let whose = if trait_.is_compiler() {
            format!("`{trait_}` is the compiler's")
        } else {
            format!("`{trait_}` is module `{}`'s", trait_.module.join("::"))
        };
        let declares =
            |decl: &Rc<NominalDecl>| ctx.nominal_types.iter().any(|d| Rc::ptr_eq(d, decl));
        if !heads
            .iter()
            .any(|h| matches!(h, InstanceHead::Nominal(d) if declares(d)))
        {
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`instance {}` names no type this module declares; an instance is declared in \
                     its trait's module or in the module of a type its head names, and {whose}",
                    head_spelling(&trait_, &operands)
                ),
            ));
        }
        if let Some((arg, _)) = block
            .args
            .iter()
            .zip(&heads)
            .find(|(_, h)| matches!(h, InstanceHead::Any))
        {
            return Err(LoweringError::unsupported(
                arg.span,
                format!(
                    "`instance {}` has a type variable as a whole operand, which only an instance \
                     in its trait's module may, and {whose}; write an instance for each type",
                    head_spelling(&trait_, &operands)
                ),
            ));
        }
    }
    // A `**`'s exponent is a non-negative `Int` whichever instance answers it, so an instance
    // of `Exponentiable` takes `Int` there (`docs/chl-spec.md`, "Declaring an instance").
    if trait_ == Trait::exponentiable()
        && operands.get(1) != Some(&Type::Base(crate::ccl::BaseType::Int))
    {
        return Err(LoweringError::unsupported(
            block.args.get(1).map_or(block.ty.span, |a| a.span),
            format!(
                "`instance {}` takes an exponent that is not `Int`; a `**`'s exponent is a \
                 non-negative `Int` whichever instance answers it",
                head_spelling(&trait_, &operands)
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
                    "type variable `{}` appears in no operand of `instance {}`, so no call's types \
                     determine it",
                    v.node,
                    head_spelling(&trait_, &operands)
                ),
            ));
        }
    }
    for (name, param) in &variables {
        ctx.declare_type_throughout(
            name.as_str(),
            AliasType::Type(Type::Param(Rc::clone(param))),
        );
        ctx.type_params_in_scope.push(name.to_string());
    }
    // The block defines each associated type the trait declares, once.
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
                format!("`{}` is defined twice in `instance {written}`", a.name),
            ));
        }
        let mut ty = lower_type_expr(&a.value, ctx)?;
        close_kind_holes(&mut ty);
        if mentions_refinement(&ty) {
            return Err(LoweringError::internal(
                a.value.span,
                format!(
                    "a refinement in the associated type `{}` of `instance {written}` is not \
                     supported yet",
                    a.name
                ),
            ));
        }
        // A loop walks its source through one `elements` call to a structural collection,
        // so a nominal `Elements` would need a second instance's `elements` after it
        // (`docs/chl-spec.md`, "Trait requirements").
        if trait_ == Trait::iterable() && matches!(ty, Type::Nominal(..)) {
            return Err(LoweringError::unsupported(
                a.value.span,
                format!(
                    "`Elements = {ty}` in `instance {}` is a nominal type, and an `Elements` that \
                     is not a structural collection is not supported yet",
                    head_spelling(&trait_, &operands)
                ),
            ));
        }
        assoc.push((name, ty));
    }
    // An instance's choice is below the associated type's bound, at the instance's operands
    // and its other choices, which the bound may name. A type variable of the instance is
    // inference's question wherever the instance is used; a choice of another form than the
    // bound has no use that could satisfy it.
    let mut at: HashMap<TypeParamId, Type> = trait_
        .operand_params()
        .iter()
        .zip(&operands)
        .map(|(p, t)| (p.id, t.clone()))
        .collect();
    for (name, ty) in &assoc {
        if let Some(p) = trait_.assoc_param(name) {
            at.insert(p.id, ty.clone());
        }
    }
    for ((name, ty), a) in assoc.iter().zip(&block.assoc) {
        let Some(declared) = trait_.assoc_bound(name) else {
            continue;
        };
        let bound = replace_params(declared, &at);
        if !may_be_below(ty, &bound) {
            let chl = crate::ccl::chl_print::chl_type;
            let (declared, bound) = (chl(declared), chl(&bound));
            let here = if declared == bound {
                String::new()
            } else {
                format!(
                    ", which is `{name} <: {bound}` in `instance {}`",
                    head_spelling(&trait_, &operands)
                )
            };
            return Err(LoweringError::unsupported(
                a.value.span,
                format!(
                    "`{name}` is declared `{name} <: {declared}` in `trait {trait_}`{here}, and \
                     `{}` is not below `{bound}`",
                    chl(ty),
                ),
            ));
        }
    }
    if let Some(missing) = trait_
        .assocs()
        .into_iter()
        .find(|n| !assoc.iter().any(|(m, _)| m == n))
    {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`instance {}` does not define `{missing}`; an instance's block defines each \
                 associated type its trait declares, `{missing} = T`",
                head_spelling(&trait_, &operands)
            ),
        ));
    }
    let head = head_spelling(&trait_, &operands);
    let mut members: Vec<PolyParam> = Vec::new();
    let (requires, named) = lower_named_requirements(&block.requires, Some(&mut members), ctx)?;
    // The instance's functions read the requirements the trait names and those the block
    // names, by one set of names.
    if let Some((name, r)) = named
        .iter()
        .find(|(n, _)| trait_.named.iter().any(|(m, _)| m == n))
    {
        return Err(LoweringError::unsupported(
            r.at.unwrap_or(block.ty.span),
            format!(
                "`{name}` names a requirement of `{trait_}`, which the functions of \
                 `instance {head}` read by that name; name this one otherwise"
            ),
        ));
    }
    check_conditions_end(&trait_, &operands, &requires, &head, block, ctx)?;
    if trait_ == Trait::equatable() || trait_ == Trait::orderable() {
        check_comparison_instance(&trait_, &operands, &requires, &head, block, &ctx.instances)?;
    }
    // What the trait requires of every instance holds at this one's types, by the instances
    // declared above it and what this one requires.
    for needed in trait_.requirements_at(&operands, &assoc) {
        if !entailed(&needed, &requires, &ctx.instances) {
            let needed = head_spelling(&needed.trait_, &needed.args);
            return Err(LoweringError::unsupported(
                block.ty.span,
                format!(
                    "`instance {head}` needs `{needed}`, which `{trait_}` requires of every \
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
                "`instance {head}` overlaps another instance of `{trait_}`; a trait has one \
                 instance for a type"
            ),
        );
        return Err(match &other.declared {
            Some(d) => error.with_related(d.span, "the other instance"),
            None => error,
        });
    }
    // The block defines each of the trait's functions, and nothing else.
    let mut functions: Vec<(SmolStr, Implementation)> = Vec::new();
    for def in &block.defs {
        let (fname, fspan, owner) = match &def.node {
            ChlStmt::FunctionDef { name, owner, .. } => (&name.node, def.span, owner),
            ChlStmt::Pub { .. } => {
                return Err(LoweringError::unsupported(
                    def.span,
                    format!(
                        "an instance's functions are its trait's, so `pub` does not mark one \
                         in `instance {head}`"
                    ),
                ));
            }
            _ => unreachable!("the parser builds an `instance` block of `def`s"),
        };
        if let Some(other) = owner {
            return Err(LoweringError::unsupported(
                other.span,
                format!(
                    "a `def` in `instance {head}` defines a function of `{trait_}` and names no \
                     type of its own; write `def {fname}(…)`"
                ),
            ));
        }
        if trait_.function(fname).is_none() {
            return Err(LoweringError::unsupported(
                fspan,
                format!(
                    "`{trait_}` declares no function `{fname}` for `instance {head}` to define"
                ),
            ));
        }
        if functions.iter().any(|(n, _)| n == fname) {
            return Err(LoweringError::unsupported(
                fspan,
                format!("`instance {head}` defines `{fname}` twice"),
            ));
        }
        functions.push((
            fname.clone(),
            Implementation::Binding(Name::fresh(format!("{trait_}::{fname}"))),
        ));
    }
    if let Some(missing) = trait_
        .functions()
        .iter()
        .find(|f| !functions.iter().any(|(n, _)| *n == f.name))
    {
        return Err(LoweringError::unsupported(
            block.ty.span,
            format!(
                "`instance {head}` does not define `{}`, which `{trait_}` declares",
                missing.name
            ),
        ));
    }
    let instance = Rc::new(TraitInstance {
        params: variables
            .iter()
            .map(|(_, p)| Rc::clone(p))
            .chain(members.iter().map(|m| Rc::clone(&m.param)))
            .collect(),
        operands,
        heads,
        assoc,
        requires,
        bounds: members
            .iter()
            .filter_map(|m| m.bound().map(|b| (Rc::clone(&m.param), b.clone())))
            .collect(),
        functions,
        declared: Some(DeclaredAt {
            module: ctx
                .module
                .labels
                .as_ref()
                .map_or_else(Vec::new, |path| path.segments().to_vec()),
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
        named,
        members,
    });
    Ok(())
}

/// Check that resolving an instance's conditions ends (`docs/chl-spec.md`, "Declaring an
/// instance"): each condition is no deeper than the head, and one on a trait not declared
/// before the instance's is shallower (`src/ccl/design/type-inference.md`, "An instance's
/// conditions end").
///
/// `requires` holds what the instance's clause states, and selecting the instance mints an
/// obligation for each, so each is checked.
fn check_conditions_end(
    trait_: &Trait,
    operands: &[Type],
    requires: &[Rc<TraitRequirement>],
    head: &str,
    block: &ImplBlock,
    ctx: &LoweringContext,
) -> Result<(), LoweringError> {
    let head_depth = operands.iter().map(depth).max().unwrap_or(0);
    let mut head_variables = HashMap::new();
    for o in operands {
        variable_depths(o, 0, &mut head_variables);
    }
    for r in requires {
        let shrinks = !declared_before(&r.trait_, trait_, ctx);
        let mut variables = HashMap::new();
        let mut written = None;
        for a in &r.args {
            variable_depths(a, 0, &mut variables);
            written = written.max(deepest_written_leaf(a, 0));
        }
        let fits = |at: usize, bound: usize| if shrinks { at < bound } else { at <= bound };
        let deeper = written.is_some_and(|at| at > head_depth)
            || variables.iter().any(|(v, at)| {
                let bound = head_variables
                    .get(v)
                    .expect("an instance's type variables each appear in its head");
                at > bound
            });
        let ends = !deeper
            && written.is_none_or(|at| fits(at, head_depth))
            && variables.iter().all(|(v, at)| fits(*at, head_variables[v]));
        if ends {
            continue;
        }
        let condition = head_spelling(&r.trait_, &r.args);
        let why = if deeper {
            "a condition is no deeper than the instance's head".to_string()
        } else if r.trait_ == *trait_ {
            format!("a condition on `{trait_}` itself is shallower than the instance's head")
        } else {
            format!(
                "a condition on `{}`, which is not declared above `{trait_}`, is shallower than \
                 the instance's head",
                r.trait_
            )
        };
        return Err(LoweringError::unsupported(
            r.at.unwrap_or(block.ty.span),
            format!(
                "`instance {head}` requires `{condition}`, which is {} the head; {why}, so resolving \
                 an instance's conditions ends",
                if deeper {
                    "deeper than"
                } else {
                    "not shallower than"
                },
            ),
        ));
    }
    Ok(())
}

/// Whether the trait `earlier` is declared before `later`, the order an instance's conditions
/// may descend without shrinking: the compiler's traits before a module's, and a module's in the
/// order it declares them. Two compiler traits are unordered.
fn declared_before(earlier: &Trait, later: &Trait, ctx: &LoweringContext) -> bool {
    match (earlier.is_compiler(), later.is_compiler()) {
        (true, false) => true,
        (false, false) => {
            let at = |t: &Trait| ctx.traits.iter().position(|d| d == t);
            matches!((at(earlier), at(later)), (Some(e), Some(l)) if e < l)
        }
        (_, true) => false,
    }
}

/// How deep `ty` nests: `0` for a type with no parts, as `Int` and a type variable are, and one
/// more than its deepest part otherwise.
fn depth(ty: &Type) -> usize {
    let mut deepest: Option<usize> = None;
    ty.peel_refinements()
        .walk_children(|c| deepest = Some(deepest.map_or(depth(c), |d| d.max(depth(c)))));
    deepest.map_or(0, |d| d + 1)
}

/// The deepest place each type variable stands in `ty`, which stands at depth `at`.
fn variable_depths(ty: &Type, at: usize, out: &mut HashMap<TypeParamId, usize>) {
    let ty = ty.peel_refinements();
    if let Type::Param(p) = ty {
        let deepest = out.entry(p.id).or_insert(at);
        *deepest = (*deepest).max(at);
        return;
    }
    ty.walk_children(|c| variable_depths(c, at + 1, out));
}

/// The deepest place a part of `ty` with no parts stands, other than a type variable, where
/// `ty` stands at depth `at`: `None` where every such part is a type variable.
fn deepest_written_leaf(ty: &Type, at: usize) -> Option<usize> {
    let ty = ty.peel_refinements();
    if matches!(ty, Type::Param(_)) {
        return None;
    }
    let mut deepest = None;
    let mut leaf = true;
    ty.walk_children(|c| {
        leaf = false;
        deepest = deepest.max(deepest_written_leaf(c, at + 1));
    });
    if leaf { Some(at) } else { deepest }
}

/// Check an instance of `Equatable` or `Orderable`, which compare by value
/// (`docs/chl-spec.md`, "Equality and order"): the head names one nominal type twice, and
/// each of its constructors' arguments compares by value, there and in order.
fn check_comparison_instance(
    trait_: &Trait,
    operands: &[Type],
    requires: &[Rc<TraitRequirement>],
    head: &str,
    block: &ImplBlock,
    instances: &InstanceTable,
) -> Result<(), LoweringError> {
    let refuse = |message: String| Err(LoweringError::unsupported(block.ty.span, message));
    let [one, other] = operands else {
        unreachable!("`{trait_}` is over two types")
    };
    if one != other {
        return refuse(format!(
            "`instance {head}` relates two different types; a comparison is by value, so an \
             instance of `{trait_}` names one type twice"
        ));
    }
    let Type::Nominal(decl, args) = one else {
        unreachable!("an instance's head names a nominal type, and this one names one type")
    };
    let ctors = &decl.body().ctors;
    let orderable = *trait_ == Trait::orderable();
    if orderable && ctors.len() != 1 {
        return refuse(format!(
            "`instance {head}`: `{}` has {} constructors, which have no order; only a type with \
             one constructor is orderable",
            decl.name,
            ctors.len()
        ));
    }
    for ctor in ctors {
        // A constructor with no parameters holds nothing to compare: its value is its name.
        if ctor.params.is_empty() {
            continue;
        }
        let payload = decl.instantiate(
            &crate::ccl::ccl_utils::strip_refinements(&ctor.payload()),
            args,
        );
        if orderable && !ctor.payload_order().is_ordered() {
            return refuse(format!(
                "`instance {head}`: `{}::{}`'s argument holds a record its declaration does not \
                 write, whose fields have no order; write the record in `{}`'s declaration",
                decl.name, ctor.name, decl.name
            ));
        }
        if !compares_as_written(trait_, &payload, &ctor.payload_order(), requires, instances) {
            return refuse(format!(
                "`instance {head}`: `{}::{}`'s argument is `{}`, which is not `{trait_}`; a \
                 nominal type compares by its constructor's argument",
                decl.name,
                ctor.name,
                crate::ccl::chl_print::chl_type(&payload)
            ));
        }
    }
    Ok(())
}

/// Whether values of `ty`, a constructor's argument ordered as its declaration writes it,
/// `order`, compare by value under `trait_`: each product the declaration writes by its
/// components, a record among them in the order its fields are written, and every other type
/// as [`compares_by_value`] reads it, where a record has no order.
fn compares_as_written(
    trait_: &Trait,
    ty: &Type,
    order: &WrittenOrder,
    requires: &[Rc<TraitRequirement>],
    instances: &InstanceTable,
) -> bool {
    let each = |t: &Type, o: &WrittenOrder| compares_as_written(trait_, t, o, requires, instances);
    match (order, ty.peel_refinements()) {
        (WrittenOrder::Fields(fields), Type::Record(types)) => fields.iter().all(|(key, o)| {
            types
                .iter()
                .find(|(n, _)| matches!(key, FieldKey::Name(k) if k == n))
                .is_some_and(|(_, t)| each(t, o))
        }),
        (WrittenOrder::Fields(fields), Type::Tuple(elems)) if fields.len() == elems.len() => {
            fields.iter().zip(elems).all(|((_, o), t)| each(t, o))
        }
        _ => compares_by_value(trait_, ty, requires, instances),
    }
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
                "`instance {head}` names a type that is not a type variable, a base type or a \
                 nominal type; an instance's head is built from those"
            ),
        )
    };
    // Another module's type, `shapes::Circle`, is named through its qualifier.
    let qualified = |q: &QualifiedName, span: Span, ctx: &LoweringContext| {
        qualified_nominal(q, span, ctx)?.ok_or_else(|| {
            LoweringError::unsupported(
                span,
                format!(
                    "`{}` names no nominal type; `instance {head}` names a type variable, a base \
                     type or a nominal type at each operand",
                    crate::ccl::names::QualifiedName::of(q)
                ),
            )
        })
    };
    let (name, args): (&SmolStr, &[Spanned<ChlExpr>]) = match &arg.node {
        ChlExpr::Name(n) => (n, &[]),
        ChlExpr::Qualified(q) => {
            let decl = qualified(q, arg.span, ctx)?;
            return applied_pattern(arg, decl, &[], head, variables, ctx);
        }
        ChlExpr::Call { func, args } => match &func.node {
            ChlExpr::Name(n) => (n, args.as_slice()),
            ChlExpr::Qualified(q) => {
                let decl = qualified(q, func.span, ctx)?;
                return applied_pattern(arg, decl, args, head, variables, ctx);
            }
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
            && matches!(ctx.type_alias(name, arg.span), AliasAt::Undeclared)
            && reserved_name(name).is_none()
        {
            return Err(LoweringError::unsupported(
                arg.span,
                format!(
                    "`{name}` is no type; a type variable of an instance is declared before its \
                     head, `instance forall ({name}) {head}`"
                ),
            ));
        }
        return Err(refuse());
    };
    applied_pattern(arg, decl, args, head, variables, ctx)
}

/// The nominal type `decl` applied to the patterns `args` write, `Two(T)`, as an instance's
/// head names it at `arg`.
fn applied_pattern(
    arg: &Spanned<ChlExpr>,
    decl: Rc<NominalDecl>,
    args: &[Spanned<ChlExpr>],
    head: &str,
    variables: &[(SmolStr, Rc<TypeParam>)],
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    if args.len() != decl.params.len() {
        return Err(LoweringError::unsupported(
            arg.span,
            format!(
                "`{}` takes {} type parameter{}, and `instance {head}` applies it to {}",
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

/// Lower the `def`s of an `instance` block where it stands: each a binding, under
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
    let (trait_, instance, variables, named, members) = {
        let b = &ctx.instance_blocks[at];
        (
            b.trait_.clone(),
            Rc::clone(&b.instance),
            b.variables.clone(),
            b.named.clone(),
            b.members.clone(),
        )
    };
    let mut lowered = Vec::new();
    for def in &block.defs {
        let aliases = ctx.snapshot_type_aliases();
        let scoped = ctx.type_params_in_scope.len();
        let in_scope = ctx.named_requirements.len();
        let result = lower_instance_def(&trait_, &instance, &variables, &named, &members, def, ctx);
        ctx.named_requirements.truncate(in_scope);
        ctx.end_type_params(scoped);
        ctx.restore_type_aliases(aliases);
        let (name, func, annotation) = result?;
        let binding = match annotation {
            Some(poly) => TypedBinding::new_annotated(name, poly),
            None => TypedBinding::new_unannotated(name),
        };
        lowered.push((binding, func));
    }
    // An instance of a trait that declares no function binds nothing.
    if lowered.is_empty() {
        return Ok(body);
    }
    Ok(ctx.tag_image(Expr::def_group(lowered, body), span))
}

/// Lower one `def` of an instance, its signature completed from its trait's at the
/// instance's types: an annotation it leaves out is the trait's, and one it writes must be
/// the trait's (`docs/chl-spec.md`, "Declaring an instance"). Its body reads the
/// requirements the trait names, at the instance's types, and those the instance names.
fn lower_instance_def(
    trait_: &Trait,
    instance: &TraitInstance,
    variables: &[(SmolStr, Rc<TypeParam>)],
    named: &[NamedRequirement],
    members: &[PolyParam],
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
    let Some(Implementation::Binding(binding)) = instance.implementation(name).cloned() else {
        unreachable!("`declare_instances` named each function's binding")
    };
    let qualified = format!("{trait_}::{name}");
    let sig = &function.signature;
    // The head's variables, then the function's own type parameters: the instance's
    // spelling of them, or the trait's where it writes none.
    let mut declared: Vec<PolyParam> = Vec::new();
    // A call determines the head's variables through the trait's operands, so only the
    // function's own type parameters have to be determined by its arguments.
    let mut spans: Vec<Option<Span>> = Vec::new();
    for (n, p) in variables {
        ctx.declare_type_throughout(n.as_str(), AliasType::Type(Type::Param(Rc::clone(p))));
        ctx.type_params_in_scope.push(n.to_string());
        declared.push(PolyParam {
            param: Rc::clone(p),
            kind: TypeKind::Type,
            bound_at: None,
        });
        spans.push(None);
    }
    // The associated types of the requirements the block names, which the instance a call
    // selects determines.
    for m in members {
        declared.push(m.clone());
        spans.push(None);
    }
    let own: Vec<Rc<TypeParam>> = if type_params.is_empty() {
        sig.params
            .iter()
            .map(|p| {
                let mine = TypeParam::declared(p.spelling.clone());
                ctx.declare_type_throughout(
                    p.spelling.as_str(),
                    AliasType::Type(Type::Param(Rc::clone(&mine))),
                );
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
    if let Some(p) = params.iter().find(|p| p.name == "self") {
        return Err(LoweringError::unsupported(
            p.name_span,
            format!(
                "`{qualified}` is no method, so no parameter of `{name}` is `self`; name it, \
                 and read the function from an instance, as `summon({trait_}(…))::{name}`"
            ),
        ));
    }
    let mut params: Vec<Param> = params.clone();
    for (i, (p, stated)) in params.iter_mut().zip(&inputs).enumerate() {
        match &p.annotation {
            None => {
                let alias = signature_alias(i);
                ctx.declare_type_throughout(alias.as_str(), AliasType::Type(stated.clone()));
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
            ctx.declare_type_throughout(alias.as_str(), AliasType::Type(output_ty));
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
    for (name, r) in &trait_.named {
        let at = r.map_types(|t| replace_params(t, &at_instance));
        ctx.named_requirements.push((name.clone(), Rc::new(at)));
    }
    ctx.named_requirements.extend(named.iter().cloned());
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
    /// The trait `name` names: the compiler's, one the module declares, or one a `use` name
    /// of the module reaches.
    pub(super) fn trait_named(&self, name: &str) -> Option<Trait> {
        Trait::compiler_named(name)
            .or_else(|| self.traits.iter().find(|t| t.name() == name).cloned())
            .or_else(
                || match self.module.uses.get(name).map(|used| &used.reached) {
                    Some(Reached::Trait(Some(trait_))) => Some(trait_.clone()),
                    _ => None,
                },
            )
    }

    /// The trait `qualifier::name` names, written at `span`: by its name, as
    /// [`trait_named`](Self::trait_named) reads it, or through the modules `qualifier`
    /// names, `shapes::Area` (`docs/chl-spec.md`, "Traits and instances across modules
    /// \[Decided\]").
    /// `Ok(None)` where an unqualified name names no trait. A qualified one names a trait or
    /// is an error.
    pub(super) fn resolve_trait(
        &self,
        qualifier: &[Spanned<SmolStr>],
        name: &Spanned<SmolStr>,
        span: Span,
    ) -> Result<Option<Trait>, LoweringError> {
        if qualifier.is_empty() {
            if let Some(Reached::Trait(None)) = self
                .module
                .uses
                .get(name.node.as_str())
                .map(|used| &used.reached)
            {
                return Err(Qualifier::no_trait(&name.node, name.span));
            }
            return Ok(self.trait_named(&name.node));
        }
        let at = self.qualifier_path(qualifier, span)?;
        let spelled = crate::ccl::names::QualifiedName::of_segments(qualifier);
        match at.reach_trait(&spelled, &name.node, name.span)? {
            Some(trait_) => Ok(Some(trait_)),
            None => Err(Qualifier::no_trait(
                &spelled.child(name.node.clone()).to_string(),
                name.span,
            )),
        }
    }

    /// The trait an `instance` block's head names, or `None` where it names none by its name:
    /// a name written through a module names a trait or is an error.
    pub(super) fn block_trait(&self, block: &ImplBlock) -> Result<Option<Trait>, LoweringError> {
        self.resolve_trait(&block.qualifier, &block.ty, block.ty.span)
    }

    /// Whether an `impl` block's head names a trait, which a type's own block may not.
    pub(super) fn names_a_trait(&self, block: &ImplBlock) -> bool {
        self.block_trait(block).is_ok_and(|t| t.is_some())
    }

    /// The trait a qualified name's qualifier ends at, `Area` in `Area::area` and in
    /// `shapes::Area::area`, if it ends at one.
    ///
    /// An error where the qualifier's module declares a trait by that name but it cannot be
    /// reached, a private one. A name the module does not declare as a trait is not an
    /// error here: it is read as a type, whose own lowering reports what is wrong with it.
    pub(super) fn trait_of_member(
        &self,
        q: &QualifiedName,
    ) -> Result<Option<Trait>, LoweringError> {
        let Some((last, modules)) = q.qualifier.split_last() else {
            return Ok(None);
        };
        if modules.is_empty() {
            return self.resolve_trait(modules, last, last.span);
        }
        let Ok(at) = self.qualifier_path(modules, last.span) else {
            return Ok(None);
        };
        if !at.declares_trait(&last.node) {
            return Ok(None);
        }
        self.resolve_trait(modules, last, last.span)
    }

    /// The innermost requirement in scope that `name` names.
    pub(super) fn named_requirement(&self, name: &str) -> Option<Rc<TraitRequirement>> {
        self.named_requirements
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, r)| Rc::clone(r))
    }

    /// The program's instances, for inference; the context keeps none.
    pub(crate) fn take_instances(&mut self) -> InstanceTable {
        std::mem::take(&mut self.instances)
    }
}
