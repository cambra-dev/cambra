//! A feed's contribution from under nested loops, keyed by the tuple of the loops' positions
//! (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability").
//!
//! Two phases build this key. `channelize` rebuilds a nest it finds under a feed
//! ([`Nest`]), and `mut_elim` flattens the taps a recurrence's feeds rode
//! ([`flatten_nested_contribution`], through [`crate::ccl::mut_elim::hoist_feeds`]). Both
//! take a nest in one of two forms: the product of the loops' positions where no loop's source
//! reads an enclosing loop ([`nest_as_product`]), and otherwise one collection per level,
//! indexed by that level's position ([`indexed_nest`]), whose levels are then flattened.
//!
//! Both are the forms a multi-clause comprehension lowers to (`src/ccl/lower/comprehension.rs`),
//! rebuilt here on the typed tree because loops reach these phases as loops. The product
//! applies where no loop's source or filter reads an enclosing position, and keys the feed by
//! the plain tuple of positions, with each filter lifted onto it. Where one does, that loop's
//! keys depend on the enclosing position, so the nest is keyed by a dependent tuple, which the
//! indexed form builds a level at a time.

use std::rc::Rc;

use crate::ccl::ccl_utils::{
    PredMemo, apply_primitive, cast_target_refinement, compose_typed_or_hole, count_free,
};
use crate::ccl::{
    BaseType, BindingTransparency, Builtin, Expr, FunKind, Lit, Name, Refinement, Type,
    TypedBinding, TypedExpr, TypedExprNode, provenance::NodeId,
};

/// A feed out of a loop, lifted out of the loop with the values it fed: `view` holds them,
/// keyed by the positions of the `levels` loops around the feed, curried outermost first —
/// for an induction loop, `__hist ▷ .__to_<feed>` (`mut_elim`'s `hist_field_view`); for a
/// `with begin():` block, a commit-record tap binding.
pub(crate) struct LoopFeed {
    pub defer: Name,
    pub view: Expr,
    pub levels: usize,
    /// The site of the feed the values came from, which the feed hoisted for them keeps
    /// ([`crate::ccl::site`]).
    pub site: Option<Rc<crate::ccl::site::Site>>,
}

/// `λ param → body`, a channel contribution built around a fed value, with the kind of
/// `exemplar`'s function (`Compute` where there is none) and dependent where `body`'s type
/// reads `param`: a row fed in a loop may read the loop's variable
/// (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
pub(crate) fn contribution_lambda(
    param: &TypedBinding,
    body: Expr,
    exemplar: Option<&Type>,
) -> Expr {
    let codomain = body.ty.clone();
    let fun_kind = exemplar
        .and_then(
            |t| match Type::fun_like(t, param.ty.clone(), codomain.clone()) {
                Type::Fun { fun_kind, .. } => Some(fun_kind),
                _ => None,
            },
        )
        .unwrap_or(FunKind::Compute);
    let ty = if crate::ccl::subst::type_free_vars(&codomain).contains(&param.name) {
        Type::pi_kinded(param.name.clone(), param.ty.clone(), codomain, fun_kind)
    } else {
        Type::Fun {
            name: None,
            fun_kind,
            domain: Box::new(param.ty.clone()),
            codomain: Box::new(codomain),
            effects: crate::ccl::effects::Effects::none(),
        }
    };
    Expr::lambda(&param.name, param.ty.clone(), body).with_ty(ty)
}

/// A feed's contribution from under `levels` loops, keyed by the tuple of their positions:
/// rebuilt over their product where it is one, and otherwise indexed per level and flattened
/// ([`Nest`]).
pub(crate) fn key_by_positions(value: Expr, levels: usize) -> Expr {
    match classify_nest(&value, levels) {
        Nest::Product(generators) => nest_as_product(value, generators),
        Nest::Indexed => flatten_nested_contribution(indexed_nest(value, levels), levels),
        Nest::Flat => flatten_nested_contribution(value, levels),
    }
}

/// A feed contribution flattened to one entry per position it was fed at.
///
/// `<<` appends at the site it is written, so a feed inside a loop contributes one value
/// per position of that loop — which is what the loop's tap holds. Inside a **nest** the
/// enclosing tap holds the inner loop's whole tap collection per enclosing position, one
/// level per level the feed sits under, so the contribution arrives curried. Flattening
/// each of those levels away is what makes the channel the innermost positions rather than
/// the groups they fall into.
///
/// `levels` is the number of loops the feed sits under, so the contribution's outer `levels`
/// collection levels are positions. A fed value may hold collections of its own, beneath
/// those: `out << [[1, 2], [3]]` appends a collection of collections whole, so nothing of it
/// is flattened.
///
pub(crate) fn flatten_nested_contribution(mut value: Expr, levels: usize) -> Expr {
    for level in 0..levels.saturating_sub(1) {
        let Levels {
            outer_name,
            outer,
            inner_name,
            keys,
            elem,
        } = outer_levels(&value.ty);
        let paired = keyed_by(
            vec![
                (outer_name.clone(), outer.clone()),
                (inner_name.clone(), keys.clone()),
            ],
            elem.clone(),
        );
        value = apply_primitive(value, Builtin::Uncurry, paired.clone());
        // Past the first level the outer key is the tuple this loop built, and it is spliced
        // open: a feed under three loops is keyed by the three positions, not by a pair of a
        // pair and a position (`docs/chl-spec.md`, "8.4 Feeds are the second form of
        // mutability"). A loop's own key that is a tuple stays one; only the position this
        // flattening paired is spliced.
        if level > 0 {
            let flat = spliced(outer_name.as_ref(), &outer, inner_name, keys, elem);
            let positions = Expr::list(vec![
                Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int)),
            ])
            .with_ty(Type::data_fun(
                Type::UIntRange(1),
                Type::Base(BaseType::Int),
            ));
            let flatten = apply_primitive(
                positions,
                Builtin::FlattenDomain,
                Type::fun(paired, flat.clone()),
            );
            value = crate::ccl::ccl_utils::apply_function(value, flatten, flat);
        }
    }
    value
}

/// The two outer collection levels of a contribution, `(𝑘₀ : 𝐴) ⤇ (𝑘₁ : 𝐾) ⤇ 𝐸`, opened
/// by name: `keys` (`𝐾`) may read `outer_name`, and `elem` (`𝐸`) both names. An inner loop
/// whose positions depend on the outer loop's value is the case where `𝐾` reads `𝑘₀`.
struct Levels {
    outer_name: Option<Name>,
    outer: Type,
    inner_name: Option<Name>,
    keys: Type,
    elem: Type,
}

fn outer_levels(ty: &Type) -> Levels {
    let Type::Fun {
        fun_kind: FunKind::Data(_),
        name: outer_name,
        domain: outer,
        codomain: inner,
        ..
    } = ty.peel_refinements()
    else {
        unreachable!("a contribution has a collection level per loop it was fed under")
    };
    let inner = crate::ccl::subst::open_codomain(ty, inner);
    let Type::Fun {
        fun_kind: FunKind::Data(_),
        name: inner_name,
        domain: keys,
        codomain: elem,
        ..
    } = inner.peel_refinements()
    else {
        unreachable!("a contribution has a collection level per loop it was fed under")
    };
    Levels {
        outer_name: outer_name.clone(),
        outer: (**outer).clone(),
        inner_name: inner_name.clone(),
        keys: (**keys).clone(),
        elem: crate::ccl::subst::open_codomain(inner.peel_refinements(), elem),
    }
}

/// The collection `(key : (𝑐₀ : 𝐶₀) × … × 𝐶ₙ) ⤇ 𝐸` over the telescope `components`, with
/// `elem`'s reads of each component name `𝑐ᵢ` read as `key.𝑖`. Where no component reads an
/// earlier one the key is the plain tuple ([`Type::dep_tuple`]), and where `elem` reads none
/// the function is unnamed.
fn keyed_by(components: Vec<(Option<Name>, Type)>, elem: Type) -> Type {
    let tuple = Type::dep_tuple(components.clone());
    let key = Name::fresh("__key");
    // A projection binds the key, which its component can read.
    let project = |index: usize, component: &Type| {
        Expr::apply(
            Expr::var(&key).with_ty(tuple.clone()),
            Expr::proj_index(index).with_ty(Type::pi(
                key.clone(),
                tuple.clone(),
                component.clone(),
            )),
        )
        .with_ty(component.clone())
    };
    let elem = components
        .iter()
        .enumerate()
        .filter_map(|(index, (name, _))| Some((index, name.clone()?)))
        .fold(elem, |elem, (index, name)| {
            let component = tuple
                .component_type(index, project)
                .expect("a telescope has a component per name");
            crate::ccl::subst::Subst::discharge(name, project(index, &component)).apply_type(&elem)
        });
    if crate::ccl::subst::codomain_depends_on(&key, &elem) {
        Type::pi_kinded(key, tuple, elem, FunKind::Data(None))
    } else {
        Type::data_fun(tuple, elem)
    }
}

/// The collection over `outer`'s components followed by `keys`, where `outer` is the tuple of
/// positions an earlier level built and `outer_name` the binder `keys` and `elem` read it
/// through: each read `outer_name.𝑗` becomes the spliced key's component `𝑗`
/// (`src/ccl/design/type-inference.md`, "Flattening").
fn spliced(
    outer_name: Option<&Name>,
    outer: &Type,
    inner_name: Option<Name>,
    mut keys: Type,
    mut elem: Type,
) -> Type {
    let prefix: Vec<(Option<Name>, Type)> = match outer {
        Type::Tuple(ts) => ts.iter().map(|t| (None, t.clone())).collect(),
        Type::DepTuple(cs) => cs.clone(),
        other => unreachable!("the level above was flattened to a tuple, got {other}"),
    };
    let names = crate::ccl::subst::tuple_component_names(&prefix);
    let opened = crate::ccl::subst::open_tuple_components(&prefix, |j, _| {
        crate::ccl::subst::Mapping::Rename(names[j].clone())
    });
    if let Some(outer_name) = outer_name {
        let components: Vec<Expr> = names
            .iter()
            .zip(&opened)
            .map(|(name, ty)| Expr::var(name).with_ty(ty.clone()))
            .collect();
        let memo = PredMemo::new();
        crate::ccl::subst::rewrite_pairing_projections_memo(
            outer_name,
            &components,
            &mut keys,
            &memo,
        );
        crate::ccl::subst::rewrite_pairing_projections_memo(
            outer_name,
            &components,
            &mut elem,
            &memo,
        );
        assert!(
            !crate::ccl::subst::type_free_vars(&keys).contains(outer_name)
                && !crate::ccl::subst::type_free_vars(&elem).contains(outer_name),
            "a nested feed's keys and rows read an earlier level's key only through its \
             components"
        );
    }
    let components = names
        .into_iter()
        .map(Some)
        .zip(opened)
        .chain([(inner_name, keys)])
        .collect();
    keyed_by(components, elem)
}

/// A feed's contribution from under nested loops, rebuilt over the product of the loops'
/// positions: `𝐴 ≫ (λ 𝑥 → 𝐵 ≫ (λ 𝑦 → 𝑣))` becomes
/// `λ 𝑝 : (𝐷𝐴, 𝐷𝐵) → (𝑝.0 ▷ 𝐴) ▷ (λ 𝑥 → (𝑝.1 ▷ 𝐵) ▷ (λ 𝑦 → 𝑣))`, at any depth. A feed is keyed
/// by the position of every loop around it, so the channel is one collection over the tuple of
/// positions rather than a collection per outer position. The form is the one a multi-clause
/// comprehension lowers to (`src/ccl/lower/comprehension.rs`), and a `let` around or between
/// the loops stays where it is.
///
/// The tuple's refinement carries the loops' filters, read at their components, which is
/// where planning applies them. A loop's filter is the refinement its source's cast adds
/// ([`refine_source_domain`](crate::ccl::channelize::refine_source_domain)); the cast is dropped from the loop's read, as a comprehension's
/// source carries none. No filter reads an enclosing loop's variable: that nest's keys depend
/// on the enclosing position, and [`indexed_nest`] builds it. A source's own domain refinement
/// stays on its component and is lifted as well; a present-key refinement is not a filter and
/// is not lifted.
///
/// [`classify_nest`] decides whether a contribution is that nest.
fn nest_as_product(contribution: Expr, generators: Vec<Generator>) -> Expr {
    let levels = generators.len();
    let domains: Vec<Type> = generators
        .iter()
        .map(|g| source_domain(&g.source().ty).expect("a loop's source is a collection"))
        .collect();
    let bare = Type::Tuple(domains.clone());
    let at = |index: usize| {
        Expr::apply(
            Expr::var(Name::elem()).with_ty(bare.clone()),
            Expr::proj_index(index).with_ty(Type::fun(bare.clone(), domains[index].clone())),
        )
        .with_ty(domains[index].clone())
    };
    let mut lifted: Vec<Refinement> = Vec::new();
    for (index, generator) in generators.iter().enumerate() {
        // The keys this loop ranges over: its source's own refinements and, where it filters,
        // the ones its `cast` states, which the keys satisfy together. A present-key
        // refinement is not a filter and is not lifted.
        let mut refinements: Vec<Refinement> = domains[index].refinements().to_vec();
        if let TypedExprNode::Cast { target, .. } = &generator.iterated.node {
            for r in cast_target_refinement(target)
                .expect("a loop filter's cast states the filter (`make_cast` asserts it)")
                .iter()
            {
                if !refinements.contains(r) {
                    refinements.push(r.clone());
                }
            }
        }
        for r in refinements.iter().filter(|r| !r.is_collection_membership()) {
            let predicate = crate::ccl::subst::Subst::discharge(Name::elem(), at(index))
                .apply_expr(&r.predicate);
            debug_assert!(
                generators[..index]
                    .iter()
                    .all(|g| count_free(&g.param.name, &predicate) == 0),
                "a product nest's filter reads no enclosing loop's variable ([`generator_nest`])"
            );
            lifted.push(Refinement::born(Rc::new(predicate)));
        }
    }
    let keys = if lifted.is_empty() {
        bare
    } else {
        let mut set = crate::ccl::ty::RefinementSet::new();
        set.extend(lifted);
        Type::Refinement(Box::new(bare), set)
    };
    let record = Name::fresh("__iter_record");
    let nest_params: Vec<Name> = generators.iter().map(|g| g.param.name.clone()).collect();
    around_lets(contribution, &mut |nest| {
        let body = rebuild_nest(nest, 0, levels, &mut |depth, _, param, inner| {
            let position = Expr::apply(
                Expr::var(&record).with_ty(keys.clone()),
                Expr::proj_index(depth).with_ty(Type::fun(keys.clone(), domains[depth].clone())),
            )
            .with_ty(domains[depth].clone());
            read_level(
                position,
                generators[depth].source().clone(),
                param,
                inner,
                &nest_params,
            )
        });
        collection_over(&record, keys.clone(), body)
    })
}

/// How a feed's contribution from under nested loops is rebuilt to be keyed by the tuple of
/// the loops' positions (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability").
enum Nest {
    /// No loop's source reads an enclosing loop's binder or a name bound inside one, so the
    /// positions are a product: [`nest_as_product`].
    Product(Vec<Generator>),
    /// Generators, some source reading an enclosing loop, so its positions differ per
    /// enclosing position: [`indexed_nest`], then [`flatten_nested_contribution`].
    Indexed,
    /// One loop, or a level that is not a loop generator but a collection indexed by position
    /// or a gated unit: [`flatten_nested_contribution`] alone.
    Flat,
}

/// Which [`Nest`] `contribution` is, fed under `levels` loops.
fn classify_nest(contribution: &Expr, levels: usize) -> Nest {
    if levels < 2 {
        return Nest::Flat;
    }
    let mut generators = Vec::with_capacity(levels);
    match generator_nest(
        contribution,
        levels,
        &mut NestScope::default(),
        &mut generators,
    ) {
        Some(true) => Nest::Product(generators),
        Some(false) => Nest::Indexed,
        None => Nest::Flat,
    }
}

/// `build` applied beneath the `let`s that open `expr`, which stay around what it builds: a
/// `let` ahead of the outermost loop is bound once, not once per position.
fn around_lets(expr: Expr, build: &mut dyn FnMut(Expr) -> Expr) -> Expr {
    if !matches!(expr.node, TypedExprNode::Let { .. }) {
        return build(expr);
    }
    let TypedExpr {
        node:
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            },
        user_annotation,
        node_id,
        ..
    } = expr
    else {
        unreachable!("matched as a `let`")
    };
    rebuild_let(
        binding,
        bound_expr,
        user_annotation,
        node_id,
        around_lets(*body, build),
    )
}

/// The `let` at `node_id` rebuilt around a new `body`, which gives it its type.
fn rebuild_let(
    binding: TypedBinding,
    bound_expr: Box<Expr>,
    user_annotation: Option<Type>,
    node_id: NodeId,
    body: Expr,
) -> Expr {
    TypedExpr {
        ty: lifted_past(&binding, &bound_expr, &body.ty),
        node: TypedExprNode::Let {
            binding,
            bound_expr,
            body: Box::new(body),
        },
        user_annotation,
        // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
        node_id,
        site: None,
    }
}

/// `ty`, written under the binder `binding` of a `let` defining it as `bound_expr`, as it reads
/// outside it: a transparent binder discharged to its definition, as inference's
/// `close_let_type` lifts a `let`'s type. An opaque binder's name stays.
pub(crate) fn lifted_past(binding: &TypedBinding, bound_expr: &Expr, ty: &Type) -> Type {
    if binding.transparency == BindingTransparency::Opaque
        || !crate::ccl::subst::type_free_vars(ty).contains(&binding.name)
    {
        return ty.clone();
    }
    crate::ccl::subst::Subst::discharge(
        &binding.name,
        crate::ccl::ccl_utils::predicate_term(bound_expr),
    )
    .apply_type(ty)
}

/// One generator of a nest, as [`generator_nest`] reads it: the term the loop iterates and
/// the loop's binder.
struct Generator {
    /// The loop's source, under the `cast` that carries the loop's filter when it has one
    /// ([`refine_source_domain`](crate::ccl::channelize::refine_source_domain)).
    iterated: Expr,
    param: TypedBinding,
}

impl Generator {
    /// The collection the loop reads its elements from: the iterated term without its
    /// filter's `cast`.
    fn source(&self) -> &Expr {
        match &self.iterated.node {
            TypedExprNode::Cast { value, .. } => value,
            _ => &self.iterated,
        }
    }
}

/// The names [`generator_nest`] has passed: the binders of enclosing generators and the
/// names bound between them.
#[derive(Default)]
struct NestScope {
    binders: Vec<Name>,
    lets: Vec<Name>,
}

/// Whether `nest` is `levels` generators, each a source composed with a lambda over its
/// elements, and if so whether it is **independent**: no generator's source or filter reads an
/// enclosing generator's binder or a name bound inside one. Collects each generator into
/// `generators`, outermost first. `None` where a level is not a loop generator but a collection indexed by position or
/// a gated unit, which [`flatten_nested_contribution`] takes as it is.
///
/// Decided by the nest's shape and the names its terms read alone: no type is consulted.
fn generator_nest(
    nest: &Expr,
    levels: usize,
    scope: &mut NestScope,
    generators: &mut Vec<Generator>,
) -> Option<bool> {
    if levels == 0 {
        return Some(true);
    }
    match &nest.node {
        TypedExprNode::Let { binding, body, .. } => {
            if !scope.binders.is_empty() {
                scope.lets.push(binding.name.clone());
            }
            generator_nest(body, levels, scope, generators)
        }
        TypedExprNode::Compose(elts) => {
            let [prefix @ .., last] = elts.as_slice() else {
                return None;
            };
            let TypedExprNode::Lambda { param, body } = &last.node else {
                return None;
            };
            let iterated = match prefix {
                [] => return None,
                [one] => one.clone(),
                _ => compose_typed_or_hole(prefix.to_vec()),
            };
            let generator = Generator {
                iterated,
                param: param.clone(),
            };
            // Neither the source nor its filter may read an enclosing binder or a name bound
            // between the loops: the loop's keys would then depend on the enclosing position,
            // and the keys of the nest are a dependent tuple rather than a product.
            let reads = |names: &[Name], e: &Expr| names.iter().any(|n| count_free(n, e) > 0);
            let independent = !reads(&scope.binders, &generator.iterated)
                && !reads(&scope.lets, &generator.iterated);
            generators.push(generator);
            scope.binders.push(param.name.clone());
            Some(generator_nest(body, levels - 1, scope, generators)? && independent)
        }
        _ => None,
    }
}

/// The domain of a loop's source: a collection's, or, for a read of a deferred collection
/// (a generator's channel, typed by its handle until `channelize` assembles it), the handle's
/// channel domain, which its read view states ([`Type::read_view`]).
fn source_domain(ty: &Type) -> Option<Type> {
    ty.read_view().domain()
}

/// The type of one item of a loop's source: a collection's codomain, or a deferred
/// collection's element type, as [`source_domain`] reads its domain.
fn source_item(ty: &Type) -> Type {
    ty.codomain()
        .or_else(|| ty.as_feed().map(|(_, element)| element.clone()))
        .unwrap_or_else(|| panic!("a loop's source is a collection, got {ty}"))
}

/// `nest` with each of its `levels` generators `𝑠 ≫ (λ 𝑥 → body)` rebuilt by `level`, which
/// is handed the generator's depth, its source `𝑠`, its binder `𝑥` and the rebuilt `body`.
/// Every `let` stays in place.
fn rebuild_nest(
    nest: Expr,
    depth: usize,
    levels: usize,
    level: &mut dyn FnMut(usize, Expr, TypedBinding, Expr) -> Expr,
) -> Expr {
    if depth == levels {
        return nest;
    }
    let TypedExpr {
        node,
        user_annotation,
        node_id,
        ..
    } = nest;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => rebuild_let(
            binding,
            bound_expr,
            user_annotation,
            node_id,
            rebuild_nest(*body, depth, levels, level),
        ),
        TypedExprNode::Compose(mut elts) => {
            let lambda = elts
                .pop()
                .expect("a generator has a source before its lambda");
            let TypedExprNode::Lambda { param, body } = lambda.node else {
                panic!("a loop level of a feed contribution is `𝑠 ≫ (λ 𝑥 → body)`")
            };
            let source = match elts.len() {
                1 => elts.pop().expect("one element"),
                _ => compose_typed_or_hole(elts),
            };
            let inner = rebuild_nest(*body, depth + 1, levels, level);
            level(depth, source, param, inner)
        }
        other => panic!(
            "a loop level of a feed contribution is `𝑠 ≫ (λ 𝑥 → body)`, got {}",
            other.kind_name()
        ),
    }
}

/// `(position ▷ source) ▷ (λ param → inner)`: one generator's step at `position`. The lambda's
/// type is dependent: a deeper generator's domain may name `param`, in a filter that reads it.
///
/// Where `inner`'s type reads a variable of the nest's loops (`nest_params`), as a row filtered
/// by one does, the step is `inner` with the read substituted for `param` in terms and types
/// alike, at every level, rather than a redex. The row's filter then reads the position, which
/// lambda elimination lifts onto the key as it lifts any filter reading a lambda's parameter.
/// Behind a redex, the variable the filter reads would be gone from the term by the time the
/// key's lambda is eliminated.
fn read_level(
    position: Expr,
    source: Expr,
    param: TypedBinding,
    inner: Expr,
    nest_params: &[Name],
) -> Expr {
    let item = source_item(&source.ty);
    let read = Expr::apply(position, source).with_ty(item);
    let row_reads = crate::ccl::subst::type_free_vars(&inner.ty);
    if nest_params.iter().any(|p| row_reads.contains(p)) {
        return crate::ccl::subst::Subst::discharge(param.name, read).apply_expr(&inner);
    }
    let ty = inner.ty.clone();
    let lambda = contribution_lambda(&param, inner, None);
    Expr::apply(read, lambda).with_ty(ty)
}

/// `λ position : domain → body`, a collection over `domain`, keyed where `body`'s type reads
/// `position`.
fn collection_over(position: &Name, domain: Type, body: Expr) -> Expr {
    let value = body.ty.clone();
    let ty = if crate::ccl::subst::type_free_vars(&value).contains(position) {
        Type::pi_kinded(position.clone(), domain.clone(), value, FunKind::Data(None))
    } else {
        Type::data_fun(domain.clone(), value)
    };
    Expr::lambda(position, domain, body).with_ty(ty)
}

/// A feed's contribution from under `levels` loops, each level indexed by its own position:
/// `𝐴 ≫ (λ 𝑥 → 𝐵 ≫ (λ 𝑦 → 𝑣))` becomes
/// `λ 𝑟 : 𝐷𝐴 → (𝑟 ▷ 𝐴) ▷ (λ 𝑥 → λ 𝑞 : 𝐷𝐵 → (𝑞 ▷ 𝐵) ▷ (λ 𝑦 → 𝑣))`, the form a nested
/// comprehension lowers to (`src/ccl/lower/comprehension.rs`). A generator composed onto its
/// source is a pipeline, which a recurrence's body cannot hold per position of the recurrence;
/// the indexed form is a collection there like any other.
///
/// A `let` between two levels is bound inside the inner level's position lambda, next to the
/// read of that level's source, as it is in [`nest_as_product`]'s form.
pub(crate) fn indexed_nest(nest: Expr, levels: usize) -> Expr {
    let nest_params = loop_params(&nest, levels);
    rebuild_nest(nest, 0, levels, &mut |_, source, param, inner| {
        let inner = lets_into_position(inner);
        let domain = source_domain(&source.ty).expect("a loop's source is a collection");
        let position = Name::fresh("__iter_record");
        let step = read_level(
            Expr::var(&position).with_ty(domain.clone()),
            source,
            param,
            inner,
            &nest_params,
        );
        collection_over(&position, domain, step)
    })
}

/// The variables of the `levels` loops of `nest`, outermost first: each `𝑠 ≫ (λ 𝑥 → body)`'s
/// `𝑥`, through the `let`s between them.
fn loop_params(nest: &Expr, levels: usize) -> Vec<Name> {
    let mut params = Vec::with_capacity(levels);
    let mut at = nest;
    while params.len() < levels {
        match &at.node {
            TypedExprNode::Let { body, .. } => at = body,
            TypedExprNode::Compose(elts) => match elts.last().map(|e| &e.node) {
                Some(TypedExprNode::Lambda { param, body }) => {
                    params.push(param.name.clone());
                    at = body;
                }
                _ => break,
            },
            _ => break,
        }
    }
    params
}

/// `expr` with the `let`s that open it moved inside the position lambda they open onto, if
/// they open onto one.
fn lets_into_position(expr: Expr) -> Expr {
    let TypedExprNode::Let { .. } = &expr.node else {
        return expr;
    };
    let TypedExpr {
        node:
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            },
        user_annotation,
        node_id,
        ..
    } = expr
    else {
        unreachable!("matched as a `let`")
    };
    let body = lets_into_position(*body);
    // The position lambda moves out from under the `let`, so its type reads the binding as the
    // `let`'s own type would.
    let lambda_ty = lifted_past(&binding, &bound_expr, &body.ty);
    let name = binding.name.clone();
    let rebind = |body: Expr| rebuild_let(binding, bound_expr, user_annotation, node_id, body);
    match body.node {
        // A filter that reads the binding refines the positions, so the binding stays where
        // the lambda's domain can name it.
        TypedExprNode::Lambda { param, body: step }
            if !crate::ccl::subst::type_free_vars(&param.ty).contains(&name) =>
        {
            TypedExpr {
                node: TypedExprNode::Lambda {
                    param,
                    body: Box::new(rebind(*step)),
                },
                ty: lambda_ty,
                ..body
            }
        }
        node => rebind(TypedExpr { node, ..body }),
    }
}
