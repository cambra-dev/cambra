//! Linking: each run of a module created from the module's one lowering, and the
//! shared imports around the root (`docs/modules.md`, "Linking").

use super::*;
use crate::ccl::{BaseType, BinOpKind, CompareKind, PredicateId, Refinement};

/// The spelling of the placeholder a module's chain holds where the code below
/// a run of it goes. User code cannot bind a double-underscore name, so no
/// reference in the module resolves to it.
pub const MODULE_BODY: &str = "__module_body";

/// The placeholder [`MODULE_BODY`] as an expression.
pub fn module_body() -> Expr {
    Expr::var(Name::raw(MODULE_BODY))
}

/// Whether `expr` is the placeholder [`MODULE_BODY`].
pub fn is_module_body(expr: &Expr) -> bool {
    matches!(&expr.node, TypedExprNode::Var(Name::Raw(s)) if s == MODULE_BODY)
}

/// The rest of the module below `expr`, when `expr` stands on a module's spine:
/// the body of a `let`, a mutable variable, a statement, a type alias, an `impl`
/// block's group of functions, or a `run`. A module's top level is the chain of
/// these bodies from the root.
pub(in crate::ccl::lower) fn spine_body(expr: &Expr) -> Option<&Expr> {
    match &expr.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. }
        | TypedExprNode::LetType { body, .. }
        | TypedExprNode::DefGroup { body, .. }
        | TypedExprNode::Run { body, .. } => Some(body.as_ref()),
        _ => None,
    }
}

/// [`spine_body`], to rewrite the rest of the module.
pub(in crate::ccl::lower) fn spine_body_mut(expr: &mut Expr) -> Option<&mut Expr> {
    match &mut expr.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. }
        | TypedExprNode::LetType { body, .. }
        | TypedExprNode::DefGroup { body, .. }
        | TypedExprNode::Run { body, .. } => Some(body.as_mut()),
        _ => None,
    }
}

/// The binders on `chain`'s spine and the node the spine ends at.
pub(super) fn spine(chain: &Expr) -> (Vec<&Name>, &Expr) {
    let mut binders = Vec::new();
    let mut at = chain;
    while let Some(body) = spine_body(at) {
        match &at.node {
            TypedExprNode::Let { binding, .. } | TypedExprNode::MutDecl { binding, .. } => {
                binders.push(&binding.name);
            }
            TypedExprNode::DefGroup { bindings, .. } => {
                binders.extend(bindings.iter().map(|(binding, _)| &binding.name));
            }
            _ => {}
        }
        at = body;
    }
    (binders, at)
}

/// Put each site in `e` that no run holds yet under the run at `run`.
fn in_run(e: &mut Expr, run: &RunPath) {
    if let Some(site) = &e.site
        && site.run == RunPath::default()
    {
        e.site = Some(site.in_run(run));
    }
    if let TypedExprNode::Feed {
        site: Some(site), ..
    } = &mut e.node
        && site.run == RunPath::default()
    {
        *site = site.in_run(run);
    }
    e.walk_children_mut(|child| in_run(child, run));
}

/// `chain` with `body` in place of its one placeholder, at the end of its spine.
pub fn fill_module_body(mut chain: Expr, body: Expr) -> Expr {
    let mut at = &mut chain;
    while !is_module_body(at) {
        at = spine_body_mut(at).expect("the placeholder of a module's chain stands on its spine");
    }
    *at = body;
    chain
}

/// `expr` with the `const` parameters of each copy of a module in it settled to the terms
/// `values` gives them, by the binder of each parameter's `let`: a literal, or a term over the
/// `const` parameters of the module checked alone, each read through the binder `own` gives
/// it (`docs/modules.md`, "Linking").
///
/// - Each predicate in a type slot reads the term in place of the binder, and each operation
///   over literals this leaves is folded to the literal it computes, and each ternary whose
///   condition this decides to the arm it takes. A predicate a copy holds then reads its
///   import's or run's arguments as values, or as terms over the checked module's own
///   parameters, which the predicates that module writes read too.
/// - Each such `let` of a scalar is bound at the singleton of its term,
///   `{Int | __elem == 𝑡}`, so a read of the parameter is known to be its term, and holds the
///   term: its literal, or, in a module checked alone, [`TypedExprNode::Abstract`] at the
///   singleton. A parameter of the checked module stands for the binder `own` gives it.
///
/// A reference that a literal or a parameter replaces keeps its id, as an operation folded
/// does, and a ternary takes its arm's. A term with operations is built, once for each
/// reference it replaces, before the predicates are rebuilt, since a rebuild copies and mints
/// nothing.
pub(super) fn settle_const_params(
    expr: &mut Expr,
    values: &HashMap<Name, (ConstTerm, Span)>,
    own: &HashMap<TypeParamId, Name>,
    ctx: &mut LoweringContext,
) {
    use crate::ccl::lower::nominal::predicate_term;
    if values.is_empty() {
        return;
    }
    let param = |p: &ConstParam| -> Name {
        own.get(&p.id).cloned().unwrap_or_else(|| {
            panic!(
                "a copy's `const` argument reads only the `const` parameters of the module \
                 checked alone, and `{}` is none",
                p.spelling
            )
        })
    };
    // A literal or a parameter takes a reference's place in the reference's own node.
    let leaf = |term: &ConstTerm| match term {
        ConstTerm::Lit(lit) => Some(TypedExprNode::Lit(lit.clone())),
        ConstTerm::Param(p) => Some(TypedExprNode::Var(param(p))),
        _ => None,
    };
    fn count(expr: &Expr, values: &HashMap<Name, (ConstTerm, Span)>, n: &mut HashMap<Name, usize>) {
        if let TypedExprNode::Var(name) = &expr.node
            && values.contains_key(name)
        {
            *n.entry(name.clone()).or_default() += 1;
        }
        expr.walk_children(|child| count(child, values, n));
    }
    fn counts(
        expr: &Expr,
        values: &HashMap<Name, (ConstTerm, Span)>,
        seen: &mut HashSet<PredicateId>,
        n: &mut HashMap<Name, usize>,
    ) {
        expr.walk_type_slots(|ty| {
            walk_refined_predicates(ty, seen, &mut |predicate, _| count(predicate, values, n));
        });
        expr.walk_children(|child| counts(child, values, seen, n));
    }
    let mut occurrences = HashMap::new();
    counts(expr, values, &mut HashSet::new(), &mut occurrences);
    let mut built: HashMap<Name, Vec<Expr>> = HashMap::new();
    for (binder, n) in occurrences {
        let (term, span) = &values[&binder];
        if leaf(term).is_none() {
            let terms = (0..n)
                .map(|_| predicate_term(term, &param, *span, ctx))
                .collect();
            built.insert(binder, terms);
        }
    }
    fn replace(
        expr: &mut Expr,
        values: &HashMap<Name, (ConstTerm, Span)>,
        leaf: &dyn Fn(&ConstTerm) -> Option<TypedExprNode>,
        built: &mut HashMap<Name, Vec<Expr>>,
    ) -> bool {
        if let TypedExprNode::Var(name) = &expr.node
            && let Some((term, _)) = values.get(name)
        {
            match leaf(term) {
                Some(node) => expr.node = node,
                None => {
                    let name = name.clone();
                    *expr = built
                        .get_mut(&name)
                        .and_then(Vec::pop)
                        .expect("a term is built for each reference");
                }
            }
            return true;
        }
        let mut replaced = false;
        expr.walk_children_mut(|child| replaced |= replace(child, values, leaf, built));
        replaced
    }
    fn walk(
        expr: &mut Expr,
        values: &HashMap<Name, (ConstTerm, Span)>,
        leaf: &dyn Fn(&ConstTerm) -> Option<TypedExprNode>,
        built: &mut HashMap<Name, Vec<Expr>>,
        memo: &PredMemo,
    ) {
        expr.walk_type_slots_mut(|ty| {
            walk_refined_predicates_mut(ty, memo, &(), &mut |predicate, _| {
                let replaced = replace(predicate, values, leaf, built);
                let folded = fold(predicate);
                replaced || folded
            });
        });
        expr.walk_children_mut(|child| walk(child, values, leaf, built, memo));
    }
    walk(expr, values, &leaf, &mut built, &PredMemo::new());
    debug_assert!(
        built.values().all(Vec::is_empty),
        "every term built is placed"
    );
    // Each parameter's `let`, bound at the singleton of its term.
    fn bind(
        expr: &mut Expr,
        values: &HashMap<Name, (ConstTerm, Span)>,
        param: &dyn Fn(&ConstParam) -> Name,
        ctx: &mut LoweringContext,
    ) {
        if let TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } = &mut expr.node
            && let Some((term, span)) = values.get(&binding.name)
            && let Some(Type::Base(base)) = binding.user_annotation.clone()
            && base != BaseType::Unit
        {
            const LABEL: &str = "link.const_singleton";
            // An annotation is cleared once inference has read it, so each of its nodes is
            // recorded as a predicate's ([`LoweringContext::tag_predicate`]).
            let value = match term {
                ConstTerm::Lit(lit) => Expr::lit(lit.clone()),
                ConstTerm::Param(p) => Expr::var(param(p)),
                _ => predicate_term(term, param, *span, ctx),
            };
            let predicate = Expr::binop(
                Expr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                value,
            );
            ctx.tag_predicate(&predicate, *span, LABEL);
            binding.user_annotation = Some(Type::refined_one(
                Type::Base(base),
                Refinement::born(Rc::new(predicate)),
            ));
            // The `let` holds its term: a literal is its value, and a term over the
            // parameters of a module checked alone is a value known only by its type, the
            // singleton, in a tree that only the check reads.
            bound_expr.node = match term {
                ConstTerm::Lit(lit) => TypedExprNode::Lit(lit.clone()),
                _ => TypedExprNode::Abstract,
            };
        }
        expr.walk_children_mut(|child| bind(child, values, param, ctx));
    }
    bind(expr, values, &param, ctx);
}

/// Fold `expr`, a predicate: each operation over literals to the literal it computes, and
/// each ternary whose condition is a literal to the arm it takes. Returns whether it changed.
fn fold(expr: &mut Expr) -> bool {
    let mut changed = false;
    expr.walk_children_mut(|child| changed |= fold(child));
    if let TypedExprNode::BinOp { left, op, right } = &expr.node
        && let (TypedExprNode::Lit(l), TypedExprNode::Lit(r)) = (&left.node, &right.node)
        && let Some(value) = crate::ccl::constant::fold_binop(*op, l, r)
    {
        expr.node = TypedExprNode::Lit(value);
        changed = true;
    }
    let negated = match &expr.node {
        TypedExprNode::UnaryOp(crate::ccl::UnaryOpKind::Neg, operand) => match operand.node {
            TypedExprNode::Lit(Lit::Int(n)) => n.checked_neg().map(Lit::Int),
            _ => None,
        },
        TypedExprNode::UnaryOp(crate::ccl::UnaryOpKind::Not, operand) => match operand.node {
            TypedExprNode::Lit(Lit::Bool(b)) => Some(Lit::Bool(!b)),
            _ => None,
        },
        _ => None,
    };
    if let Some(value) = negated {
        expr.node = TypedExprNode::Lit(value);
        changed = true;
    }
    // A ternary, as `predicate_term` builds one: the first branch whose guard holds.
    if let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &mut expr.node
    {
        while branches.len() > 1
            && matches!(branches[0].guard.node, TypedExprNode::Lit(Lit::Bool(false)))
        {
            branches.remove(0);
            changed = true;
        }
        if matches!(branches[0].guard.node, TypedExprNode::Lit(Lit::Bool(true))) {
            let taken = std::mem::take(&mut branches[0].body);
            expr.node = taken.node;
            changed = true;
        }
    }
    changed
}

/// A `const` parameter whose value is a tuple, a record or a list, by the binder of its
/// `let`, which no predicate holds yet (`docs/chl-spec.md`, "Declaring a nominal type").
#[derive(Debug, Clone)]
pub(super) struct CompoundConst {
    name: SmolStr,
    value: ConstTerm,
    /// The statement that gives the value: a `run`, an `import`, or the root's `const param`.
    given: Span,
    /// The parameter's declaration.
    declared: Span,
}

/// One error per parameter of `compounds` that a refinement predicate in `expr`'s type slots
/// reads.
pub(super) fn compound_const_reads(
    expr: &Expr,
    compounds: &HashMap<Name, CompoundConst>,
) -> Vec<LoweringError> {
    fn walk<'a>(
        expr: &Expr,
        compounds: &'a HashMap<Name, CompoundConst>,
        read: &mut Vec<&'a CompoundConst>,
    ) {
        expr.walk_type_slots(&mut |ty: &Type| {
            walk_refined_predicates(ty, &mut HashSet::new(), &mut |predicate, _| {
                for name in free_names(predicate) {
                    if let Some(compound) = compounds.get(&name)
                        && !read.iter().any(|r| std::ptr::eq(*r, compound))
                    {
                        read.push(compound);
                    }
                }
            });
        });
        expr.walk_children(|child| walk(child, compounds, read));
    }
    if compounds.is_empty() {
        return Vec::new();
    }
    let mut read = Vec::new();
    walk(expr, compounds, &mut read);
    read.sort_by_key(|c| (c.given.start, c.name.clone()));
    read.into_iter()
        .map(|c| {
            let error = LoweringError::unsupported(
                c.given,
                format!(
                    "`{}` is `{}` here, and a declaration's refinement reads it; a tuple, a \
                     record or a list constant in a declaration's refinement is not supported \
                     yet",
                    c.name, c.value
                ),
            );
            if c.declared == c.given {
                error
            } else {
                error.with_related(c.declared, "the parameter")
            }
        })
        .collect()
}

/// `expr`, a copy of a module's chain, with each refinement predicate in its type slots
/// copied too, once per predicate, so a term several slots share stays one term. A copy of
/// a chain shares its predicates with the module's, and uniquifying rebuilds each with the
/// ids it had, so two runs of the module in one tree would hold two predicates of one id.
/// The first copy in a tree keeps the module's, which the declarations of its nominal types
/// share, so a predicate inference reads off a declaration is one the tree holds
/// ([`ProgramLowering::holding_predicates`]). Copied in the chain's copy frame, a
/// predicate's nodes are copies of the module's, as the chain's are.
/// `copies` holds each predicate copied, with the original, which keeps its address from
/// being reused while it keys the map.
fn copy_predicates(expr: &mut Expr, copies: &mut HashMap<PredicateId, (Rc<Expr>, Rc<Expr>)>) {
    fn in_type(ty: &mut Type, copies: &mut HashMap<PredicateId, (Rc<Expr>, Rc<Expr>)>) {
        if let Type::Refinement(_, refinements) = ty {
            refinements.rewrite_each(|_, refinement| {
                let id = refinement.predicate_id();
                let copy = match copies.get(&id) {
                    Some((_, copy)) => Rc::clone(copy),
                    None => {
                        let mut copy = (*refinement.predicate).clone();
                        copy_predicates(&mut copy, copies);
                        let copy = Rc::new(copy);
                        let original = Rc::clone(&refinement.predicate);
                        copies.insert(id, (original, Rc::clone(&copy)));
                        copy
                    }
                };
                refinement.predicate = copy;
            });
        }
        ty.walk_children_mut(|child| in_type(child, copies));
    }
    expr.walk_type_slots_mut(|ty| in_type(ty, copies));
    expr.walk_children_mut(|child| copy_predicates(child, copies));
}

/// `names` keyed by the raw name each spelling lowers to: the scope
/// [`uniquify::run_in`] resolves a run's raw references in.
pub(super) fn raw_scope(names: &HashMap<QualifiedName, Name>) -> HashMap<String, Name> {
    names
        .iter()
        .map(|(spelling, name)| (spelling.to_string(), name.clone()))
        .collect()
}

/// `errors` in source order, with the errors that differ only in their labels merged into one
/// that has the labels of each: the copies of a statement that raise an error their arguments
/// give rise to ([`ProgramLowering::at_enclosing_run`]).
pub(super) fn in_source_order(errors: Vec<LoweringError>) -> Vec<LoweringError> {
    let mut merged: Vec<LoweringError> = Vec::new();
    for error in errors {
        match merged.iter_mut().find(|e| e.differs_only_in_labels(&error)) {
            Some(into) => {
                for label in error.related() {
                    if !into.related().contains(label) {
                        into.related_mut().push(label.clone());
                    }
                }
            }
            None => merged.push(error),
        }
    }
    merged.sort_by_key(|e| {
        let span = e.span();
        (span.file, span.start, span.end)
    });
    merged
}

/// Lower every module of `program` once and link its runs into one tree
/// (`docs/modules.md`, "A module lowers once", "Linking").
///
/// Each module lowers in link order, so the modules it imports and runs lower
/// before it, and the root lowers last. Linking then creates each imported
/// module's shared import, in link order, and the root's run, which creates each
/// run it declares in turn. The shared imports' chains wrap the root's, the first
/// in link order outermost. A module whose own errors stop it from lowering has
/// no interface, and a reference into it lowers to an error placeholder without
/// an error of its own.
///
/// An imported module that performs IO or declares state has no shared import,
/// and each `import` of it is the error.
pub fn lower_program(program: &LoadedProgram, ctx: &mut LoweringContext) -> LoweringResult {
    let sources = program.sources();
    let root = sources.root();
    let mut lowering = ProgramLowering::new(program);
    // With a cycle there is no link order, and the root lowers with no module to
    // reach: loading has reported the cycle.
    let order = program.link_order().unwrap_or_default();
    // Each import's shared import is decided once the module it imports has
    // lowered, and before its importer lowers, so the importer reaches the
    // types its arguments give.
    let mut sites = HashMap::new();
    for &file in order {
        lowering.import_keys(file, &mut sites, ctx);
        if file != root {
            lowering.lower(file, ctx);
        }
    }
    if !order.contains(&root) {
        lowering.import_keys(root, &mut sites, ctx);
    }
    let chains = lowering.shared_imports(order, &sites, ctx);

    let Some(ast) = program.root() else {
        return LoweringResult {
            value: None,
            errors: lowering.errors,
        };
    };
    let scope = lowering.scope(ast, None, ctx);
    ctx.begin_module(scope.clone());
    let lowered = lower_root(ast, ctx);
    // The root has one run, which no `run` statement supplies arguments.
    for stmt in &ast.body {
        if let ChlStmt::Param {
            name,
            default: None,
            ..
        } = &stmt.node
        {
            lowering.errors.push(LoweringError::unsupported(
                stmt.span,
                format!(
                    "the root module's parameter `{}` has no default, and no `run` statement \
                     supplies the root's arguments: run this module from a root instead",
                    name.node
                ),
            ));
        }
    }
    let sinks = std::mem::take(&mut ctx.declared_sinks);
    let mut errors = std::mem::take(&mut lowering.errors);
    errors.extend(lowered.errors);
    let parameters: Vec<(SmolStr, Span, Rc<ModuleType>, QualifiedName)> = ctx
        .parameters
        .iter()
        .filter_map(|parameter| {
            Some((
                parameter.name.clone(),
                parameter.declared,
                Rc::clone(parameter.module()?),
                parameter.module_default()?.clone(),
            ))
        })
        .collect();
    // The root's type parameters take their defaults, and so do the abstract
    // type members of its Module-typed parameters. Each type parameter takes
    // its default after the ones declared above it, which its default may name.
    let mut defaults = Arguments::default();
    for parameter in &ctx.parameters {
        let Some(ty) = parameter.module() else {
            continue;
        };
        for (member, param) in abstract_members(&QualifiedName::new(parameter.name.clone()), ty) {
            if let Some(default) = parameter.default_type(&member) {
                defaults.types.insert(param.id, default.clone());
            }
        }
    }
    let mut declared: Vec<&Parameter> = ctx.parameters.iter().collect();
    declared.sort_by_key(|parameter| parameter.declared.start);
    for parameter in declared {
        if let ParameterKind::Type {
            param,
            default: Some(default),
            ..
        } = &parameter.kind
        {
            let mut default = default.clone();
            substitute(&mut default, &defaults);
            defaults.types.insert(param.id, default);
        }
        // A `const` parameter takes its default, a term over the ones above it.
        if let Some(constant) = parameter.constant()
            && let Some(default) = &constant.default
        {
            match default.substituted(&defaults.consts) {
                Ok(term) => {
                    defaults.consts.insert(constant.param.id, term);
                }
                Err(no_value) => lowering.errors.push(LoweringError::unsupported(
                    parameter.declared,
                    format!(
                        "the default of `{}` has no value: {}",
                        parameter.name, no_value.0
                    ),
                )),
            }
        }
    }
    // The root's lowering, for its check: a copy no tree holds.
    let run_checks = std::mem::take(&mut ctx.run_type_checks);
    let root_lowered = lowered
        .value
        .as_ref()
        .filter(|_| errors.is_empty())
        .map(|chain| {
            let module = sources
                .module(root)
                .cloned()
                .unwrap_or_else(|| ModulePath::new([SmolStr::from("main")]));
            LoweredModule {
                chain: chain.clone_preserving_ids(),
                interface: Rc::new(Interface::of_lowered(
                    module,
                    ast,
                    chain,
                    ctx.parameters.clone(),
                    ctx,
                    None,
                )),
                scope: scope.clone(),
                sinks: Vec::new(),
                run_checks,
                as_root: true,
            }
        });
    let value = lowered.value.map(|mut chain| {
        substitute_in(&mut chain, &defaults);
        let mut qualified = lowering.shared_names(&scope);
        // The root's Module-typed parameters take their defaults.
        let mut modules = HashMap::new();
        for (name, declared, ty, default) in parameters {
            let names = Rc::new(names_under(&qualified, &default));
            let at = (declared, declared);
            chain = lowering.bind_module_parameter(chain, &name, &ty, &names, at, ctx);
            modules.insert(name, names);
        }
        let program_span = ast
            .body
            .first()
            .map_or(Span::new(root, 0, 0), |stmt| stmt.span);
        let sinks = sinks_at(
            &sinks,
            &defaults.consts,
            &mut chain,
            program_span,
            &mut lowering.errors,
        );
        let chain = lowering.expand_runs(
            chain,
            &RunPath::default(),
            &mut qualified,
            &modules,
            &defaults.consts,
            ctx,
        );
        let (chain, refused) = finish_program(&ast.body, chain, &sinks, ctx);
        lowering.errors.extend(refused);
        let scope = use_names(&scope, qualified);
        let root = uniquify::run_in(chain, &raw_scope(&scope), None);
        // The root's `const` parameters bind their `let`s on its spine, with no home.
        let (spine_binders, _) = spine(&root);
        for binder in spine_binders {
            if binder.home().is_none()
                && let Some(constant) = ctx.constants.param(binder.base())
                && let Some(value) = defaults.consts.get(&constant.id)
                && let Some(parameter) = ctx.parameters.iter().find(|p| p.name == binder.base())
            {
                lowering.record_const(binder, value, parameter, parameter.declared);
            }
        }
        let mut program = chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| fill_module_body(chain, body));
        add_method_copies(&mut program, &lowering.method_copies, ctx);
        settle_const_params(&mut program, &lowering.const_values, &HashMap::new(), ctx);
        let refused = compound_const_reads(&program, &lowering.const_compounds);
        lowering.errors.extend(refused);
        program
    });
    errors.extend(std::mem::take(&mut lowering.errors));
    // Each `import` reaching a shared import brings its copy in.
    for (statement, imported) in &lowering.imports {
        let home = Home::Import(imported.shared.clone());
        if ctx
            .run_sites
            .by_file
            .values()
            .any(|homes| homes.contains(&home))
        {
            let label = format!(
                "this import reaches the shared import `{}`, whose copy fails",
                imported.shared
            );
            ctx.run_sites
                .statements
                .entry(home)
                .or_default()
                .push((*statement, label));
        }
    }
    // Each module is checked on its own, once linking has found nothing wrong.
    // The root's check is the linked program's inference, unless its parameters
    // or the arguments its own runs and imports pass need one of their own.
    if errors.is_empty() && value.is_some() {
        if let Some(root_lowered) = root_lowered
            && (!root_lowered.interface.parameters.is_empty()
                || !lowering
                    .inferred_arguments(root, &root_lowered.chain)
                    .is_empty()
                || root_lowered
                    .run_checks
                    .values()
                    .any(|checks| !checks.is_empty())
                || lowering
                    .import_checks
                    .get(&root)
                    .is_some_and(|checks| !checks.is_empty()))
        {
            lowering.lowered.insert(root, Some(Rc::new(root_lowered)));
        }
        ctx.root_statements = lowering.statements(root);
        lowering.check_all(order, ctx);
        errors.extend(std::mem::take(&mut lowering.errors));
    }
    LoweringResult {
        value,
        errors: in_source_order(errors),
    }
}

/// The lowering of a program's modules: each module lowered once, the shared
/// import each `import` reaches, the names each shared import reaches, and the errors
/// found.
pub(super) struct ProgramLowering<'a> {
    pub(super) program: &'a LoadedProgram,
    /// Each module other than the root, lowered, by file, or `None` when it has
    /// no syntax tree or has errors of its own.
    pub(super) lowered: HashMap<FileId, Option<Rc<LoweredModule>>>,
    /// What each `import` statement reaches, by the statement. An import whose
    /// arguments are in error reaches nothing.
    pub(super) imports: HashMap<Span, Imported>,
    /// The key of each type an import passes as an argument.
    pub(super) type_keys: TypeKeys,
    /// The names each shared import reaches ([`Created::names`]), or `None` when it
    /// has none.
    pub(super) shared: HashMap<SharedImport, Option<Rc<HashMap<QualifiedName, Name>>>>,
    /// The imported modules whose statements an import may not hold have been
    /// reported ([`ProgramLowering::importable`]).
    pub(super) import_refusals: HashSet<FileId>,
    /// The modules a copy in the tree being assembled holds the own predicates of
    /// ([`copy_predicates`]).
    pub(super) holding_predicates: HashSet<FileId>,
    /// Each shared import's chain, as linking created it, in the order created,
    /// which a module's check copies ([`ProgramLowering::check`]).
    pub(super) shared_chains: Vec<(SharedImport, Expr)>,
    /// The shared imports each shared import reaches: its arguments' and its
    /// module's imports'.
    pub(super) shared_reached: HashMap<SharedImport, Vec<SharedImport>>,
    /// Whether runs are being created for a module's check, which registers no
    /// sink or route.
    pub(super) checking: bool,
    /// Whether the runs being created are declared by a module run inside the
    /// module being linked or checked. Creating one raises no error of its `run`
    /// statement or its arguments: those depend on the statement and the
    /// interface it runs alone, so its module's own check raises them
    /// ([`ProgramLowering::create`]).
    pub(super) nested: bool,
    /// The run whose copy's runs are being created, with its statement. An error that a
    /// copy's arguments give rise to carries a label at it
    /// ([`ProgramLowering::at_enclosing_run`]).
    pub(super) enclosing: Option<(RunPath, Span)>,
    /// The checks of each module's imports' type arguments, by the importer
    /// ([`ProgramLowering::import_keys`]).
    pub(super) import_checks: HashMap<FileId, Vec<TypeCheck>>,
    pub(super) errors: Vec<LoweringError>,
    /// Each run's and shared import's copy of each public method of each public type its
    /// module declares, which a method call reaches wherever the copy is in scope
    /// ([`add_method_copies`]).
    pub(super) method_copies: Vec<MethodCopy>,
    /// The term each `const` parameter of a copy of a module takes, a literal or a term over
    /// the parameters of the module checked alone, with the span its import or run gives it
    /// at, by the binder of the parameter's `let` in the copy's chain
    /// ([`settle_const_params`]).
    pub(super) const_values: HashMap<Name, (ConstTerm, Span)>,
    /// Each `const` parameter of a copy of a module whose value is a tuple, a record or a
    /// list, by the binder of its `let`, which no predicate may read yet ([`compound_const_reads`]).
    pub(super) const_compounds: HashMap<Name, CompoundConst>,
}

/// A run's or a shared import's copy of a public method
/// ([`ProgramLowering::method_copies`]).
#[derive(Clone)]
pub(super) struct MethodCopy {
    /// The type, as the instance the copy's arguments reach.
    decl: Rc<crate::ccl::nominal::NominalDecl>,
    method: SmolStr,
    /// The number of value parameters it declares after `self`.
    params: usize,
    binder: Name,
    /// The method's declaration, which a reference to the copy is imaged at.
    declared: Span,
}

/// Add to each method call in `tree` a candidate for each of `copies` of its method,
/// after the candidates lowering found. Inference takes a copy only where its binding is
/// in scope ([`crate::ccl::MethodCandidate::copy`]), which reaches a type whose module the
/// calling module neither imports nor runs (`docs/chl-spec.md`, "Associated functions and
/// methods").
pub(super) fn add_method_copies(tree: &mut Expr, copies: &[MethodCopy], ctx: &mut LoweringContext) {
    if copies.is_empty() {
        return;
    }
    if let TypedExprNode::Method {
        name, candidates, ..
    } = &mut tree.node
    {
        for copy in copies.iter().filter(|c| c.method == name.as_str()) {
            let function = ctx.tag_machinery(
                Expr::var(copy.binder.clone()),
                copy.declared,
                "link.method_copy",
            );
            candidates.push(crate::ccl::MethodCandidate {
                decl: Rc::clone(&copy.decl),
                params: copy.params,
                function,
                copy: true,
            });
        }
    }
    tree.walk_children_mut(|child| add_method_copies(child, copies, ctx));
}

/// The copy `binder` is of a public method of a public type `interface` declares, if it is
/// one, with the type as the instance the copy's `defaults` and `arguments` reach.
fn method_copy(
    interface: &Interface,
    binder: &Name,
    defaults: &Arguments,
    arguments: &Arguments,
) -> Option<MethodCopy> {
    let (ty, method) = binder.base().split_once("::")?;
    let member = interface.nominal.get(ty).filter(|member| member.public)?;
    let (params, declared) = match member.functions.get(method) {
        Some(function) if function.public && function.is_method => {
            (function.arity - 1, function.declared)
        }
        Some(_) => return None,
        None if method == "extract" && member.decl.declares_extract => (0, member.declared),
        None => return None,
    };
    let mut decl = Rc::clone(&member.decl);
    substitute_decl(&mut decl, defaults);
    substitute_decl(&mut decl, arguments);
    Some(MethodCopy {
        decl,
        method: method.into(),
        params,
        binder: binder.clone(),
        declared,
    })
}

/// The arguments a run is created with ([`ProgramLowering::create`]).
pub(super) enum Supplied<'a> {
    /// A run's: the parameters its `run` statement passes value arguments for,
    /// each bound above the run under its run name, its module arguments, each
    /// the names its module reaches, with the argument's span, and its type
    /// arguments, by parameter, as its declaring module's chain holds them.
    Run(
        &'a [SmolStr],
        Vec<PassedModule>,
        HashMap<QualifiedName, Type>,
    ),
    /// A shared import's: its import's constants, a literal bound at the head of
    /// its chain under its spelling, `scaled(scale=3)`, and an import name
    /// reaching its shared import.
    Import(&'a SharedImport, &'a ImportSite),
}

/// A module passed to a Module-typed parameter, at `span`: the names its run
/// reaches ([`Created::names`]), or `None` when the module has errors of its
/// own.
#[derive(Clone)]
pub(super) struct PassedModule {
    pub(super) parameter: SmolStr,
    pub(super) names: Option<Rc<HashMap<QualifiedName, Name>>>,
    pub(super) span: Span,
}

/// A module lowered once ([`ProgramLowering::lower`]).
pub(super) struct LoweredModule {
    /// The module's top-level statements around [`MODULE_BODY`], each `run`
    /// statement a [`TypedExprNode::Run`], not uniquified.
    pub(super) chain: Expr,
    pub(super) interface: Rc<Interface>,
    /// The scope it lowered in, which each run of it is uniquified against.
    pub(super) scope: ModuleScope,
    /// The sinks it declares, which each run of it registers.
    pub(super) sinks: Vec<DeclaredSink>,
    /// The checks of each `run` statement's type arguments, by run name, which
    /// the module's check makes ([`LoweringContext::declare_run_types`]).
    pub(super) run_checks: HashMap<SmolStr, Vec<TypeCheck>>,
    /// Whether it was lowered as the root, so its chain ends at its last
    /// statement rather than at [`MODULE_BODY`].
    pub(super) as_root: bool,
}

/// Where each run and shared import of a linked program is brought in, for the
/// errors a pass after linking raises in its copy (`docs/modules.md`,
/// "Diagnostics").
#[derive(Debug, Default)]
pub struct RunSites {
    /// Each run's `run` statement, or each `import` that reaches a shared import,
    /// with its label's text, by the run's home.
    pub statements: HashMap<Home, Vec<(Span, String)>>,
    /// The runs and shared imports of each module, by its file.
    pub by_file: HashMap<FileId, Vec<Home>>,
}

/// One run of a module, created ([`ProgramLowering::create`]).
pub(super) struct Created {
    /// The run's chain, uniquified, around the placeholder for the rest of the
    /// tree it stands in.
    pub(super) chain: Expr,
    /// Each name the run's top level resolves, by spelling: its members, the
    /// other binders on its spine, its `use` names, and each name spelled
    /// through one of its qualifiers. A module reaching the run spells each
    /// through its own qualifier for it ([`reroot`]).
    pub(super) names: HashMap<QualifiedName, Name>,
}

impl<'a> ProgramLowering<'a> {
    pub(super) fn new(program: &'a LoadedProgram) -> Self {
        ProgramLowering {
            program,
            lowered: HashMap::new(),
            imports: HashMap::new(),
            type_keys: TypeKeys::default(),
            shared: HashMap::new(),
            import_refusals: HashSet::new(),
            holding_predicates: HashSet::new(),
            shared_chains: Vec::new(),
            shared_reached: HashMap::new(),
            checking: false,
            nested: false,
            enclosing: None,
            import_checks: HashMap::new(),
            errors: Vec::new(),
            method_copies: Vec::new(),
            const_values: HashMap::new(),
            const_compounds: HashMap::new(),
        }
    }

    /// Record `value`, which the `const` parameter `parameter` takes at `given`, by `binder`,
    /// the binder of the parameter's `let`: a literal, or a term over the parameters of a
    /// module checked alone, is what each predicate reading it holds in its place and what the
    /// parameter is known to be ([`settle_const_params`]), and a tuple, a record or a list is
    /// refused where a predicate reads it ([`compound_const_reads`]).
    fn record_const(
        &mut self,
        binder: &Name,
        value: &ConstTerm,
        parameter: &Parameter,
        given: Span,
    ) {
        match value {
            ConstTerm::Lit(_) => {
                self.const_values
                    .insert(binder.clone(), (value.clone(), given));
            }
            value if value.is_value() => {
                self.const_compounds.insert(
                    binder.clone(),
                    CompoundConst {
                        name: parameter.name.clone(),
                        value: value.clone(),
                        given,
                        declared: parameter.declared,
                    },
                );
            }
            // A term over the parameters of a module checked alone, which compares as written.
            value if crate::ccl::lower::nominal::predicate_holds(value) => {
                self.const_values
                    .insert(binder.clone(), (value.clone(), given));
            }
            // A tuple, a record or a list over those parameters, which no predicate holds:
            // a predicate reading it reads the parameter.
            _ => {}
        }
    }

    /// `error`, which the arguments of the copy holding its statement give rise to, labelled
    /// at the run whose copy that is, when there is one. Each copy of the statement raises
    /// it, and [`in_source_order`] merges them into one error with a label at each.
    fn at_enclosing_run(&self, error: LoweringError) -> LoweringError {
        match &self.enclosing {
            Some((path, statement)) => {
                error.with_related(*statement, format!("the run `{path}`, whose copy fails"))
            }
            None => error,
        }
    }

    /// Create each shared import in `sites` but one of the root's file, after the
    /// shared imports it reaches, and return their chains in the order created. A
    /// run's key holds the keys of the imports it passes, so the order is well
    /// founded.
    pub(super) fn shared_imports(
        &mut self,
        order: &[FileId],
        sites: &HashMap<SharedImport, (FileId, ImportSite)>,
        ctx: &mut LoweringContext,
    ) -> Vec<Expr> {
        let root = self.program.sources().root();
        let position: HashMap<FileId, usize> = order
            .iter()
            .enumerate()
            .map(|(i, file)| (*file, i))
            .collect();
        let mut in_order: Vec<&SharedImport> = sites.keys().collect();
        in_order
            .sort_by_key(|shared| (position.get(&sites[*shared].0).copied(), (*shared).clone()));
        let mut chains = Vec::new();
        for shared in in_order {
            if sites[shared].0 != root {
                self.ensure_shared_import(shared, sites, &mut chains, ctx);
            }
        }
        chains
    }

    /// Lower the module in `file` once, recording it, or `None` when it has no
    /// syntax tree or has errors of its own.
    pub(super) fn lower(&mut self, file: FileId, ctx: &mut LoweringContext) {
        let lowered = self.lower_once(file, ctx).map(Rc::new);
        self.lowered.insert(file, lowered);
    }

    pub(super) fn lower_once(
        &mut self,
        file: FileId,
        ctx: &mut LoweringContext,
    ) -> Option<LoweredModule> {
        let ast = self.program.ast(file)?;
        // The root's file, lowered as a module for `cambra check`, is named by
        // its file's stem.
        let sources = self.program.sources();
        let module = sources.module(file).cloned().unwrap_or_else(|| {
            let stem = std::path::Path::new(sources.path(file))
                .file_stem()
                .and_then(|stem| stem.to_str())
                .unwrap_or("main");
            ModulePath::new([SmolStr::from(stem)])
        });
        let scope = self.scope(ast, Some(module.clone()), ctx);
        ctx.begin_module(scope.clone());
        ctx.sites.add_module(module.segments(), &ast.body);
        let lowered = lower_module_body(ast, ctx);
        let sinks = std::mem::take(&mut ctx.declared_sinks);
        let run_checks = std::mem::take(&mut ctx.run_type_checks);
        let unimportable = sink_site(ast)
            .map(Unimportable::Io)
            .or_else(|| state_site(ast).map(Unimportable::State))
            .or(ctx.io_site.map(Unimportable::Io));
        let clean = lowered.errors.is_empty() && self.program.parsed_cleanly(file);
        self.errors.extend(lowered.errors);
        let chain = lowered.value.filter(|_| clean)?;
        let interface = Interface::of_lowered(
            module,
            ast,
            &chain,
            std::mem::take(&mut ctx.parameters),
            ctx,
            unimportable,
        );
        ctx.reached_methods.extend(interface.public_methods());
        Some(LoweredModule {
            chain,
            interface: Rc::new(interface),
            scope,
            sinks,
            run_checks,
            as_root: false,
        })
    }

    /// Whether the module in `file` can be imported for its statements: an
    /// imported module declares no `run`, since the import would reach the run's
    /// state (`docs/chl-spec.md`, "9.7 Importing asserts a shareable module"), and
    /// no statement but a value binding, a `def`, a type alias, an `import`, or
    /// `pass`. Each refusal is reported once, at the statement.
    pub(super) fn importable(&mut self, file: FileId) -> bool {
        let Some(ast) = self.program.ast(file) else {
            return false;
        };
        let refusals = library_statement_refusals(&ast.body);
        if refusals.is_empty() {
            return true;
        }
        if self.import_refusals.insert(file) {
            self.errors.extend(refusals);
        }
        false
    }

    /// The interface an import of the module in `file` reaches, or `None` when
    /// the module has errors of its own or an import may not hold its statements.
    pub(super) fn import_interface(&mut self, file: FileId) -> Option<Rc<Interface>> {
        // A module that performs IO or declares state is refused at each import
        // of it, for that reason alone (`module_scope`), whether or not it has
        // errors of its own.
        let Some(lowered) = self.lowered.get(&file).cloned().flatten() else {
            let ast = self.program.ast(file)?;
            let why = sink_site(ast)
                .map(Unimportable::Io)
                .or_else(|| state_site(ast).map(Unimportable::State))?;
            let module = self.program.sources().module(file)?.clone();
            return Some(Rc::new(Interface::unimportable(module, why)));
        };
        if lowered.interface.unimportable.is_some() {
            return Some(Rc::clone(&lowered.interface));
        }
        self.importable(file).then(|| Rc::clone(&lowered.interface))
    }

    /// Create the shared import `shared`, of those in `sites`, if it is not created
    /// yet, after each shared import it reaches: those its module imports and those
    /// its arguments name. Each chain is pushed onto `chains` once its own
    /// shared imports' are.
    pub(super) fn ensure_shared_import(
        &mut self,
        shared: &SharedImport,
        sites: &HashMap<SharedImport, (FileId, ImportSite)>,
        chains: &mut Vec<Expr>,
        ctx: &mut LoweringContext,
    ) {
        if self.shared.contains_key(shared) {
            return;
        }
        // Each shared import is created once, and a cycle among imports is refused
        // by loading, so the entry made here ends the recursion.
        self.shared.insert(shared.clone(), None);
        let (file, site) = &sites[shared];
        let mut reached: Vec<SharedImport> = shared
            .arguments
            .iter()
            .filter_map(|(_, argument)| match argument {
                KeyArgument::Module(passed) => Some(passed.clone()),
                KeyArgument::Lit(_) | KeyArgument::Type(_) => None,
            })
            .collect();
        if let Some(ast) = self.program.ast(*file) {
            reached.extend(
                ast.body
                    .iter()
                    .filter_map(|stmt| Some(self.imports.get(&stmt.span)?.shared.clone())),
            );
        }
        for reached in &reached {
            if sites.contains_key(reached) {
                self.ensure_shared_import(reached, sites, chains, ctx);
            }
        }
        self.shared_reached.insert(shared.clone(), reached);
        if let Some(chain) = self.shared_import(*file, shared.clone(), site, ctx) {
            // A copy no tree holds, which each check that reaches the shared import
            // copies again.
            let kept = chain.clone_preserving_ids();
            self.shared_chains.push((shared.clone(), kept));
            chains.push(chain);
        }
    }

    /// Create the shared import `shared` of the imported module in `file`, for the
    /// import `site`, recording the names it reaches, and return its chain.
    pub(super) fn shared_import(
        &mut self,
        file: FileId,
        shared: SharedImport,
        site: &ImportSite,
        ctx: &mut LoweringContext,
    ) -> Option<Expr> {
        let interface = self.import_interface(file);
        let created = interface
            .filter(|interface| interface.unimportable.is_none())
            .and_then(|_| {
                let home = Home::Import(shared.clone());
                self.create(
                    file,
                    Some(home),
                    None,
                    Supplied::Import(&shared, site),
                    &[],
                    ctx,
                )
            });
        let (chain, names) = match created {
            Some(created) => (Some(created.chain), Some(Rc::new(created.names))),
            None => (None, None),
        };
        self.shared.insert(shared, names);
        chain
    }

    /// Create a run of the module in `file` with `home` as its members' home:
    /// a shared import, with no `run` statement, or the run at the run path and
    /// `run` statement `place`, with the arguments `supplied`. `None` when the
    /// module has no lowering.
    ///
    /// Its chain is a copy of the module's. Each parameter with an argument
    /// reads it ([`argument_name`]), and one with neither an argument nor a
    /// default is an error. A shared import's arguments are constants, bound at
    /// the head of its chain at their parameters' types, so a mismatch is the
    /// argument's error. A nested run raises none of these ([`Self::nested`]).
    /// Each run it declares is created in turn and put in place
    /// ([`Self::expand_runs`]), nested. It is uniquified with a scope that maps
    /// each name spelled through a qualifier to the binder in the qualifier's
    /// run, and each `use` name of an import to its member's binder. A run
    /// registers the sinks its module declares, under its run path.
    pub(super) fn create(
        &mut self,
        file: FileId,
        home: Option<Home>,
        place: Option<(RunPath, Span)>,
        supplied: Supplied,
        given_consts: &[(ConstParam, ConstTerm)],
        ctx: &mut LoweringContext,
    ) -> Option<Created> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        let raised = self.errors.len();
        // The first copy of a module in a tree holds the module's own predicates, which
        // a nominal type's declaration shares, and each later copy copies them.
        let first = self.holding_predicates.insert(file);
        let mut chain = {
            let _copy = crate::ccl::provenance::copy_frame("link.run");
            let mut chain = lowered.chain.clone();
            if !first {
                copy_predicates(&mut chain, &mut HashMap::new());
            }
            chain
        };
        let path = place
            .as_ref()
            .map(|(path, _)| path.clone())
            .unwrap_or_default();
        let prefix = match supplied {
            Supplied::Run(..) => place
                .as_ref()
                .and_then(|(path, _)| path.last())
                .expect("a run has a name")
                .to_string(),
            Supplied::Import(shared, _) => shared.to_string(),
        };
        let own = self.shared_names(&lowered.scope);
        let mut modules: HashMap<SmolStr, Rc<HashMap<QualifiedName, Name>>> = HashMap::new();
        // A type parameter's default is its module's own type, so it takes the
        // run's names. An argument is its declaring module's, so it replaces the
        // parameter once the run is uniquified, and the declaring module's
        // `let type` of it resolves its refinements where it is written.
        let given = match &supplied {
            Supplied::Run(.., types) => types,
            Supplied::Import(_, site) => &site.types,
        };
        let mut defaults = Arguments::default();
        let mut arguments = Arguments::default();
        for parameter in &lowered.interface.parameters {
            if let ParameterKind::Type { param, default, .. } = &parameter.kind {
                if let Some(argument) = given.get(&QualifiedName::new(parameter.name.clone())) {
                    arguments.types.insert(param.id, argument.clone());
                    continue;
                }
                if let Some(default) = default {
                    let mut default = default.clone();
                    substitute(&mut default, &defaults);
                    defaults.types.insert(param.id, default);
                    continue;
                }
            } else if let Some(ty) = parameter.module() {
                // Each abstract type member takes the argument's member, or,
                // with no argument, the default's.
                for (member, param) in
                    abstract_members(&QualifiedName::new(parameter.name.clone()), ty)
                {
                    if let Some(argument) = given.get(&member) {
                        arguments.types.insert(param.id, argument.clone());
                    } else if let Some(default) = parameter.default_type(&member) {
                        defaults.types.insert(param.id, default.clone());
                    } else if let (Supplied::Run(_, modules, _), Some((_, statement))) =
                        (&supplied, &place)
                        && modules
                            .iter()
                            .any(|module| module.parameter == parameter.name)
                    {
                        // A run's module argument declared below its statement
                        // was not known where its type arguments were lowered.
                        self.errors.push(
                            LoweringError::unsupported(
                                *statement,
                                format!(
                                    "the argument for `{}` is declared below this statement, so \
                                     the type member `{member}` it gives is not known here",
                                    parameter.name
                                ),
                            )
                            .with_related(parameter.declared, "the parameter"),
                        );
                    }
                }
                let argument = match &supplied {
                    Supplied::Run(_, arguments, _) => arguments
                        .iter()
                        .find(|argument| argument.parameter == parameter.name)
                        .map(|argument| (argument.names.clone(), argument.span)),
                    // A shared import that failed to be created has no names.
                    Supplied::Import(_, site) => match site.arguments.get(&parameter.name) {
                        Some((span, KeyArgument::Module(passed))) => {
                            Some((self.shared.get(passed).cloned().flatten(), *span))
                        }
                        Some((span, KeyArgument::Lit(_))) => {
                            self.errors
                                .extend(parameter.mismatched(false, *span, IMPORT_MODULE));
                            continue;
                        }
                        Some((_, KeyArgument::Type(_))) => {
                            unreachable!("a type argument is for a capitalized parameter")
                        }
                        None => None,
                    },
                }
                .or_else(|| {
                    let default = parameter.module_default()?;
                    Some((
                        Some(Rc::new(names_under(&own, default))),
                        parameter.declared,
                    ))
                });
                if let Some((names, span)) = argument {
                    // An argument whose module has errors of its own binds
                    // nothing, and reports nothing more: its errors account for
                    // the run.
                    let Some(names) = names else {
                        continue;
                    };
                    let at = (span, parameter.declared);
                    chain = self.bind_module_parameter(chain, &parameter.name, ty, &names, at, ctx);
                    modules.insert(parameter.name.clone(), names);
                    continue;
                }
            } else {
                let given = match &supplied {
                    Supplied::Run(arguments, ..) => arguments.contains(&parameter.name),
                    Supplied::Import(_, site) => match site.arguments.get(&parameter.name) {
                        Some((_, KeyArgument::Lit(_))) => true,
                        Some((_, KeyArgument::Type(_))) => {
                            unreachable!("a type argument is for a capitalized parameter")
                        }
                        Some((span, KeyArgument::Module(_))) => {
                            self.errors
                                .extend(parameter.mismatched(true, *span, IMPORT_MODULE));
                            continue;
                        }
                        None => false,
                    },
                };
                if given {
                    let argument = ctx.tag_image(
                        Expr::var(argument_name(
                            &prefix,
                            &QualifiedName::new(parameter.name.clone()),
                        )),
                        parameter.declared,
                    );
                    read_argument(&mut chain, &parameter.name, argument);
                    continue;
                }
            }
            if parameter.default {
                continue;
            }
            let error = match (&place, &supplied) {
                (Some((path, statement)), _) => LoweringError::unsupported(
                    *statement,
                    format!(
                        "the run `{path}` passes no argument for the parameter `{}`, which has \
                         no default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Import(_, site)) => LoweringError::unsupported(
                    site.statement,
                    format!(
                        "this import passes no argument for the parameter `{}`, which has no \
                         default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Run(..)) => unreachable!("a run has a `run` statement"),
            };
            self.errors
                .push(error.with_related(parameter.declared, "the parameter"));
        }
        if let Supplied::Import(_, site) = &supplied {
            let mut arguments: Vec<_> = site
                .arguments
                .iter()
                .filter_map(|(parameter, (span, argument))| match argument {
                    KeyArgument::Lit(value) => Some((parameter, (span, value))),
                    KeyArgument::Module(_) | KeyArgument::Type(_) => None,
                })
                .collect();
            arguments.sort_by(|l, r| l.0.cmp(r.0));
            for (parameter, (span, value)) in arguments.into_iter().rev() {
                let ty = lowered
                    .interface
                    .parameters
                    .iter()
                    .find(|p| &p.name == parameter)
                    .and_then(|p| p.annotation().cloned());
                let value = ctx.tag_image(Expr::lit(value.clone()), *span);
                let bound = argument_name(&prefix, &QualifiedName::new(parameter.clone()));
                let bound = match ty {
                    Some(ty) => Expr::let_bind_annotated(bound, value, chain, ty),
                    None => Expr::let_bind(bound, value, chain),
                };
                chain = ctx.tag_image(bound, *span);
            }
        }
        if self.nested {
            self.errors.truncate(raised);
        }
        // Each `const` parameter takes the term its run passes, or the literal its import
        // passes or its default, over the parameters above it. A run's statement already
        // holds each default it takes (`run_consts`), so an argument with no value there is
        // reported where the run is expanded, and its default is not tried again.
        let statement = match (&place, &supplied) {
            (Some((_, statement)), _) => *statement,
            (None, Supplied::Import(_, site)) => site.statement,
            (None, Supplied::Run(..)) => unreachable!("a run has a `run` statement"),
        };
        for parameter in &lowered.interface.parameters {
            let Some(constant) = parameter.constant() else {
                continue;
            };
            let imported = match &supplied {
                Supplied::Import(_, site) => match site.arguments.get(&parameter.name) {
                    Some((_, KeyArgument::Lit(value))) => Some(ConstTerm::Lit(value.clone())),
                    _ => None,
                },
                Supplied::Run(..) => None,
            };
            let term = given_consts
                .iter()
                .find(|(param, _)| param.id == constant.param.id)
                .map(|(_, term)| Ok(term.clone()))
                .or(imported.map(Ok))
                .or_else(|| {
                    let Supplied::Import(..) = &supplied else {
                        return None;
                    };
                    let default = constant.default.as_ref()?;
                    Some(default.substituted(&arguments.consts))
                });
            match term {
                Some(Ok(term)) => {
                    arguments.consts.insert(constant.param.id, term);
                }
                Some(Err(no_value)) => {
                    let error = LoweringError::unsupported(
                        statement,
                        format!(
                            "the default of `{}` has no value here: {}",
                            parameter.name, no_value.0
                        ),
                    )
                    .with_related(parameter.declared, "the parameter");
                    self.errors.push(self.at_enclosing_run(error));
                }
                // A parameter with no argument and no default is reported above, and a
                // run's argument with no value where the run is expanded.
                None => {}
            }
        }
        substitute_in(&mut chain, &defaults);
        // A route takes the address its run gives it. A module's check keeps the name the
        // module's chain gives its source, which it reads the requests' type off.
        let declared = if self.checking {
            Vec::new()
        } else {
            sinks_at(
                &lowered.sinks,
                &arguments.consts,
                &mut chain,
                statement,
                &mut self.errors,
            )
        };
        let mut qualified = own;
        let outer = std::mem::replace(&mut self.nested, true);
        let enclosing = std::mem::replace(&mut self.enclosing, place.clone());
        let copies = self.method_copies.len();
        let chain = self.expand_runs(
            chain,
            &path,
            &mut qualified,
            &modules,
            &arguments.consts,
            ctx,
        );
        self.nested = outer;
        self.enclosing = enclosing;
        // A copy that a run this one declares recorded reaches this module's type
        // parameters wherever that run's arguments name them, so it takes this run's
        // arguments as its chain does.
        for copy in &mut self.method_copies[copies..] {
            substitute_decl(&mut copy.decl, &defaults);
            substitute_decl(&mut copy.decl, &arguments);
        }
        let (sinks, refused) = match &place {
            Some(place) if !self.checking => ctx.register_sinks(&declared, Some(place)),
            _ => (Vec::new(), Vec::new()),
        };
        if !self.checking
            && let Some(home) = &home
        {
            if let Some((path, statement)) = &place {
                let label = format!("the run `{path}`, whose copy fails");
                ctx.run_sites
                    .statements
                    .entry(home.clone())
                    .or_default()
                    .push((*statement, label));
            }
            ctx.run_sites
                .by_file
                .entry(file)
                .or_default()
                .push(home.clone());
        }
        self.errors.extend(refused);
        let scope = use_names(&lowered.scope, qualified);
        let mut uniquified = uniquify::run_in(chain, &raw_scope(&scope), home.clone());
        substitute_in(&mut uniquified, &arguments);
        let mut names = scope;
        let (spine, _) = spine(&uniquified);
        for name in spine {
            // The spine also runs through the chain of each run this one declares,
            // whose binders carry that run's home.
            if name.home() == home.as_ref() {
                names.insert(QualifiedName::new(name.base()), name.clone());
                if let Some(copy) = method_copy(&lowered.interface, name, &defaults, &arguments) {
                    self.method_copies.push(copy);
                }
            }
        }
        for parameter in &lowered.interface.parameters {
            if let Some(constant) = parameter.constant()
                && let Some(value) = arguments.consts.get(&constant.param.id)
                && let Some(binder) = names.get(&QualifiedName::new(parameter.name.clone()))
            {
                self.record_const(binder, value, parameter, statement);
            }
        }
        // A member bound to a module reaches what that module does, so a Module
        // type naming it, `shop: Module{k: …}`, finds its members under it.
        for (name, member) in &lowered.interface.modules {
            let reached = match &member.view {
                Some(view) => view_names(view, &names),
                None => names_under(&names, &member.name),
            };
            for (spelling, binder) in reached {
                names.insert(QualifiedName::new(name.clone()).then(&spelling), binder);
            }
        }
        // Each sink the run declares is read at the program's tail through the
        // binder its chain minted.
        for (key, binder) in sinks {
            let name = names
                .get(&QualifiedName::new(binder.as_str()))
                .unwrap_or_else(|| panic!("the run `{path}`'s chain binds its sink `{binder}`"));
            ctx.run_sink_names.insert(key, name.clone());
        }
        Some(Created {
            chain: uniquified,
            names,
        })
    }

    /// `chain`, a copy of a module's chain, with each `let` the Module-typed
    /// parameter `parameter` of type `ty` binds bound to its member among
    /// `names`, what the module passed at `at.0` reaches. A member it lacks is an
    /// error at the argument, with a note at the parameter, `at.1`.
    pub(super) fn bind_module_parameter(
        &mut self,
        mut chain: Expr,
        parameter: &str,
        ty: &ModuleType,
        names: &HashMap<QualifiedName, Name>,
        at: (Span, Span),
        ctx: &mut LoweringContext,
    ) -> Expr {
        let (span, declared) = at;
        let parameter = QualifiedName::new(parameter);
        let mut lets = Vec::new();
        ModuleView::of(&parameter, ty, &mut lets);
        for (binder, _) in lets {
            let entry = binder
                .strip_prefix(&parameter)
                .expect("a parameter's entries are spelled under it");
            match names.get(&entry) {
                Some(member) => rebind_entry(&mut chain, &binder, member.clone(), span, ctx),
                None => self.errors.push(
                    LoweringError::unsupported(
                        span,
                        format!(
                            "this module does not fit the parameter's Module type: it has no \
                             public member `{entry}`"
                        ),
                    )
                    .with_related(declared, "the parameter"),
                ),
            }
        }
        chain
    }

    /// `expr`, a module's chain, with each [`TypedExprNode::Run`] on its spine
    /// replaced by the run it declares, at a run path under `path`, around the
    /// rest of the module. Each name a created run reaches is recorded in
    /// `qualified`, spelled through its run name. Each type argument the run
    /// takes is a `let type` where the `Run` stood, which resolves the
    /// argument's refinements in the declaring module's scope.
    pub(super) fn expand_runs(
        &mut self,
        mut expr: Expr,
        path: &RunPath,
        qualified: &mut HashMap<QualifiedName, Name>,
        modules: &HashMap<SmolStr, Rc<HashMap<QualifiedName, Name>>>,
        own_consts: &HashMap<TypeParamId, ConstTerm>,
        ctx: &mut LoweringContext,
    ) -> Expr {
        if matches!(expr.node, TypedExprNode::Run { .. }) {
            let TypedExprNode::Run {
                name,
                module,
                statement,
                arguments,
                modules: passed,
                types,
                consts,
                body,
            } = expr.node
            else {
                unreachable!("matched a `Run` above");
            };
            // Each `const` argument is a term over the declaring module's `const`
            // parameters, which take this run's values.
            let consts: Vec<(ConstParam, ConstTerm)> = consts
                .into_iter()
                .filter_map(|(param, term)| match term.substituted(own_consts) {
                    Ok(term) => Some((param, term)),
                    Err(no_value) => {
                        let error = LoweringError::unsupported(
                            statement,
                            format!(
                                "`{}` has no value at this run: {}",
                                param.spelling, no_value.0
                            ),
                        );
                        self.errors.push(self.at_enclosing_run(error));
                        None
                    }
                })
                .collect();
            let passed = passed
                .into_iter()
                .map(|(parameter, spelling, span)| PassedModule {
                    parameter,
                    names: spelling
                        .map(|spelling| Rc::new(module_names(&spelling, qualified, modules))),
                    span,
                })
                .collect();
            let given = types
                .iter()
                .map(|(parameter, _, ty)| (parameter.clone(), ty.clone()))
                .collect();
            let run_path = path.child(name.clone());
            let created = self.program.file_of(&module).and_then(|file| {
                let home = Home::Run(run_path.clone());
                let place = Some((run_path, statement));
                self.create(
                    file,
                    Some(home),
                    place,
                    Supplied::Run(&arguments, passed, given),
                    &consts,
                    ctx,
                )
            });
            let run = match created {
                Some(mut created) => {
                    // The run's places are this run's ([`crate::ccl::site`]). A run nested in
                    // it has stamped its own deeper path already.
                    in_run(&mut created.chain, &path.child(name.clone()));
                    // The rest of the module, below the run, reaches it.
                    for (spelling, binder) in created.names {
                        qualified.insert(QualifiedName::new(name.clone()).then(&spelling), binder);
                    }
                    let body = self.expand_runs(*body, path, qualified, modules, own_consts, ctx);
                    fill_module_body(created.chain, body)
                }
                None => self.expand_runs(*body, path, qualified, modules, own_consts, ctx),
            };
            return types
                .into_iter()
                .rev()
                .fold(run, |body, (parameter, span, ty)| {
                    let bound = argument_name(&name, &parameter);
                    let bound = Expr::let_type(bound.base(), AliasType::Type(ty), body);
                    ctx.tag_image(bound, span)
                });
        }
        // The rest of the spine stays in place, so no node is minted.
        if let Some(body) = spine_body_mut(&mut expr) {
            let rest = std::mem::take(body);
            *body = self.expand_runs(rest, path, qualified, modules, own_consts, ctx);
        }
        expr
    }

    /// Each name the shared imports of `scope`'s import names reach, spelled
    /// through the import name.
    pub(super) fn shared_names(&self, scope: &ModuleScope) -> HashMap<QualifiedName, Name> {
        let mut qualified = HashMap::new();
        for (qualifier, reached) in &scope.qualifiers {
            let Some(Some(names)) = reached
                .shared
                .as_ref()
                .and_then(|shared| self.shared.get(shared))
            else {
                continue;
            };
            for (spelling, binder) in names.iter() {
                qualified.insert(
                    QualifiedName::new(qualifier.clone()).then(spelling),
                    binder.clone(),
                );
            }
        }
        qualified
    }

    /// The interface each `import` and `run` statement of `module` reaches, by
    /// the statement, or `None` where there is none.
    pub(super) fn interfaces(
        &mut self,
        module: &ChlModule,
    ) -> HashMap<Span, Option<Rc<Interface>>> {
        let mut interfaces = HashMap::new();
        for stmt in &module.body {
            let path = match &stmt.node {
                ChlStmt::Import { path, .. } | ChlStmt::Run { path, .. } => path,
                _ => continue,
            };
            let Some(file) = path.to_path().and_then(|path| self.program.file_of(&path)) else {
                continue;
            };
            let interface = match &stmt.node {
                ChlStmt::Import { .. } => self.import_interface(file),
                _ => self
                    .lowered
                    .get(&file)
                    .cloned()
                    .flatten()
                    .map(|lowered| Rc::clone(&lowered.interface)),
            };
            interfaces.insert(stmt.span, interface);
        }
        interfaces
    }

    /// The scope `module` lowers in ([`module_scope`]).
    pub(super) fn scope(
        &mut self,
        module: &ChlModule,
        labels: Option<ModulePath>,
        ctx: &LoweringContext,
    ) -> ModuleScope {
        let interfaces = self.interfaces(module);
        module_scope(
            module,
            labels,
            self.program,
            &interfaces,
            &self.imports,
            ctx,
            &mut self.errors,
        )
    }
}

/// What the view `view` reaches among `names`, a run's names: each value under
/// its entry's name, at any depth, `log::events` for a module entry `log`.
pub(super) fn view_names(
    view: &ModuleView,
    names: &HashMap<QualifiedName, Name>,
) -> HashMap<QualifiedName, Name> {
    let mut reached = HashMap::new();
    for (entry, spelling) in &view.values {
        if let Some(binder) = names.get(spelling) {
            reached.insert(QualifiedName::new(entry.clone()), binder.clone());
        }
    }
    for (entry, inner) in &view.modules {
        for (spelling, binder) in view_names(inner, names) {
            reached.insert(QualifiedName::new(entry.clone()).then(&spelling), binder);
        }
    }
    reached
}

/// The names under `prefix` in `names`, each without it: what the module
/// spelled `prefix` reaches, `count` for `c::count`.
pub(super) fn names_under(
    names: &HashMap<QualifiedName, Name>,
    prefix: &QualifiedName,
) -> HashMap<QualifiedName, Name> {
    names
        .iter()
        .filter_map(|(spelling, name)| Some((spelling.strip_prefix(prefix)?, name.clone())))
        .collect()
}

/// The names the module spelled `spelling` reaches, in a run whose names are
/// `qualified` and whose Module-typed parameters take the modules `modules`.
/// A spelling through a parameter, `audit` or `audit::log`, reaches what the
/// parameter's argument does.
pub(super) fn module_names(
    spelling: &QualifiedName,
    qualified: &HashMap<QualifiedName, Name>,
    modules: &HashMap<SmolStr, Rc<HashMap<QualifiedName, Name>>>,
) -> HashMap<QualifiedName, Name> {
    let (first, rest) = spelling
        .split_first()
        .expect("a module's spelling has a segment");
    match modules.get(first) {
        Some(names) if rest == QualifiedName::default() => (**names).clone(),
        Some(names) => names_under(names, &rest),
        None => names_under(qualified, spelling),
    }
}

/// The scope a run of the module that lowered in `scope` is uniquified in:
/// `qualified`, each name spelled through a qualifier, and each `use` name of an
/// import, mapped to its member's binder. A run's `use` names are `let`s at its
/// statement ([`LoweringContext::take_run`]).
pub(super) fn use_names(
    scope: &ModuleScope,
    qualified: HashMap<QualifiedName, Name>,
) -> HashMap<QualifiedName, Name> {
    let mut names = qualified;
    for (bound, used) in &scope.uses {
        if used.run.is_some() {
            continue;
        }
        let Reached::Value(Some(reference)) = &used.reached else {
            continue;
        };
        // An import whose arguments are in error reaches no shared import, and its `use` names
        // reach nothing: the error at the import accounts for them.
        let qualifier = reference.name.segments().first();
        if !names
            .keys()
            .any(|name| name.segments().first() == qualifier)
        {
            continue;
        }
        let binder = names.get(&reference.name).cloned();
        debug_assert!(
            binder.is_some(),
            "the `use` name `{bound}` reached `{}` through an interface, so its qualifier's \
             run holds it",
            reference.name
        );
        if let Some(binder) = binder {
            names.insert(QualifiedName::new(bound.clone()), binder);
        }
    }
    names
}
