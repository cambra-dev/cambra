//! The source-level name-resolution index over the parsed CHL AST.
//!
//! This is the [`NameBinderIndex`] — the source-level answer to lexical name
//! questions, enumerated onto the wire as the payload's `definitions` (use →
//! binder) and the name half of its `scopes` (the binders visible in a region).
//! Unlike [`SpanIndex`], which projects the *typed IR* back onto source spans,
//! this index resolves purely over the **surface AST** ([`Module`]).
//!
//! [`SpanIndex`]: crate::inspector_model::SpanIndex
//!
//! # Why source-level
//!
//! Name resolution is a *source-language* lexical question, and lowering has
//! already destroyed the **name** by the time any pass could resolve it:
//! `uncurry_params` rewrites a multi-param reference `Var(p)` to the projection
//! `__arg_tuple_N ▷ .i` **before** uniquify runs, so nothing downstream binds or
//! mentions `p` and a uniquify/IR-based binder table has no `Var(p)` to rename.
//! The occurrence's *span* survives — substitution is root-carry — so what is
//! lost is the correspondence from a use to its binder, not the position. The
//! surface AST still has `p`/`q` with their
//! [`Param.name_span`](crate::chl_parser::ast::Param::name_span), so resolving
//! over it is lossless and matches the standard LSP approach.
//!
//! # Scoping model
//!
//! The walk mirrors CHL's actual scoping, which lowering realizes as nested
//! `let`s (`x = 1; x = 2` → `let x = 1 in let x = 2 in …`), i.e. **sequential
//! let-style**: a binder is visible only *after* its binding site within its
//! scope, and an inner binder shadows an outer one of the same name (innermost
//! wins). See `ccl/lower.rs`'s "Name uniqueness" note. Binder sites:
//!
//! * top-level + block assignments (`Assign`/`AnnAssign`/`AugAssign`/`Define`
//!   targets, including `Tuple` destructuring),
//! * `def` name + its [`Param`]s, `lambda` params,
//! * `for`-loop targets, comprehension `for`-clause targets.
//!
//! Uses are [`Expr::Name`] occurrences.

use crate::chl_parser::ast::{
    AssignTarget, Comprehension, Expr, IfBranch, MatchArm, MatchPattern, Module, Param,
    PayloadPattern, Span, Spanned, Stmt, VariantPayload,
};
use smol_str::SmolStr;

/// A name binding visible at some position: the bound name and the source span
/// of its binding site (its definition span).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// The bound name.
    pub name: SmolStr,
    /// The source span of the binder — the `defSpan` a payload row carries. For
    /// a parameter this is its [`Param.name_span`](crate::chl_parser::ast::Param::name_span);
    /// for an assignment it is the target's span; for a `def` it is the name's
    /// span.
    pub def_span: Span,
}

/// One resolved use→binder pair, the enumeration unit behind the
/// `/api/snapshot` `definitions` array: a `Name` use, the binder it resolves
/// to, and the bound name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition {
    /// The use-site span.
    pub use_span: Span,
    /// The binder's source span — where the use is defined.
    pub def_span: Span,
    /// The bound name.
    pub name: SmolStr,
}

/// One scope region, the enumeration unit behind the `/api/snapshot` `scopes`
/// array: a binder-bearing span plus the binders visible inside it. The type
/// join (each binding's `type`) is added by the snapshot assembler, which has
/// the [`SpanIndex`](crate::inspector_model::SpanIndex).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopeRegion {
    /// The source span of the region.
    pub span: Span,
    /// The binders visible inside it, outermost → innermost.
    pub bindings: Vec<Binding>,
}

/// Source-level lexical name resolution over the parsed CHL [`Module`].
///
/// Built once over the surface AST ([`build`](Self::build)); enumerated by
/// [`definitions`](Self::definitions) (every resolved use→binder pair) and
/// [`scopes`](Self::scopes) (every binder-bearing region with the names visible
/// inside it).
///
/// # Resolution by span
///
/// Every handle the enumerations carry is a source [`Span`]: a use span, a
/// binder's def-span, a region's span. Both enumerations walk the AST with the
/// same scope bookkeeping, resolving each use against the binder stack live at
/// it; an unbound use contributes no row. The index owns its copy of the
/// `Module`, and each enumeration re-runs the walk rather than caching a
/// span→binder map with shadowing.
#[derive(Clone, Debug)]
pub struct NameBinderIndex {
    module: Module,
}

/// One lexical binder in scope during a walk: its name, def-span, and the byte
/// offset *after which* it becomes visible (sequential let-style — a binder is
/// not visible to its own RHS, only to statements/expressions that follow it in
/// its scope).
#[derive(Clone, Copy, Debug)]
struct Scoped<'a> {
    name: &'a SmolStr,
    def_span: Span,
    /// The binder is visible at a position `pos` iff `pos >= visible_from`. For
    /// statement bindings this is the end of the binding statement (the binder
    /// is in scope for everything after it); for parameters and loop/comp
    /// targets it is the start of the body the binder scopes over.
    visible_from: usize,
}

impl NameBinderIndex {
    /// Build the index over the parsed CHL surface AST.
    pub fn build(module: &Module) -> Self {
        Self {
            module: module.clone(),
        }
    }

    /// Enumerate every resolved use→binder pair in the module — the data behind
    /// the `/api/snapshot` `definitions` array. Each entry is a `Name` use that
    /// resolves to a visible binder, paired with that binder's def-span and the
    /// bound name; unbound uses (which would resolve to `None`) are skipped.
    ///
    /// Pure: re-walks the AST, resolving each use against the binder stack live
    /// at it — the innermost binder of that name whose binding site precedes the
    /// use (sequential let-style shadowing). Order is the source pre-order of
    /// the uses.
    pub fn definitions(&self) -> Vec<Definition> {
        let mut out: Vec<Definition> = Vec::new();
        let mut scopes: Vec<Scoped> = Vec::new();
        walk_module(&self.module, &mut scopes, &mut |ev| {
            if let Event::Use { name, span, scopes } = ev
                && let Some(def_span) = resolve(name, span, scopes)
            {
                out.push(Definition {
                    use_span: span,
                    def_span,
                    name: name.clone(),
                });
            }
        });
        out
    }

    /// Enumerate every binder-introducing scope region in the module and the
    /// binders visible inside it — the data behind the `/api/snapshot` `scopes`
    /// array (the type join is the caller's, since it needs the `SpanIndex`).
    ///
    /// A region is emitted per statement and per expression, minus those whose
    /// visible-binder set is empty (an empty `scopes` row carries nothing). The
    /// binders are the ones visible at the region's start, outermost →
    /// innermost. Regions therefore repeat where a statement and its expression
    /// share a span; `src/inspector_model/design.md`, "Decided, not yet built"
    /// carries the deduplication.
    ///
    /// Pure; re-walks the AST. Regions may nest and overlap (an inner body's
    /// region is a sub-span of its enclosing sequence's), mirroring the lexical
    /// structure — the schema's `scopes` is a flat list of such regions, not a
    /// tree.
    pub fn scopes(&self) -> Vec<ScopeRegion> {
        let mut out: Vec<ScopeRegion> = Vec::new();
        let mut scopes: Vec<Scoped> = Vec::new();
        walk_module(&self.module, &mut scopes, &mut |ev| {
            if let Event::Scope { span, scopes } = ev {
                let bindings = visible_bindings(scopes, span.start);
                if !bindings.is_empty() {
                    out.push(ScopeRegion { span, bindings });
                }
            }
        });
        out
    }
}

/// An event surfaced during the AST walk: an [`Event::Use`] at every `Name`
/// occurrence and an [`Event::Scope`] at every statement and every expression,
/// carrying the binder stack live there. Scope events are that dense because
/// every region a name is visible in ships as a `scopes` row.
///
/// Both borrows are tied to the single lifetime `'s` of the in-progress walk;
/// the visitor (a higher-ranked `FnMut`) may inspect them only for the duration
/// of the call.
enum Event<'s> {
    /// A `Name` use occurrence.
    Use {
        name: &'s SmolStr,
        span: Span,
        scopes: &'s [Scoped<'s>],
    },
    /// A binder-bearing region and the binder stack visible inside it.
    Scope {
        span: Span,
        scopes: &'s [Scoped<'s>],
    },
}

/// Resolve `name` used at `use_span` against the visible binders: innermost
/// (last-pushed) binder of that name whose `visible_from` precedes the use.
fn resolve(name: &SmolStr, use_span: Span, in_scope: &[Scoped]) -> Option<Span> {
    in_scope
        .iter()
        .rev()
        .find(|b| b.name == name && use_span.start >= b.visible_from)
        .map(|b| b.def_span)
}

/// The set of visible bindings at `pos`, innermost shadowing outermost,
/// returned outermost → innermost with shadowed names removed.
fn visible_bindings(in_scope: &[Scoped], pos: usize) -> Vec<Binding> {
    use std::collections::HashSet;
    // Walk innermost → outermost so the first occurrence of a name is the one
    // that wins; collect into the natural (outermost→innermost) order after.
    let mut seen: HashSet<&SmolStr> = HashSet::new();
    let mut innermost_first: Vec<Binding> = Vec::new();
    for b in in_scope.iter().rev() {
        if pos < b.visible_from {
            continue;
        }
        if seen.insert(b.name) {
            innermost_first.push(Binding {
                name: b.name.clone(),
                def_span: b.def_span,
            });
        }
    }
    innermost_first.reverse();
    innermost_first
}

/// Callback invoked for every [`Event`] surfaced by the walk. The higher-ranked
/// bound lets each call hand the closure a borrow valid only for that call.
type Visitor<'v> = dyn for<'s> FnMut(Event<'s>) + 'v;

/// Walk a whole module: a top-level statement sequence is a single sequential
/// scope.
fn walk_module<'a>(module: &'a Module, scopes: &mut Vec<Scoped<'a>>, visit: &mut Visitor<'_>) {
    walk_stmt_seq(&module.body, scopes, visit);
}

/// Walk a statement sequence with sequential let-style scoping: each binding
/// statement's binders become visible to everything *after* it (their
/// `visible_from` is the binding statement's end), while a use inside the
/// binding's own RHS sees only the binders that preceded it.
fn walk_stmt_seq<'a>(
    stmts: &'a [Spanned<Stmt>],
    scopes: &mut Vec<Scoped<'a>>,
    visit: &mut Visitor<'_>,
) {
    let base = scopes.len();
    for stmt in stmts {
        walk_stmt(stmt, scopes, visit);
    }
    // Bindings introduced by this sequence go out of scope at its end.
    scopes.truncate(base);
}

fn walk_stmt<'a>(stmt: &'a Spanned<Stmt>, scopes: &mut Vec<Scoped<'a>>, visit: &mut Visitor<'_>) {
    let stmt_end = stmt.span.end;
    // Surface the scope live *at* this statement (binders preceding it in the
    // sequence), so a `bindings_in_scope` position landing on it captures them.
    visit(Event::Scope {
        span: stmt.span,
        scopes,
    });
    match &stmt.node {
        Stmt::Expr(e) => walk_expr(e, scopes, visit),

        // Assignment family: the RHS is evaluated in the *outer* scope (binders
        // not yet visible), then the target's names become visible from the end
        // of the statement onward (sequential let-style; matches lowering's
        // nested-`let` shape and shadowing semantics).
        Stmt::Assign { target, value } => {
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes);
        }
        Stmt::AnnAssign {
            target,
            annotation,
            value,
        } => {
            walk_expr(&annotation.ty, scopes, visit);
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes);
        }
        Stmt::AugAssign { target, value, .. } => {
            // `x += v` reads the prior `x` in the RHS and rebinds it after.
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes);
        }
        Stmt::Define { target, value } => {
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes);
        }

        Stmt::If {
            branches,
            else_body,
        } => {
            for IfBranch { cond, body } in branches {
                walk_expr(cond, scopes, visit);
                walk_stmt_seq(body, scopes, visit);
            }
            if let Some(else_body) = else_body {
                walk_stmt_seq(else_body, scopes, visit);
            }
        }

        // `match scrutinee: case `tag(v): body …` — the scrutinee is evaluated in
        // the outer scope; an arm's payload binder is visible only inside that
        // arm's body. The arms are siblings, so each one's binder is popped
        // before the next is walked.
        Stmt::Match { scrutinee, arms } => {
            walk_expr(scrutinee, scopes, visit);
            for MatchArm { pattern, body } in arms {
                let base = scopes.len();
                let body_start = body.first().map(|s| s.span.start).unwrap_or(stmt_end);
                // Only `` case `tag(v): `` binds; `_` is the explicit
                // unused-binder spelling and a bare `` case `tag: `` says the tag
                // carries no payload, so neither names anything the body can use.
                if let Some(MatchPattern {
                    payload: PayloadPattern::Named(name, name_span),
                    ..
                }) = pattern
                {
                    scopes.push(Scoped {
                        name,
                        def_span: *name_span,
                        visible_from: body_start,
                    });
                }
                walk_stmt_seq(body, scopes, visit);
                scopes.truncate(base);
            }
        }

        // `for target in iter: body` — `iter` is evaluated in the outer scope;
        // `target` is bound across the loop body (visible from the body onward).
        Stmt::For { target, iter, body } => {
            walk_expr(iter, scopes, visit);
            let base = scopes.len();
            let body_start = body.first().map(|s| s.span.start).unwrap_or(stmt_end);
            bind_target(target, body_start, scopes);
            walk_stmt_seq(body, scopes, visit);
            scopes.truncate(base);
        }

        // `def name(params): body` — `name` is visible after the def (recursion
        // is not modeled; matches lowering's `let name = λ… in …`). `params`
        // are visible only inside the body.
        Stmt::FunctionDef {
            name,
            name_span,
            params,
            output,
            body,
        } => {
            // The output-type annotation is a type expression in the *enclosing*
            // scope: it is written before the body opens, so the params are not
            // visible in it.
            if let Some(output) = output {
                walk_expr(output, scopes, visit);
            }
            // The def's name is bound in the enclosing scope from the statement
            // end onward, and its def-span is the name's own.
            scopes.push(Scoped {
                name,
                def_span: *name_span,
                visible_from: stmt_end,
            });
            let base = scopes.len();
            let body_start = body.first().map(|s| s.span.start).unwrap_or(stmt_end);
            bind_params(params, body_start, scopes);
            walk_stmt_seq(body, scopes, visit);
            scopes.truncate(base);
        }

        // `target := value` (optionally annotated) — store introduction/write.
        // Like the assignment family: the RHS (and annotation) are evaluated in
        // the outer scope, then the target's names become visible from the end of
        // the statement onward.
        Stmt::MutAssign {
            target,
            annotation,
            value,
        } => {
            if let Some(annotation) = annotation {
                walk_expr(&annotation.ty, scopes, visit);
            }
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes);
        }

        // `with [binding =] begin(): body` — a transaction block. The context
        // (`begin()`) is evaluated in the outer scope; the body is a nested
        // statement sequence. The optional `binding` (a commit-time handle) is
        // reserved and not consumed by lowering, so it introduces no binder here.
        Stmt::With {
            binding: _,
            context,
            body,
        } => {
            walk_expr(context, scopes, visit);
            let base = scopes.len();
            walk_stmt_seq(body, scopes, visit);
            scopes.truncate(base);
        }

        Stmt::Return(Some(e)) => walk_expr(e, scopes, visit),
        Stmt::Return(None) | Stmt::Pass | Stmt::Error => {}
    }
}

fn walk_expr<'a>(expr: &'a Spanned<Expr>, scopes: &mut Vec<Scoped<'a>>, visit: &mut Visitor<'_>) {
    // Surface the scope live at this expression so a `bindings_in_scope`
    // position inside a lambda/comprehension body (where the stack carries the
    // params/targets) captures it.
    visit(Event::Scope {
        span: expr.span,
        scopes,
    });
    match &expr.node {
        Expr::Name(name) => visit(Event::Use {
            name,
            span: expr.span,
            scopes,
        }),
        Expr::Lit(_) | Expr::Error => {}

        Expr::BinOp { left, right, .. } => {
            walk_expr(left, scopes, visit);
            walk_expr(right, scopes, visit);
        }
        Expr::UnaryOp { operand, .. } => walk_expr(operand, scopes, visit),
        Expr::BoolOp { operands, .. } => {
            for o in operands {
                walk_expr(o, scopes, visit);
            }
        }
        Expr::Compare {
            left, comparators, ..
        } => {
            walk_expr(left, scopes, visit);
            for c in comparators {
                walk_expr(c, scopes, visit);
            }
        }
        Expr::Call { func, args } => {
            walk_expr(func, scopes, visit);
            for a in args {
                walk_expr(a, scopes, visit);
            }
        }
        Expr::List(items) | Expr::Tuple(items) => {
            for it in items {
                walk_expr(it, scopes, visit);
            }
        }
        Expr::Record(fields) => {
            for f in fields {
                walk_expr(&f.value, scopes, visit);
            }
        }
        // Brace forms are structural *type* syntax (a record type `{x: T}`, a
        // tuple type `{T, U}`), reached here through an annotation — which this
        // walk descends into like any other expression, so the type names inside
        // surface as uses on the same footing as those in a `Mut(Int, Txn)`
        // annotation's `Call` form.
        Expr::BraceRecord(fields) => {
            for f in fields {
                walk_expr(&f.value, scopes, visit);
            }
        }
        Expr::BraceGroup(items) => {
            for it in items {
                walk_expr(it, scopes, visit);
            }
        }
        Expr::Subscript { target, index } => {
            walk_expr(target, scopes, visit);
            walk_expr(index, scopes, visit);
        }
        // `target.attr`: only `target` is a name use; `attr` is a field label,
        // not a binding reference.
        Expr::Attribute { target, .. } => walk_expr(target, scopes, visit),

        // `\params -> body` — params visible only inside the body.
        Expr::Lambda { params, body } => {
            let base = scopes.len();
            bind_params(params, body.span.start, scopes);
            walk_expr(body, scopes, visit);
            scopes.truncate(base);
        }

        Expr::IfExp {
            cond,
            then_expr,
            else_expr,
        } => {
            walk_expr(cond, scopes, visit);
            walk_expr(then_expr, scopes, visit);
            walk_expr(else_expr, scopes, visit);
        }

        Expr::ListComp(comp) | Expr::GenExp(comp) => walk_comprehension(comp, scopes, visit),

        // `{base where predicate}` — type syntax. Both halves are ordinary
        // expressions for name purposes: the base names a type and the predicate
        // is a term over `__elem`, so a use inside it resolves in the scope the
        // annotation sits in.
        Expr::BraceRefinement { base, predicate } => {
            walk_expr(base, scopes, visit);
            walk_expr(predicate, scopes, visit);
        }
        // `T => U` — type syntax; both sides name types.
        Expr::FunctionType { domain, codomain } => {
            walk_expr(domain, scopes, visit);
            walk_expr(codomain, scopes, visit);
        }
        // `` `tag ``, `` `tag(𝑒) ``, `` `tag{T} `` — the tag is a literal, not a
        // name use, so only the payload is walked. Both payload brackets carry an
        // expression, and which bracket was written does not change what a name
        // inside it means.
        Expr::VariantCtor { payload, .. } => match payload {
            Some(VariantPayload::Term(e) | VariantPayload::Fields(e)) => {
                walk_expr(e, scopes, visit)
            }
            None => {}
        },

        Expr::Yield(e) => walk_expr(e, scopes, visit),
        Expr::Feed { target, value } => {
            walk_expr(target, scopes, visit);
            walk_expr(value, scopes, visit);
        }

        // An `if`/`match` in value position. The wrapped statement carries its
        // own scoping (its arm bodies are statement sequences), so the walk is
        // the statement walk; the region the statement and this expression
        // share is deduplicated by `scopes`.
        Expr::Block(stmt) => walk_stmt(stmt, scopes, visit),
    }
}

/// Walk a comprehension. Each `for` clause's target is bound from that clause
/// onward (across later clauses and the element), mirroring Python/CHL
/// comprehension scoping; the very first clause's `iter` is evaluated in the
/// enclosing scope.
fn walk_comprehension<'a>(
    comp: &'a Comprehension,
    scopes: &mut Vec<Scoped<'a>>,
    visit: &mut Visitor<'_>,
) {
    use crate::chl_parser::ast::CompClause;
    let base = scopes.len();
    for clause in &comp.clauses {
        match clause {
            CompClause::For { target, iter } => {
                // `iter` sees bindings from prior clauses but not this clause's
                // target; the target then binds across subsequent clauses + the
                // element, visible from the iter's end.
                walk_expr(iter, scopes, visit);
                bind_target(target, iter.span.end, scopes);
            }
            CompClause::If(guard) => walk_expr(guard, scopes, visit),
        }
    }
    walk_expr(&comp.element, scopes, visit);
    scopes.truncate(base);
}

/// Push every name bound by an assignment/loop/comprehension target (handling
/// nested `Tuple` destructuring), each visible from `visible_from`.
fn bind_target<'a>(
    target: &'a Spanned<AssignTarget>,
    visible_from: usize,
    scopes: &mut Vec<Scoped<'a>>,
) {
    match &target.node {
        AssignTarget::Name(name) => {
            scopes.push(Scoped {
                name,
                def_span: target.span,
                visible_from,
            });
        }
        AssignTarget::Tuple(elts) => {
            for elt in elts {
                bind_target(elt, visible_from, scopes);
            }
        }
    }
}

/// Push each parameter binder, visible from `visible_from` (the body start).
fn bind_params<'a>(params: &'a [Param], visible_from: usize, scopes: &mut Vec<Scoped<'a>>) {
    for p in params {
        scopes.push(Scoped {
            name: &p.name,
            def_span: p.name_span,
            visible_from,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::interpreter::Consumer;

    /// Compile a CHL program and return the surface AST this index resolves over.
    fn compile_source_ast(code: &str) -> Module {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        compiled.source_ast
    }

    /// The span of the `n`-th (0-based) byte occurrence of `needle` in `code`.
    fn nth_span(code: &str, needle: &str, n: usize) -> Span {
        let start = code
            .match_indices(needle)
            .nth(n)
            .unwrap_or_else(|| panic!("occurrence {n} of {needle:?} not found"))
            .0;
        Span::new(start, start + needle.len())
    }

    /// The def-span `definitions()` pairs with the use at `use_span`.
    fn def_of(index: &NameBinderIndex, use_span: Span) -> Option<Span> {
        index
            .definitions()
            .into_iter()
            .find(|d| d.use_span == use_span)
            .map(|d| d.def_span)
    }

    /// An assignment variable's use pairs with the binding-site span (the
    /// assignment target) in `definitions()`.
    #[test]
    fn a_use_pairs_with_its_assignment_target() {
        let code = "\
x = 1 + 2
y = x + 3
y
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // The use of `x` in `y = x + 3` (the 2nd `x`: target then use).
        let use_x = nth_span(code, "x", 1);
        // The binder `x` is the assignment target on line 1 (the 1st `x`).
        let def_x = nth_span(code, "x", 0);

        assert_eq!(
            def_of(&index, use_x),
            Some(def_x),
            "use of x pairs with its assignment target span"
        );
    }

    /// The motivating case for source-level resolution: a use of a **multi-param
    /// `def` parameter** pairs with that param's `name_span`. A lowered/uniquify
    /// index structurally cannot do this — `uncurry_params` rewrites the
    /// multi-param reference `Var(a)` to `__arg_tuple_N ▷ .0` before uniquify,
    /// so `a` never survives as a renamable `Var`. Source-level resolution does.
    #[test]
    fn goto_def_on_multi_param_def_parameter_resolves_to_name_span() {
        // Two params `p`, `q` (multi-param → uncurried in lowering). The function
        // name `combine` shares no letters with the params, so byte occurrences
        // of `p`/`q` are unambiguous. Their uses are in the body expression.
        let code = "\
def combine(p, q):
  p + q
combine(1, 2)
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // Param decl `p` is the 1st `p`; its use in `p + q` is the 2nd `p`.
        let param_p = nth_span(code, "p", 0);
        let use_p = nth_span(code, "p", 1);
        // Likewise for `q`.
        let param_q = nth_span(code, "q", 0);
        let use_q = nth_span(code, "q", 1);

        assert_eq!(
            def_of(&index, use_p),
            Some(param_p),
            "multi-param `p` use pairs with its Param.name_span"
        );
        assert_eq!(
            def_of(&index, use_q),
            Some(param_q),
            "multi-param `q` use pairs with its Param.name_span"
        );
    }

    /// Shadowing: a re-bound name pairs with the innermost (most recent) binder
    /// visible at the use, per CHL's sequential let-style scoping.
    #[test]
    fn shadowing_resolves_to_innermost_binder() {
        let code = "\
x = 1
x = x + 1
x
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // Occurrences of `x`: [0]=line1 target, [1]=line2 target, [2]=line2 RHS
        // use, [3]=line3 use.
        let def0 = nth_span(code, "x", 0);
        let def1 = nth_span(code, "x", 1);
        let rhs_use = nth_span(code, "x", 2);
        let trailing_use = nth_span(code, "x", 3);

        // The RHS use on line 2 sees only the *outer* `x` (the line-2 binder is
        // not visible to its own RHS — sequential let-style).
        assert_eq!(
            def_of(&index, rhs_use),
            Some(def0),
            "x in `x = x + 1` RHS pairs with the prior (outer) binding"
        );
        // The trailing `x` sees the innermost (line-2) binder.
        assert_eq!(
            def_of(&index, trailing_use),
            Some(def1),
            "trailing x pairs with the innermost (shadowing) binder"
        );
    }

    /// The scope region at a nested position (inside a `def` body) lists the
    /// expected visible names: the params + the enclosing-scope binders.
    #[test]
    fn scope_region_in_a_def_body_lists_the_visible_names() {
        let code = "\
g = 10
def f(p, q):
  p + q + g
f(1, 2)
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // The region emitted for the body use of `p` — a region is emitted per
        // expression, so this one's span is exactly that occurrence's.
        let body_use_p = nth_span(code, "p", 1);
        let region = index
            .scopes()
            .into_iter()
            .find(|r| r.span == body_use_p)
            .expect("a region is emitted at the body use of p");
        let names: std::collections::HashSet<String> = region
            .bindings
            .into_iter()
            .map(|b| b.name.to_string())
            .collect();

        // Inside f's body: params p, q and the outer g are visible. The def
        // name `f` itself is *not* visible in its own body — CHL does not model
        // recursion (lowering emits `let f = λ… in …`, with `f` bound only in
        // the `in` continuation, not the lambda body).
        assert!(names.contains("p"), "p in scope; got {names:?}");
        assert!(names.contains("q"), "q in scope; got {names:?}");
        assert!(names.contains("g"), "outer g in scope; got {names:?}");
        assert!(
            !names.contains("f"),
            "def name f is NOT visible in its own body (no recursion); got {names:?}"
        );
    }

    /// An unbound use contributes no `definitions()` row — the enumeration skips
    /// it rather than pairing it with anything. Uses a raw parse (an unbound
    /// reference fails type inference, so it can't go through `compile_program`);
    /// name resolution is a pure function over the parsed `Module`, exactly the
    /// point of source-level resolution.
    #[test]
    fn an_unbound_use_contributes_no_definition() {
        let code = "\
x = 1
z + x
";
        let module = crate::chl_parser::parse_module(code).value.expect("parses");
        let index = NameBinderIndex::build(&module);

        // `z` is never bound → no row names it.
        let use_z = nth_span(code, "z", 0);
        assert_eq!(def_of(&index, use_z), None, "unbound z pairs with nothing");
        assert!(
            index.definitions().iter().all(|d| d.name != "z"),
            "no definitions row carries the unbound name z"
        );

        // But `x` *is* bound, even in this parse-only module.
        let use_x = nth_span(code, "x", 1);
        let def_x = nth_span(code, "x", 0);
        assert_eq!(def_of(&index, use_x), Some(def_x));
    }
}
