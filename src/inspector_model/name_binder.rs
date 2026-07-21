//! The source-level name-resolution index over the parsed CHL AST.
//!
//! This is the [`NameBinderIndex`] — the answer to *lexical* name questions
//! (`goto-definition`, the binder half of `scope-at`). Unlike [`SpanIndex`],
//! which projects the *typed IR* back onto source spans, this index resolves
//! purely over the **surface AST** ([`Module`]).
//!
//! [`SpanIndex`]: crate::inspector_model::SpanIndex
//!
//! # Why source-level
//!
//! Name resolution is a *source-language* lexical question, and lowering has
//! already destroyed some source variables by the time any IR node exists:
//! `uncurry_params` rewrites a multi-param reference `Var(x)` to the projection
//! `__arg_tuple_N ▷ .i` **before** uniquify runs, so a uniquify/IR-based binder
//! table structurally cannot resolve a multi-param `def`/`lambda` parameter
//! (there is no surviving `Var(x)` to rename, no use-span). The surface AST
//! still has `x`/`y` with their [`Param.name_span`](crate::chl_parser::ast::Param::name_span),
//! so resolving over it is lossless and matches the standard LSP approach.
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
    /// The source span of the binder — what `goto-definition` returns. For a
    /// parameter this is its [`Param.name_span`](crate::chl_parser::ast::Param::name_span);
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
    /// The binder's source span (goto-definition target).
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
/// Built once over the surface AST ([`build`](Self::build)); answers
/// [`definition_of`](Self::definition_of) (use→binder, goto-definition) and
/// [`bindings_in_scope`](Self::bindings_in_scope) (visible binders at a
/// position, the name half of `scope-at`).
///
/// # Resolution by span
///
/// The canonical handle is the source [`Span`] (what you click). Both queries
/// take a span and answer by re-walking the AST with the same scope bookkeeping
/// the build pass used; an unbound or unknown span resolves gracefully to
/// `None`/empty, never a panic. The index keeps a reference-free owned copy of
/// the resolution inputs — the `Module` is borrowed only during a query, so the
/// index is built eagerly but the walks are re-run per query (a program's AST is
/// small; this trades a tiny amount of recomputation for a far simpler, clearly
/// correct implementation than caching a span→binder map with shadowing).
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

    /// Resolve a `Name` use at `use_span` to the source span of its binder
    /// (goto-definition). `None` if `use_span` is not a `Name` use, or the name
    /// is unbound at that position.
    ///
    /// The innermost binder visible at `use_span` wins (shadowing); a binder is
    /// only visible if its binding site precedes the use in lexical scope
    /// (sequential let-style).
    pub fn definition_of(&self, use_span: Span) -> Option<Span> {
        let mut found: Option<Span> = None;
        let mut scopes: Vec<Scoped> = Vec::new();
        walk_module(&self.module, &mut scopes, &mut |ev| {
            // Only the `Name` use exactly at `use_span` is a query hit.
            if let Event::Use { name, span, scopes } = ev
                && span == use_span
            {
                found = resolve(name, use_span, scopes);
            }
        });
        found
    }

    /// The binder whose binding site is exactly `def_span`, or `None` if no
    /// binder is written there.
    ///
    /// The inverse question to [`definition_of`](Self::definition_of): that one
    /// asks what a *use* refers to, this one asks whether a span *is* a binding
    /// site and what it binds. The inspector needs it to type a binder: a
    /// binder's name and type live on the IR node that binds it, and no IR node
    /// carries the binder's own span, so the name from here is what selects that
    /// node (see `Snapshot::binder_type`).
    ///
    /// Spans are compared exactly, as [`definition_of`](Self::definition_of)
    /// compares use spans. Two binders never share a binding site, so the first
    /// match in source order is the only one.
    pub fn binder_at(&self, def_span: Span) -> Option<Binding> {
        let mut found: Option<Binding> = None;
        let mut scopes: Vec<Scoped> = Vec::new();
        walk_module(&self.module, &mut scopes, &mut |ev| {
            if let Event::Binder { name, def_span: at } = ev
                && at == def_span
                && found.is_none()
            {
                found = Some(Binding {
                    name: name.clone(),
                    def_span,
                });
            }
        });
        found
    }

    /// Enumerate every resolved use→binder pair in the module — the data behind
    /// the `/api/snapshot` `definitions` array. Each entry is a `Name` use that
    /// resolves to a visible binder, paired with that binder's def-span and the
    /// bound name; unbound uses (which would resolve to `None`) are skipped.
    ///
    /// Pure: re-walks the AST with the same scope bookkeeping the point queries
    /// use, resolving each use against the binder stack live at it. Order is the
    /// source pre-order of the uses.
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
    /// A scope region is emitted for each binder-bearing span the walk surfaces
    /// (statement sequences, function/lambda/comprehension/loop bodies) whose
    /// visible-binder set is non-empty; regions with no binders in scope are
    /// dropped (an empty `scopes` row carries nothing). The binders are the ones
    /// visible at the region's start, outermost → innermost, matching
    /// [`bindings_in_scope`](Self::bindings_in_scope)'s shape.
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

    /// The binders visible at `at` (the name half of `scope-at`): every binder
    /// in lexical scope whose binding site precedes `at`, innermost shadowing
    /// outermost. Ordered outermost → innermost.
    ///
    /// Resolution is by the position `at.start`: the index walks into the
    /// tightest AST scope containing it, capturing the binder stack there. A
    /// position outside every scope (or inside no binding-introducing context)
    /// returns just the top-level binders visible at that point.
    pub fn bindings_in_scope(&self, at: Span) -> Vec<Binding> {
        let pos = at.start;
        let mut scopes: Vec<Scoped> = Vec::new();
        // Capture the binder stack at the deepest scope-boundary that still
        // contains `pos`. The use-visitor reports the *stack as of each scope's
        // body*; we record the last (deepest) one covering `pos`.
        let mut captured: Vec<Binding> = Vec::new();
        let mut best_extent = usize::MAX;
        walk_module(&self.module, &mut scopes, &mut |ev| {
            if let Event::Scope { span, scopes } = ev
                && span.start <= pos
                && pos < span.end
            {
                let extent = span.end - span.start;
                // `<=` so a tie (coincident span) keeps the later, deeper
                // capture — its binder stack is a superset.
                if extent <= best_extent {
                    best_extent = extent;
                    captured = visible_bindings(scopes, pos);
                }
            }
        });
        captured
    }
}

/// An event surfaced during the AST walk: an [`Event::Use`] at every `Name`
/// occurrence, an [`Event::Binder`] wherever a binder is introduced, and an
/// [`Event::Scope`] over every region that carries binders (statement sequences,
/// loop/function/lambda/comprehension bodies), the latter two carrying the
/// binder stack live at that point.
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
    /// A binder introduction, fired where the binder is pushed rather than where
    /// it becomes visible. A binder nothing follows into — the last statement of
    /// a sequence — is surfaced like any other, which a scan of the
    /// [`Scope`](Self::Scope) stacks would miss.
    Binder { name: &'s SmolStr, def_span: Span },
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
            bind_target(target, stmt_end, scopes, visit);
        }
        Stmt::AnnAssign {
            target,
            annotation,
            value,
        } => {
            walk_expr(&annotation.ty, scopes, visit);
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes, visit);
        }
        Stmt::AugAssign { target, value, .. } => {
            // `x += v` reads the prior `x` in the RHS and rebinds it after.
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes, visit);
        }
        Stmt::Define { target, value } => {
            walk_expr(value, scopes, visit);
            bind_target(target, stmt_end, scopes, visit);
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
                    visit(Event::Binder {
                        name,
                        def_span: *name_span,
                    });
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
            bind_target(target, body_start, scopes, visit);
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
            visit(Event::Binder {
                name,
                def_span: *name_span,
            });
            scopes.push(Scoped {
                name,
                def_span: *name_span,
                visible_from: stmt_end,
            });
            let base = scopes.len();
            let body_start = body.first().map(|s| s.span.start).unwrap_or(stmt_end);
            bind_params(params, body_start, scopes, visit);
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
            bind_target(target, stmt_end, scopes, visit);
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
            bind_params(params, body.span.start, scopes, visit);
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
                bind_target(target, iter.span.end, scopes, visit);
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
    visit: &mut Visitor<'_>,
) {
    match &target.node {
        AssignTarget::Name(name) => {
            visit(Event::Binder {
                name,
                def_span: target.span,
            });
            scopes.push(Scoped {
                name,
                def_span: target.span,
                visible_from,
            });
        }
        AssignTarget::Tuple(elts) => {
            for elt in elts {
                bind_target(elt, visible_from, scopes, visit);
            }
        }
    }
}

/// Push each parameter binder, visible from `visible_from` (the body start).
fn bind_params<'a>(
    params: &'a [Param],
    visible_from: usize,
    scopes: &mut Vec<Scoped<'a>>,
    visit: &mut Visitor<'_>,
) {
    for p in params {
        visit(Event::Binder {
            name: &p.name,
            def_span: p.name_span,
        });
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

    /// goto-definition on an assignment variable's use resolves to the
    /// binding-site span (the assignment target).
    #[test]
    fn goto_def_on_assignment_use_resolves_to_binding_site() {
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
            index.definition_of(use_x),
            Some(def_x),
            "use of x resolves to its assignment target span"
        );
    }

    /// The motivating case for source-level resolution: goto-definition on a
    /// **multi-param `def` parameter** use resolves to that param's `name_span`.
    /// A lowered/uniquify
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
            index.definition_of(use_p),
            Some(param_p),
            "multi-param `p` use resolves to its Param.name_span"
        );
        assert_eq!(
            index.definition_of(use_q),
            Some(param_q),
            "multi-param `q` use resolves to its Param.name_span"
        );
    }

    /// Shadowing: a re-bound name resolves to the innermost (most recent)
    /// binder visible at the use, per CHL's sequential let-style scoping.
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
            index.definition_of(rhs_use),
            Some(def0),
            "x in `x = x + 1` RHS resolves to the prior (outer) binding"
        );
        // The trailing `x` sees the innermost (line-2) binder.
        assert_eq!(
            index.definition_of(trailing_use),
            Some(def1),
            "trailing x resolves to the innermost (shadowing) binder"
        );
    }

    /// `bindings_in_scope` at a nested position (inside a `def` body) returns
    /// the expected visible names: the params + the enclosing-scope binders.
    #[test]
    fn bindings_in_scope_at_nested_position_lists_visible_names() {
        let code = "\
g = 10
def f(p, q):
  p + q + g
f(1, 2)
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // A position on the body use of `p` (inside the def body).
        let body_use_p = nth_span(code, "p", 1);
        let names: std::collections::HashSet<String> = index
            .bindings_in_scope(body_use_p)
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

    /// An unbound name resolves to `None` — graceful, no panic. Uses a raw
    /// parse (an unbound reference fails type inference, so it can't go through
    /// `compile_program`); name resolution is a pure function over the parsed
    /// `Module`, exactly the point of source-level resolution.
    #[test]
    fn unbound_name_resolves_to_none() {
        let code = "\
x = 1
z + x
";
        let module = crate::chl_parser::parse_module(code).value.expect("parses");
        let index = NameBinderIndex::build(&module);

        // `z` is never bound → no definition.
        let use_z = nth_span(code, "z", 0);
        assert_eq!(
            index.definition_of(use_z),
            None,
            "unbound z resolves to None"
        );

        // A span that is not a `Name` use at all (the literal `1`) → None.
        let lit = nth_span(code, "1", 0);
        assert_eq!(index.definition_of(lit), None);

        // An out-of-tree span matches no use → None.
        assert_eq!(
            index.definition_of(Span::new(code.len() + 10, code.len() + 11)),
            None,
            "a span matching no use resolves to None"
        );

        // But `x` *is* bound, even in this parse-only module.
        let use_x = nth_span(code, "x", 1);
        let def_x = nth_span(code, "x", 0);
        assert_eq!(index.definition_of(use_x), Some(def_x));
    }
}
