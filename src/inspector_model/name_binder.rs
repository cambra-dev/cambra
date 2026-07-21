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
    AssignTarget, Comprehension, Expr, IfBranch, Module, Param, Span, Spanned, Stmt,
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

/// An event surfaced during the AST walk. The walk fires an [`Event::Use`] at
/// every `Name` occurrence and an [`Event::Scope`] over every region that
/// introduces or carries binders (statement sequences, loop/function/lambda/
/// comprehension bodies), each carrying the binder stack live at that point.
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
            walk_expr(annotation, scopes, visit);
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
        Stmt::FunctionDef { name, params, body } => {
            // The def's name is bound in the enclosing scope from the statement
            // end onward. The FunctionDef AST node carries no name span of its
            // own, so the whole-statement span is the binder's def-span (the
            // same span lowering tags the `let name = …`).
            scopes.push(Scoped {
                name,
                def_span: stmt.span,
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
                walk_expr(annotation, scopes, visit);
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

        Expr::Yield(e) => walk_expr(e, scopes, visit),
        Expr::Feed { target, value } => {
            walk_expr(target, scopes, visit);
            walk_expr(value, scopes, visit);
        }
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
        AssignTarget::Name(name) => scopes.push(Scoped {
            name,
            def_span: target.span,
            visible_from,
        }),
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
