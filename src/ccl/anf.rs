//! A-normalization: name every compound sub-expression via a fresh `Let`.
//!
//! Runs once, immediately after [`crate::ccl::uniquify`] and before
//! [`crate::ccl::infer::infer`]. Every position that is not already a `Let`'s
//! bound name gets one: a `BinOp`'s operands, an `Apply`'s argument, a
//! collection literal's elements, and so on are rewritten so that only an
//! atomic term — a literal, a variable, a `Lambda` value, a data-source or
//! projection reference — occupies those positions. This is the opposite of
//! `src/ccl/design/ir.md`'s documented "Less normalized than ANF" decision;
//! this pass makes CCL strict ANF instead, and the shape it produces persists
//! through every later pass rather than being undone after inference.
//!
//! # The one exception: refinement predicates
//!
//! This pass never descends into a [`crate::ccl::Type`] value — not a
//! [`crate::ccl::TypedBinding::user_annotation`], not a `Cast`
//! target, not [`crate::ccl::TypedExpr::user_annotation`]. Refinement
//! predicates exist only inside `Type::Refinement`, so this keeps them
//! untouched with no special-case skip. Predicate equality is structural
//! (`Refinement::PartialEq` already has a `Let` arm, so it would tolerate
//! ANF), but the SMT encoder (`src/ccl/infer/solver/smt.rs`) has no `Let`
//! arm and treats one as unencodable, which the solver caller turns into
//! "entailment not proved" — a spurious type error, not lost dedup.
//!
//! # Three recognition contracts: positions a `Let` must never sit between
//!
//! Five shapes carry an external recognition contract: a later pass
//! pattern-matches directly on them, and a `Let` sealed between the wrapper
//! and the thing it wraps breaks that match silently rather than producing a
//! type error. Two of them need their hoisted bindings threaded past the
//! wrapper instead of sealed locally around the child that needed them — the
//! general treatment every other node kind gets from [`normalize`] and
//! [`atomize`]. The other three are not named at all.
//!
//! **The application spine.** An n-ary surface call lowers to a **curried**
//! `Apply` spine — `f(a, b)` is `Apply(Apply(f, a), b)` — and
//! `crate::ccl::infer::emit`'s `parameter_type` walks that nesting directly
//! to find which declared parameter an argument lands on, which is how
//! `emit_apply` detects a pass-by-reference `Mut` parameter past the first
//! argument. Naively atomizing every `Apply`'s `function` position — even
//! when it is itself part of the same curried call — would wedge a `Let`
//! between two levels of one call and collapse the spine `parameter_type`
//! walks, silently breaking pass-by-reference detection for calls like
//! `bump(a + b, cnt)`. [`normalize_apply_spine`] atomizes the whole spine as
//! one unit instead: the ultimate head and every argument are atomized
//! independently, and their bindings thread up to wrap the whole spine.
//!
//! **A statement's effect.** `MutWrite`, `For`, `Case`, `Feed` and `Define`
//! mean nothing except as the `expr` an `ExprStmt` sequences — `mut_elim`
//! recognizes each by
//! pattern-matching an `ExprStmt`'s effect directly (e.g.
//! `mut_elim::rewrite`, `src/ccl/mut_elim.rs:702-708`, matches `for` loops by
//! requiring `effect.node` to be `TypedExprNode::For` verbatim, and
//! `push_continuation_into_case` requires it to be a `Case`). Atomizing,
//! say, a `for` loop's compound iteration source and sealing the hoisted
//! `Let` around the `For` node — the way an ordinary operand is treated —
//! plants that `Let` as the `ExprStmt`'s `expr` field, wedged between the
//! `ExprStmt` and the `For` it no longer directly contains.
//! [`atomize_stmt_effect`] gives these kinds the same spine treatment
//! as `Apply`: `for i in [1, 2, 3]: body` becomes `let __anf = [1, 2, 3] in
//! for i in __anf: body`, the same shape a programmer gets by writing `xs =
//! [1, 2, 3]` ahead of the loop by hand, not a `Let` wedged inside the
//! `ExprStmt`.
//!
//! A statement-position `match` is the same shape one level along: its
//! scrutinee is the compound operand, and a `Let` sealed around the `Case`
//! leaves `push_continuation_into_case` unable to see the `Case` whose
//! branches write. The continuation then stays outside the branches and reads
//! the mutable variable at its entering value, so the write is lost.
//!
//! `Feed` and `Define` are recognized the same way and get the same
//! treatment. `mut_elim`'s `collect_feed_only` walks a read-only `with
//! begin():` block expecting each statement's effect to *be* the `Feed`, and
//! `transform_chain` the same on a loop body; a binding sealed around one
//! plants a `Let` in the effect slot neither sees through. Threading the
//! binding past the `ExprStmt` reorders nothing — the feeds keep their
//! positions on the spine, which is what `channelize`'s outermost-first
//! collection reads — and it is the shape a programmer writing `tmp = e`
//! ahead of `out << tmp` gets.
//!
//! **A refined `Cast`'s value.** A filtered comprehension lowers to
//! `cast({_ | __elem ▷ src ▷ 𝑝} ⤇ _, λ __iter_record → __iter_record ▷ src ▷
//! 𝑓)`, and the two `src` are one term placed twice
//! (`crate::ccl::lower::comprehension`, Phase 1's mint-before-copy contract):
//! inference dedups the predicate-side refinement against the body-side one by
//! structural equality. The predicate rides a type slot, which this pass never
//! descends into, so naming a sub-expression under the cast rewrites the body
//! copy alone — and the fresh uid each hoist mints means normalizing the
//! predicate copy too would still produce a second, unequal name. The two
//! copies then type at unrelated witnesses. So a refined cast's value is left
//! exactly as lowering built it; an unrefined one, carrying no predicate to
//! hold a copy, normalizes like any other operand.
//!
//! **A value-position `Case`'s scrutinee.** `match c[k]?:` dispatches on a
//! *dependent* result — the checked lookup's codomain discharges its key
//! binder to the key — so the scrutinee's type spells the collection's own
//! binders. Naming the scrutinee makes lifting the `match`'s type past that
//! binder discharge the definiens into it, which carries those binders into a
//! type that then passes under them (`crate::ccl::subst`'s Barendregt check).
//! The scrutinee has one reader, so naming it buys nothing. A
//! *statement*-position `Case` is the separate case above: its scrutinee is
//! atomized, with the binding threaded past the `ExprStmt` so `mut_elim` still
//! meets the `Case` directly.
//!
//! **A tupled builtin's argument.** `lookup?` takes its `(collection, key)`
//! pair as a *term*: a dependent codomain discharges its binder to the key
//! term, and `crate::ccl::infer::emit`'s `emit_apply` reads the key straight
//! off the `Tuple` node. A `Var` bound to a pair carries the pair's type
//! without being one, so naming the argument leaves that arm with nothing to
//! read through. [`atomize_tuple_elements`] atomizes the pair's elements in
//! place and leaves the `Tuple` where it stands.
//!
//! This keeps both spines flat by construction: this pass never wedges a
//! `Let` into either one to begin with. `flatten_spine` is a related but
//! distinct repair on the same statement shape — it un-nests a `MutWrite`
//! that later substitution (chiefly `inline`, which runs after this pass)
//! buried under a `Let` again, which this pass cannot prevent since it runs
//! before that substitution exists.

use crate::ccl::{
    Branch, Expr, Name, TypedBinding, TypedExprNode,
    provenance::{self, Nature},
};

/// A-normalize `expr`. See the module docs for what "atomic" means here and
/// the one exception (refinement predicates) and the four recognition
/// contracts (an application spine, a statement's effect, a refined cast's
/// value, a value-position `match`'s scrutinee, and a tupled builtin's
/// argument).
pub fn run(expr: Expr) -> Expr {
    // One recording covers every `Let`/`Var` this pass mints: they are all
    // the same kind of rewrite (hoisting a compound sub-expression into a
    // fresh binding), so nothing inside needs its own narrower scope.
    let root_id = expr.node_id();
    let out = {
        let _g = provenance::enter(root_id, "anf.hoist", Nature::Machinery);
        normalize(expr)
    };
    #[cfg(debug_assertions)]
    debug_assert_flat_spines(&out);
    out
}

/// Is `e` already atomic — safe to leave directly in a position ANF requires
/// be atomic, with no further `let`-binding?
fn is_atomic(e: &Expr) -> bool {
    matches!(
        e.node,
        TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::LoadFrom(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Defer
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Lambda { .. }
    )
}

/// Normalize `e` in a "tail" position — one that is already going to be
/// consumed by an existing binder or sealed scope (a `Let`/`MutDecl` body, a
/// `Lambda`/`Case`-branch body, `For`/`Begin` bodies, `ExprStmt`'s own `expr`
/// and `body`). Self-contained: any bindings `e`'s children need are
/// collected via [`atomize`] and sealed immediately around `e`'s own
/// reconstruction via [`let_chain`], so the result never needs anything
/// hoisted further outward — except when `e` is an `Apply`, handled by
/// [`normalize_apply_spine`] for the reason in the module docs.
fn normalize(e: Expr) -> Expr {
    let id = e.node_id();
    // Lowering pre-stamps some nodes' `ty`/`user_annotation` before inference
    // runs (e.g. a `for`-loop's `Compose` carries a `Type::data_fun(Hole, Hole)`
    // kind stamp inference reads at `infer::emit`). `Expr::preserve` alone
    // hardcodes both to `Hole`/`None`, so every rebuild below goes through
    // this closure instead, which carries the original slots forward.
    let ty = e.ty.clone();
    let annotation = e.user_annotation.clone();
    let rebuild = move |node: TypedExprNode| -> Expr {
        let mut out = Expr::preserve(id, node).with_ty(ty.clone());
        out.user_annotation = annotation.clone();
        out
    };
    match e.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Defer
        | TypedExprNode::Builtin(_) => e,

        TypedExprNode::Error => crate::unexpected_error_node!(),

        TypedExprNode::Apply { .. } => {
            let (binds, spine) = normalize_apply_spine(e);
            let_chain(binds, spine)
        }

        TypedExprNode::Lambda { param, body } => rebuild(TypedExprNode::Lambda {
            param,
            body: Box::new(normalize(*body)),
        }),

        TypedExprNode::Cast { value, target } => {
            // **The third recognition contract: a refined cast's value is
            // copied into its own target.** A filtered comprehension lowers to
            // `cast({_ | __elem ▷ src ▷ 𝑝} ⤇ _, λ __iter_record → __iter_record
            // ▷ src ▷ 𝑓)`, and the two `src` are one term placed twice
            // (`crate::ccl::lower::comprehension`, Phase 1's "mint before copy"
            // contract): inference dedups the predicate-side refinement against
            // the body-side one by structural equality. The predicate rides a
            // type slot, which this pass never descends into, so naming a
            // sub-expression here would rewrite the body copy alone — and the
            // fresh uid each hoist mints means running this pass on the
            // predicate copy too would still produce a second, unequal name.
            // The two copies then type at unrelated witnesses.
            //
            // So a refined cast's value is left as it stands. Only an
            // unrefined one — a `cast` re-viewing a value at a kind, carrying
            // no predicate to hold a copy — normalizes like any other operand.
            if target.carries_refinement() {
                return rebuild(TypedExprNode::Cast { value, target });
            }
            let (binds, value) = atomize(*value);
            let_chain(
                binds,
                rebuild(TypedExprNode::Cast {
                    value: Box::new(value),
                    target,
                }),
            )
        }

        TypedExprNode::BinOp { left, op, right } => {
            let (mut binds, left) = atomize(*left);
            let (right_binds, right) = atomize(*right);
            binds.extend(right_binds);
            let_chain(
                binds,
                rebuild(TypedExprNode::BinOp {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }),
            )
        }

        TypedExprNode::UnaryOp(op, operand) => {
            let (binds, operand) = atomize(*operand);
            let_chain(
                binds,
                rebuild(TypedExprNode::UnaryOp(op, Box::new(operand))),
            )
        }

        TypedExprNode::Aggregate { input, kind } => {
            let (binds, input) = atomize(*input);
            let_chain(
                binds,
                rebuild(TypedExprNode::Aggregate {
                    input: Box::new(input),
                    kind,
                }),
            )
        }

        TypedExprNode::List(elts) => {
            let (binds, elts) = atomize_list(elts);
            let_chain(binds, rebuild(TypedExprNode::List(elts)))
        }

        TypedExprNode::Tuple(elts) => {
            let (binds, elts) = atomize_list(elts);
            let_chain(binds, rebuild(TypedExprNode::Tuple(elts)))
        }

        // Lowering builds both of these directly (a `for` loop desugars to
        // `Compose([source, Lambda(...)])`; `++` lowers straight to
        // `Copair`), so both reach this pass, not only post-inference
        // passes' own mints of them. Each element is a function/collection
        // value in its own right, atomized like any other list of operands.
        TypedExprNode::Compose(elts) => {
            let (binds, elts) = atomize_list(elts);
            let_chain(binds, rebuild(TypedExprNode::Compose(elts)))
        }

        TypedExprNode::Copair(elts) => {
            let (binds, elts) = atomize_list(elts);
            let_chain(binds, rebuild(TypedExprNode::Copair(elts)))
        }

        TypedExprNode::Record(fields) => {
            let mut binds = Vec::new();
            let mut out = Vec::with_capacity(fields.len());
            for (name, value) in fields {
                let (value_binds, value) = atomize(value);
                binds.extend(value_binds);
                out.push((name, value));
            }
            let_chain(binds, rebuild(TypedExprNode::Record(out)))
        }

        TypedExprNode::VariantCtor { tag, payload } => {
            let (binds, payload) = atomize(*payload);
            let_chain(
                binds,
                rebuild(TypedExprNode::VariantCtor {
                    tag,
                    payload: Box::new(payload),
                }),
            )
        }

        TypedExprNode::Feed { name, value } => {
            let (binds, value) = atomize(*value);
            let_chain(
                binds,
                rebuild(TypedExprNode::Feed {
                    name,
                    value: Box::new(value),
                }),
            )
        }

        TypedExprNode::Define { name, value } => {
            let (binds, value) = atomize(*value);
            let_chain(
                binds,
                rebuild(TypedExprNode::Define {
                    name,
                    value: Box::new(value),
                }),
            )
        }

        TypedExprNode::MutWrite { name, key, value } => {
            let mut binds = Vec::new();
            let key = match key {
                Some(key) => {
                    let (key_binds, key) = atomize(*key);
                    binds.extend(key_binds);
                    Some(Box::new(key))
                }
                None => None,
            };
            let (value_binds, value) = atomize(*value);
            binds.extend(value_binds);
            let_chain(
                binds,
                rebuild(TypedExprNode::MutWrite {
                    name,
                    key,
                    value: Box::new(value),
                }),
            )
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => rebuild(TypedExprNode::Let {
            binding,
            bound_expr: Box::new(normalize(*bound_expr)),
            body: Box::new(normalize(*body)),
        }),

        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => rebuild(TypedExprNode::MutDecl {
            binding,
            init: Box::new(normalize(*init)),
            body: Box::new(normalize(*body)),
        }),

        TypedExprNode::ExprStmt { expr, body } => {
            let (binds, expr) = atomize_stmt_effect(*expr);
            let_chain(
                binds,
                rebuild(TypedExprNode::ExprStmt {
                    expr: Box::new(expr),
                    body: Box::new(normalize(*body)),
                }),
            )
        }

        // Reached only when a `For` sits somewhere other than an `ExprStmt`'s
        // effect (e.g. a bare `Case` branch body) — the common case, `For`
        // directly under `ExprStmt`, goes through `atomize_stmt_effect`
        // instead, which threads `iter`'s hoisted bindings past the
        // `ExprStmt` rather than sealing them here. See the module docs.
        TypedExprNode::For { target, iter, body } => {
            let (binds, iter) = atomize(*iter);
            let_chain(
                binds,
                rebuild(TypedExprNode::For {
                    target,
                    iter: Box::new(iter),
                    body: Box::new(normalize(*body)),
                }),
            )
        }

        TypedExprNode::Begin { body } => rebuild(TypedExprNode::Begin {
            body: Box::new(normalize(*body)),
        }),

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            // The scrutinee is **not** named. A `match` on a dependent result
            // — `match c[k]?:` — carries the key's discharge in its own type,
            // and lifting that type past a binder discharges the definiens into
            // it, putting the collection's own binders in a type that then
            // passes under them (`crate::ccl::subst`'s Barendregt check). The
            // scrutinee is a single position with one reader, so naming it buys
            // nothing here anyway.
            let (binds, scrutinee) = match scrutinee {
                Some(scrutinee) => (Vec::new(), Some(Box::new(normalize(*scrutinee)))),
                None => (Vec::new(), None),
            };
            let branches = branches
                .into_iter()
                .map(|branch| Branch {
                    pattern: branch.pattern,
                    guard: normalize(branch.guard),
                    body: normalize(branch.body),
                })
                .collect();
            let_chain(
                binds,
                rebuild(TypedExprNode::Case {
                    scrutinee,
                    branches,
                }),
            )
        }

        TypedExprNode::Realize(_)
        | TypedExprNode::LetRec { .. }
        | TypedExprNode::Transact { .. }
        | TypedExprNode::DisjointJoin(_) => unreachable!(
            "anf: {} cannot appear before inference — it is introduced by a \
             post-inference pass (lambda_elim, mut_elim/transact_phase, or planning)",
            e.node.kind_name()
        ),
    }
}

/// Normalize `e` and, if the result is not atomic, hoist it into one fresh
/// `let`-binding rather than sealing it locally — used at every position
/// that must itself be atomic (an operator's operands, a collection's
/// elements, an `Apply` argument, ...). Returns the bindings the caller must
/// wrap around its own reconstruction (via [`let_chain`]), plus the atomic
/// term to use in `e`'s original position.
fn atomize(e: Expr) -> (Vec<(TypedBinding, Expr)>, Expr) {
    let normalized = normalize(e);
    if is_atomic(&normalized) {
        return (Vec::new(), normalized);
    }
    let name = Name::anf_temp();
    let binding = TypedBinding::new_unannotated(name.clone());
    let var_ref = Expr::var(name);
    (vec![(binding, normalized)], var_ref)
}

fn atomize_list(elts: Vec<Expr>) -> (Vec<(TypedBinding, Expr)>, Vec<Expr>) {
    let mut binds = Vec::new();
    let mut out = Vec::with_capacity(elts.len());
    for e in elts {
        let (e_binds, e) = atomize(e);
        binds.extend(e_binds);
        out.push(e);
    }
    (binds, out)
}

/// Atomize the effect an `ExprStmt` carries — the same threading
/// [`normalize_apply_spine`] gives an `Apply` spine, for the same reason.
/// `MutWrite` and `For` are structural markers `mut_elim` recognizes by
/// pattern-matching an `ExprStmt`'s effect directly (e.g.
/// `mut_elim::rewrite`, `src/ccl/mut_elim.rs:702-708`). Sealing a hoisted
/// binding locally around one of them — the way [`normalize`] treats an
/// ordinary child — wedges a `Let` between the `ExprStmt` and the marker,
/// exactly the shape that match doesn't see through. So their hoisted
/// bindings thread past the whole `ExprStmt` instead: `for i in [1,2,3]:
/// ...` becomes `let __anf = [1,2,3] in for i in __anf: ...` (matching what
/// a programmer gets from writing `xs = [1,2,3]` ahead of the loop by hand),
/// not `(let __anf = [1,2,3] in for i in __anf: ...); cont` wedged inside
/// the `ExprStmt`.
///
/// `Feed`/`Define` are excluded on purpose, even though `channelize` reads
/// them the same way: `mut_elim`'s own `flatten_spine`
/// (`src/ccl/mut_elim.rs:571-574`) deliberately leaves `Feed`/`Define`-headed
/// `ExprStmt` chains nested rather than reassociating them, because
/// `channelize` collects feeds outermost-first and reassociating would
/// reorder channel contributions. Threading a `Feed`'s hoisted binding past
/// its `ExprStmt` the same way risks that same reordering, so it falls back
/// to the ordinary [`normalize`] and seals locally like any other child.
///
/// Any other effect kind carries no recognition contract at all, so it too
/// falls back to [`normalize`] — sealing there is not just safe but
/// necessary, since a non-marker effect's own value may still be discarded
/// freely.
fn atomize_stmt_effect(expr: Expr) -> (Vec<(TypedBinding, Expr)>, Expr) {
    let id = expr.node_id();
    let ty = expr.ty.clone();
    let annotation = expr.user_annotation.clone();
    let rebuild = move |node: TypedExprNode| -> Expr {
        let mut out = Expr::preserve(id, node).with_ty(ty.clone());
        out.user_annotation = annotation.clone();
        out
    };
    match expr.node {
        TypedExprNode::MutWrite { name, key, value } => {
            let mut binds = Vec::new();
            let key = match key {
                Some(key) => {
                    let (key_binds, key) = atomize(*key);
                    binds.extend(key_binds);
                    Some(Box::new(key))
                }
                None => None,
            };
            let (value_binds, value) = atomize(*value);
            binds.extend(value_binds);
            (
                binds,
                rebuild(TypedExprNode::MutWrite {
                    name,
                    key,
                    value: Box::new(value),
                }),
            )
        }
        TypedExprNode::For { target, iter, body } => {
            let (binds, iter) = atomize(*iter);
            (
                binds,
                rebuild(TypedExprNode::For {
                    target,
                    iter: Box::new(iter),
                    body: Box::new(normalize(*body)),
                }),
            )
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let (binds, scrutinee) = match scrutinee {
                Some(scrutinee) => {
                    let (binds, scrutinee) = atomize(*scrutinee);
                    (binds, Some(Box::new(scrutinee)))
                }
                None => (Vec::new(), None),
            };
            let branches = branches
                .into_iter()
                .map(|branch| Branch {
                    pattern: branch.pattern,
                    guard: normalize(branch.guard),
                    body: normalize(branch.body),
                })
                .collect();
            (
                binds,
                rebuild(TypedExprNode::Case {
                    scrutinee,
                    branches,
                }),
            )
        }
        TypedExprNode::Feed { name, value } => {
            let (binds, value) = atomize(*value);
            (
                binds,
                rebuild(TypedExprNode::Feed {
                    name,
                    value: Box::new(value),
                }),
            )
        }
        TypedExprNode::Define { name, value } => {
            let (binds, value) = atomize(*value);
            (
                binds,
                rebuild(TypedExprNode::Define {
                    name,
                    value: Box::new(value),
                }),
            )
        }
        _ => (Vec::new(), normalize(expr)),
    }
}

/// Wrap `tail` in `binds`, innermost binding last — `binds[0]` becomes the
/// outermost `let`, matching the left-to-right evaluation order every caller
/// above accumulates them in.
fn let_chain(binds: Vec<(TypedBinding, Expr)>, tail: Expr) -> Expr {
    binds.into_iter().rev().fold(tail, |body, (binding, def)| {
        Expr::let_in(binding, def, body)
    })
}

/// Is `head` a builtin whose argument is a tuple *term* rather than a tuple
/// *value* — the tupled-argument convention `lookup?` / `insert` /
/// `get_prev_txn` share (`src/ccl/ops.rs`, `Builtin::LookupChecked`)?
///
/// `crate::ccl::infer::emit`'s `emit_apply` reads the key straight off the
/// `Tuple` node, because a dependent codomain discharges its binder to the key
/// *term* and a `Var` bound to a pair carries the pair's type without being
/// one. Naming the pair would leave that arm with a `Var` it cannot read
/// through, so the tuple stays in place and only its elements are atomized.
/// `insert` and `get_prev_txn` are minted after this pass runs, so only
/// `lookup?` can reach here.
fn takes_its_argument_as_a_tuple_term(head: &Expr) -> bool {
    matches!(
        head.node,
        TypedExprNode::Builtin(crate::ccl::Builtin::LookupChecked)
    )
}

/// Atomize a tuple's elements in place, leaving the `Tuple` node itself
/// where it stands and threading the elements' bindings up to the caller.
/// Falls back to [`atomize`] when the argument is not a `Tuple` term, which
/// is the shape `emit_apply` diagnoses rather than one this pass repairs.
fn atomize_tuple_elements(e: Expr) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if !matches!(e.node, TypedExprNode::Tuple(_)) {
        return atomize(e);
    }
    let id = e.node_id();
    let ty = e.ty;
    let annotation = e.user_annotation;
    let TypedExprNode::Tuple(elts) = e.node else {
        unreachable!("guarded above")
    };
    let (binds, elts) = atomize_list(elts);
    let mut out = Expr::preserve(id, TypedExprNode::Tuple(elts)).with_ty(ty);
    out.user_annotation = annotation;
    (binds, out)
}

/// Normalize an `Apply` spine as one unit: walk `function` through nested
/// `Apply`s to the head, atomizing the head and every argument, threading
/// every level's hoisted bindings up to the caller instead of sealing them
/// per level. See the module docs for why sealing per level is wrong here —
/// it would wedge a `Let` into an outer level's `function` position, which
/// `crate::ccl::infer::emit`'s spine walk cannot see through.
fn normalize_apply_spine(e: Expr) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if !matches!(e.node, TypedExprNode::Apply { .. }) {
        // The spine bottoms out at a non-`Apply` head: atomize it like any
        // other value in a position that must be atomic (its own bindings,
        // if any, still thread up rather than sealing here).
        return atomize(e);
    }
    let id = e.node_id();
    let ty = e.ty.clone();
    let annotation = e.user_annotation.clone();
    let TypedExprNode::Apply { function, argument } = e.node else {
        unreachable!("guarded above")
    };
    let (mut binds, function) = normalize_apply_spine(*function);
    let (arg_binds, argument) = if takes_its_argument_as_a_tuple_term(&function) {
        atomize_tuple_elements(*argument)
    } else {
        atomize(*argument)
    };
    binds.extend(arg_binds);
    let mut rebuilt = Expr::preserve(
        id,
        TypedExprNode::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        },
    )
    .with_ty(ty);
    rebuilt.user_annotation = annotation;
    (binds, rebuilt)
}

/// Every `Apply`'s `function` position, if it recurses into another `Apply`,
/// must reach it directly — never through a `Let`/`MutDecl`/`ExprStmt`/
/// `Begin`/`Case`/`For` wrapper. [`normalize_apply_spine`]'s bindings-thread-
/// up design is what is supposed to guarantee this by construction; this
/// walks the pass's own output and fails loudly if it doesn't.
#[cfg(debug_assertions)]
fn debug_assert_flat_spines(e: &Expr) {
    // A refined `Cast`'s value is left exactly as lowering built it (see the
    // `Cast` arm), so this pass has no claim to make about the spines inside
    // it — a `Case`-headed application there is the shape lowering emits for a
    // conditional generator source, and `parameter_type` reads such a head's
    // own `.ty`. What the assertion is about is a wrapper *this pass* minted.
    if let TypedExprNode::Cast { target, .. } = &e.node
        && target.carries_refinement()
    {
        return;
    }
    if let TypedExprNode::Apply { function, .. } = &e.node {
        debug_assert!(
            !matches!(
                function.node,
                TypedExprNode::Let { .. }
                    | TypedExprNode::MutDecl { .. }
                    | TypedExprNode::ExprStmt { .. }
                    | TypedExprNode::Begin { .. }
                    | TypedExprNode::Case { .. }
                    | TypedExprNode::For { .. }
            ),
            "anf: a Let/statement wrapper reached an Apply's function position at {:?} — \
             this wedges the application spine that infer::emit's parameter_type walks",
            function.node.kind_name()
        );
    }
    e.walk_children(debug_assert_flat_spines);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, Lit};

    const ADD: BinOpKind = BinOpKind::Arithmetic(ArithmeticKind::Add);
    const MUL: BinOpKind = BinOpKind::Arithmetic(ArithmeticKind::Mul);

    fn var(name: &str) -> Expr {
        Expr::var(Name::Raw(name.to_string()))
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    #[test]
    fn atomic_leaf_passes_through_unchanged() {
        let out = run(var("x"));
        assert_eq!(out, var("x"));
    }

    #[test]
    fn binop_names_compound_operand() {
        // (1 + 2) * x  ->  let __anf = 1 + 2 in __anf * x
        let e = Expr::binop(Expr::binop(lit(1), ADD, lit(2)), MUL, var("x"));
        let out = run(e);
        let TypedExprNode::Let {
            bound_expr, body, ..
        } = out.node
        else {
            panic!("expected a Let, got {:?}", out.node.kind_name());
        };
        assert_eq!(*bound_expr, Expr::binop(lit(1), ADD, lit(2)));
        let TypedExprNode::BinOp { left, right, .. } = body.node else {
            panic!("expected the body to be the BinOp");
        };
        assert!(is_atomic(&left));
        assert_eq!(*right, var("x"));
    }

    #[test]
    fn both_atoms_needs_no_binding() {
        let e = Expr::binop(var("a"), ADD, var("b"));
        let out = run(e.clone());
        assert_eq!(out, e);
    }

    #[test]
    fn multi_arg_call_keeps_one_flat_spine() {
        // f(a + b, c + d): both arguments are compound, so both get named,
        // but the two-level Apply spine stays directly nested throughout.
        let call = Expr::apply(
            Expr::binop(var("c"), ADD, var("d")),
            Expr::apply(Expr::binop(var("a"), ADD, var("b")), var("f")),
        );
        let out = run(call);

        // Peel two `Let`s.
        let TypedExprNode::Let { body: b1, .. } = out.node else {
            panic!("expected outer Let");
        };
        let TypedExprNode::Let { body: b2, .. } = b1.node else {
            panic!("expected inner Let");
        };
        // What's left must be one flat two-level Apply spine of atoms: no
        // Let/ExprStmt/etc. wedged between the two levels.
        let TypedExprNode::Apply { function, argument } = b2.node else {
            panic!("expected the outer Apply");
        };
        assert!(is_atomic(&argument), "outer argument must be atomic");
        let TypedExprNode::Apply {
            function: head,
            argument: inner_arg,
        } = function.node
        else {
            panic!("function position must still be a directly-nested Apply, not a Let");
        };
        assert!(is_atomic(&head));
        assert!(is_atomic(&inner_arg));
    }

    #[test]
    fn lambda_is_atomic_as_a_value() {
        let lam = Expr::lambda(Name::Raw("x".into()), crate::ccl::Type::Hole, var("x"));
        let e = Expr::apply(lam.clone(), var("map"));
        let out = run(e);
        // The lambda argument needs no naming; it stays inline.
        let TypedExprNode::Apply { argument, .. } = out.node else {
            panic!("expected Apply");
        };
        assert!(is_atomic(&argument));
    }

    #[test]
    fn a_value_case_keeps_its_scrutinee_and_its_guards_in_place() {
        let scrutinee = Expr::binop(var("a"), ADD, var("b"));
        let guard = Expr::binop(var("c"), ADD, var("d"));
        let branch = Branch {
            pattern: None,
            guard,
            body: lit(1),
        };
        let case = Expr::new(TypedExprNode::Case {
            scrutinee: Some(Box::new(scrutinee.clone())),
            branches: vec![branch],
        });
        let out = run(case);
        let TypedExprNode::Case {
            scrutinee: out_scrutinee,
            branches,
        } = out.node
        else {
            panic!("expected the Case with no Let around it");
        };
        // The scrutinee stays where it stands — see the `Case` arm for the
        // dependent-result shape naming it breaks.
        assert_eq!(**out_scrutinee.as_ref().unwrap(), scrutinee);
        // The guard's own compound structure is untouched here — a genuinely
        // compound guard would itself normalize into a local Let, still
        // sitting inside this one branch, never hoisted past the dispatch.
        assert_eq!(branches[0].guard, Expr::binop(var("c"), ADD, var("d")));
    }
}
