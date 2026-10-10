//! A-normalization: name every compound sub-expression via a fresh `Let`.
//!
//! Runs once, immediately after [`crate::ccl::uniquify`] and before
//! [`crate::ccl::infer::infer`]. Every position that is not already a `Let`'s
//! bound name gets one: a `BinOp`'s operands, an `Apply`'s argument, a
//! collection literal's elements, and so on are rewritten so that only an
//! atomic term — a literal, a variable other than a mutable one, a `Lambda`
//! value, a data-source or projection reference — occupies those positions.
//! This is the opposite of `src/ccl/design/ir.md`'s documented "Less normalized
//! than ANF" decision; this pass makes CCL strict ANF instead, and no later
//! pass undoes the shape wholesale. Individual bindings do go:
//! [`crate::ccl::inline`]'s read-once rule substitutes away an `AnfTemp` read
//! exactly once, so a pass that pattern-matches on such a definiens meets it
//! directly rather than through the binder.
//!
//! # The one exception: refinement predicates
//!
//! This pass never descends into a [`crate::ccl::Type`] value — not a
//! [`crate::ccl::TypedBinding::user_annotation`], not a `Cast`
//! target, not [`crate::ccl::TypedExpr::user_annotation`]. Refinement
//! predicates exist only inside `Type::Refinement`, so this keeps them
//! untouched with no special-case skip.
//!
//! A predicate acquires this pass's bindings anyway, later:
//! [`crate::ccl::inline`] substitutes a definiens carrying them into one, and
//! the copy whose single occurrence its read-once rule already moved into place
//! carries none, so one predicate reaches a comparison under two spellings.
//! `crate::ccl::ccl_utils::discharge_transparent_lets` takes the bindings back
//! out at both sites that compare predicates — the deficit rule in
//! `src/ccl/infer/solver/constrain.rs` and `refinement_discharged_by` in
//! `src/ccl/inline.rs`. Neither reads the two spellings as one predicate on its
//! own: equality is structural (`Refinement::PartialEq`), and the SMT encoder
//! (`src/ccl/infer/solver/smt.rs`) has no `Let` arm, reporting one as
//! unencodable.
//!
//! # A mutable-variable read is not atomic
//!
//! A reference to a mutable variable is a read, and a read denotes the value
//! the variable holds at the point it is performed. Every other atomic term
//! denotes the same value wherever it stands, which is what makes leaving one
//! in place free. A hoist moves the terms beside a read earlier, so the read is
//! performed after them: `(x, g(x))`, where `g` writes through a `Mut`
//! parameter, hoists the call and leaves the element reading `x` after the
//! write it was written before. So a read is named like a compound operand,
//! and its binding lands at the read's source position, in sequence with the
//! writes beside it. Which names are mutable is answered syntactically, by
//! [`crate::ccl::mut_scope`], since inference has not run.
//!
//! **Whether the binding is opaque is [`crate::ccl::mut_read`]'s to say.** That
//! pass cuts a block into read segments at its writes and seals one binding per
//! segment, so opacity is a property of the segment rather than of the read: a
//! binding sealed here would open a segment at every hoisted read.
//!
//! **A chain holding one is flattened onto the statement spine** ([`peel`]).
//! [`normalize`] seals the bindings an operand needed around that operand, and
//! an enclosing hoist nests the seal inside its own definiens, where the outer
//! binding's type names a binder bound strictly inside the term it types. An
//! ordinary chain survives that nesting, a transparent binder being discharged
//! into the types leaving its scope. The binding `mut_read` seals is opaque and
//! is not discharged, so a chain holding a read is peeled and re-sealed one
//! level out.
//!
//! A **handle** position holds the variable rather than its value, so the
//! mention there is not a read and stays where it stands
//! ([`atomize_handle`]).
//!
//! # Five recognition contracts: positions a `Let` must never sit between
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
//! recognizes each by pattern-matching an `ExprStmt`'s effect directly
//! (`mut_elim::rewrite` matches `for` loops by requiring `effect.node` to be
//! `TypedExprNode::For` verbatim, and `push_continuation_into_case` requires it
//! to be a `Case`). Atomizing,
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
//! **A refined `Cast`'s value.** `groupby(c, key)` lowers to
//! `cast({_ | __elem ▷ c ▷ key == __gb_k} ⤇ _, λ __gb_i → __gb_i ▷ c)`
//! (`crate::ccl::lower::exprs`'s `lower_groupby`), and the two `c` are one term
//! placed twice: inference dedups the predicate-side refinement against the
//! body-side one by structural equality. The predicate rides a type slot, which
//! this pass never descends into, so naming a sub-expression under the cast
//! rewrites the body copy alone — and the fresh uid each hoist mints means
//! normalizing the predicate copy too would still produce a second, unequal
//! name. The two copies then type at unrelated witnesses. So a refined cast's
//! value is left exactly as lowering built it; an unrefined one, carrying no
//! predicate to hold a copy, normalizes like any other operand.
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
    mut_scope::{Muts, is_mut_var, under_param, with},
    provenance::{self, Nature},
};

/// A-normalize `expr`. See the module docs for what "atomic" means here and
/// the one exception (refinement predicates) and the five recognition
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
        normalize(expr, &Muts::new())
    };
    #[cfg(debug_assertions)]
    debug_assert_flat_spines(&out);
    out
}

/// Is `e` already atomic — safe to leave directly in a position ANF requires
/// be atomic, with no further `let`-binding?
///
/// A reference to a **mutable variable** is not: it is a read, and a read
/// denotes the value the variable holds at the point it is performed. Left in
/// place, it is performed wherever the position it sits in ends up being
/// evaluated — after every binding this pass hoists out from beside it, which
/// is to say after any write those perform. Naming it puts the read back at its
/// source position, in sequence with the writes around it.
fn is_atomic(e: &Expr, muts: &Muts) -> bool {
    if is_mut_var(e, muts) {
        return false;
    }
    match &e.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Defer
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Lambda { .. } => true,
        // An unresolved method stands for one of its candidate references, each an atom,
        // and inference resolves it only where it is an application's function.
        TypedExprNode::Method { .. } => true,
        // A comprehension is atomic when the term it encodes to is — which is
        // the unfiltered shape, one `Lambda`
        // ([`crate::ccl::comprehension::encodes_to_lambda`]). Deciding it on the
        // encoding rather than on the node keeps a comprehension named in
        // exactly the operand positions its encoding would be, which is what a
        // dependent source needs: a `Σ`-typed collection bound by a `let` puts
        // its witness out of scope at every use of the binder.
        TypedExprNode::Comprehension {
            generators,
            element,
        } => crate::ccl::comprehension::encodes_to_lambda(generators, element),
        _ => false,
    }
}

/// Normalize `e` in a "tail" position — one that is already going to be
/// consumed by an existing binder or sealed scope (a `Let`/`MutDecl` body, a
/// `Lambda`/`Case`-branch body, `For`/`Begin` bodies, `ExprStmt`'s own `expr`
/// and `body`). Self-contained: any bindings `e`'s children need are
/// collected via [`atomize`] and sealed immediately around `e`'s own
/// reconstruction via [`let_chain`], so the result never needs anything
/// hoisted further outward — except when `e` is an `Apply`, handled by
/// [`normalize_apply_spine`] for the reason in the module docs.
fn normalize(e: Expr, muts: &Muts) -> Expr {
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
        // A comprehension is still in surface form here —
        // `crate::ccl::comprehension` turns it into the `cast`/`λ`/`▷`
        // encoding after this pass — so each part normalizes at the position
        // it will occupy.
        //
        // **Nothing that becomes a predicate normalizes.** A guard becomes the
        // refinement predicate of the cast `crate::ccl::comprehension` emits,
        // and a generator source is copied into that same predicate, so both
        // reach a type slot — the position the `Cast` arm's rule is about, and
        // one this pass never descends into. A binding sealed inside either
        // would stand inside a predicate, where it names a binder the type
        // around it does not bind. A fanned-out element's `Case` guards
        // ([`crate::ccl::comprehension::fans_out`]) become per-arm cast
        // predicates the same way, so only that element's arm bodies
        // normalize.
        //
        // Every other element becomes the per-element lambda's body and
        // normalizes exactly as a `Lambda` body does.
        //
        // Nothing hoists *out*: a generator's target scopes over its guards,
        // every later generator, and the element, and the element's own
        // bindings seal around it.
        TypedExprNode::Comprehension {
            generators,
            element,
        } => {
            // Under **no** mutable variables: a comprehension is a map, so its
            // element is evaluated once per source position with no write in
            // between, and a read of an enclosing mutable variable denotes one
            // value throughout. The hoist a read gets elsewhere exists to keep
            // it in sequence with the writes beside it, and here there are
            // none.
            let element = if crate::ccl::comprehension::fans_out(&generators, &element) {
                normalize_fan_out_arms(*element)
            } else {
                normalize(*element, &Muts::new())
            };
            rebuild(TypedExprNode::Comprehension {
                generators,
                element: Box::new(element),
            })
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Defer
        | TypedExprNode::Builtin(_) => e,

        TypedExprNode::Error => crate::unexpected_error_node!(),

        TypedExprNode::Apply { .. } => {
            let (binds, spine) = normalize_apply_spine(e, muts);
            let_chain(binds, spine)
        }

        TypedExprNode::Lambda { param, body } => {
            let inner = under_param(muts, &param);
            rebuild(TypedExprNode::Lambda {
                body: Box::new(normalize(*body, &inner)),
                param,
            })
        }

        TypedExprNode::Cast { value, target } => {
            // **The third recognition contract: a refined cast's value is
            // copied into its own target.** `groupby(c, key)` lowers to
            // `cast({_ | __elem ▷ c ▷ key == __gb_k} ⤇ _, λ __gb_i → __gb_i ▷
            // c)` (`crate::ccl::lower::exprs`'s `lower_groupby`), and the two
            // `c` are one term placed twice: inference dedups the
            // predicate-side refinement against the body-side one by structural
            // equality. The predicate rides a type slot, which this pass never
            // descends into, so naming a sub-expression here would rewrite the
            // body copy alone — and the fresh uid each hoist mints means
            // running this pass on the predicate copy too would still produce a
            // second, unequal name. The two copies then type at unrelated
            // witnesses.
            //
            // So a refined cast's value is left as it stands. Only an
            // unrefined one — a `cast` re-viewing a value at a kind, carrying
            // no predicate to hold a copy — normalizes like any other operand.
            if target.carries_refinement() {
                return rebuild(TypedExprNode::Cast { value, target });
            }
            let (binds, value) = atomize(*value, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::Cast {
                    value: Box::new(value),
                    target,
                }),
            )
        }

        TypedExprNode::BinOp { left, op, right } => {
            let (mut binds, left) = atomize(*left, muts);
            let (right_binds, right) = atomize(*right, muts);
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
            let (binds, operand) = atomize(*operand, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::UnaryOp(op, Box::new(operand))),
            )
        }

        TypedExprNode::Aggregate { input, kind } => {
            let (binds, input) = atomize(*input, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::Aggregate {
                    input: Box::new(input),
                    kind,
                }),
            )
        }

        TypedExprNode::List(elts) => {
            let (binds, elts) = atomize_list(elts, muts);
            let_chain(binds, rebuild(TypedExprNode::List(elts)))
        }

        TypedExprNode::Tuple(elts) => {
            let (binds, elts) = atomize_list(elts, muts);
            let_chain(binds, rebuild(TypedExprNode::Tuple(elts)))
        }

        // Lowering builds both of these directly (a `for` loop desugars to
        // `Compose([source, Lambda(...)])`; `++` lowers straight to
        // `Copair`), so both reach this pass, not only post-inference
        // passes' own mints of them. Each element is a function/collection
        // value in its own right, atomized like any other list of operands.
        TypedExprNode::Compose(elts) => {
            let (binds, elts) = atomize_list(elts, muts);
            let_chain(binds, rebuild(TypedExprNode::Compose(elts)))
        }

        TypedExprNode::Copair(elts) => {
            let (binds, elts) = atomize_list(elts, muts);
            let_chain(binds, rebuild(TypedExprNode::Copair(elts)))
        }

        TypedExprNode::Record(fields) => {
            let mut binds = Vec::new();
            let mut out = Vec::with_capacity(fields.len());
            for (name, value) in fields {
                let (value_binds, value) = atomize(value, muts);
                binds.extend(value_binds);
                out.push((name, value));
            }
            let_chain(binds, rebuild(TypedExprNode::Record(out)))
        }

        // The candidates are references, already atoms.
        node @ TypedExprNode::Method { .. } => rebuild(node),

        TypedExprNode::VariantCtor {
            tag,
            payload,
            nominal,
        } => {
            let (binds, payload) = atomize(*payload, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::VariantCtor {
                    tag,
                    payload: Box::new(payload),
                    nominal,
                }),
            )
        }

        TypedExprNode::Feed { name, value } => {
            let (binds, value) = atomize_handle(*value, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::Feed {
                    name,
                    value: Box::new(value),
                }),
            )
        }

        TypedExprNode::Define { name, value } => {
            let (binds, value) = atomize_handle(*value, muts);
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
                    let (key_binds, key) = atomize(*key, muts);
                    binds.extend(key_binds);
                    Some(Box::new(key))
                }
                None => None,
            };
            let (value_binds, value) = atomize(*value, muts);
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
            bound_expr: Box::new(normalize(*bound_expr, muts)),
            body: Box::new(normalize(*body, muts)),
        }),

        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let inner = with(muts, &binding.name);
            rebuild(TypedExprNode::MutDecl {
                init: Box::new(normalize(*init, muts)),
                body: Box::new(normalize(*body, &inner)),
                binding,
            })
        }

        TypedExprNode::ExprStmt { expr, body } => {
            let (binds, expr) = atomize_stmt_effect(*expr, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::ExprStmt {
                    expr: Box::new(expr),
                    body: Box::new(normalize(*body, muts)),
                }),
            )
        }

        // Reached only when a `For` sits somewhere other than an `ExprStmt`'s
        // effect (e.g. a bare `Case` branch body) — the common case, `For`
        // directly under `ExprStmt`, goes through `atomize_stmt_effect`
        // instead, which threads `iter`'s hoisted bindings past the
        // `ExprStmt` rather than sealing them here. See the module docs.
        TypedExprNode::For { target, iter, body } => {
            let (binds, iter) = atomize(*iter, muts);
            let_chain(
                binds,
                rebuild(TypedExprNode::For {
                    target,
                    iter: Box::new(iter),
                    body: Box::new(normalize(*body, muts)),
                }),
            )
        }

        TypedExprNode::Begin { body } => rebuild(TypedExprNode::Begin {
            body: Box::new(normalize(*body, muts)),
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
                Some(scrutinee) => (Vec::new(), Some(Box::new(normalize(*scrutinee, muts)))),
                None => (Vec::new(), None),
            };
            let branches = branches
                .into_iter()
                .map(|branch| Branch {
                    pattern: branch.pattern,
                    guard: normalize(branch.guard, muts),
                    body: normalize(branch.body, muts),
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

/// Normalize the arm bodies of a comprehension element that
/// [`crate::ccl::comprehension::fans_out`], leaving every guard as written.
///
/// Each guard becomes the refinement predicate of its arm's cast, a type slot
/// this pass never descends into, while each body becomes that arm's
/// per-element lambda body. A trailing `true → Case{…}` arm (an `elif` chain)
/// is flattened into the same partition by the fan-out
/// ([`crate::ccl::ccl_utils::flatten_trailing_value_case`]), so its inner
/// `Case` is treated the same way rather than normalized as a body.
fn normalize_fan_out_arms(e: Expr) -> Expr {
    let id = e.node_id();
    let ty = e.ty.clone();
    let annotation = e.user_annotation;
    let TypedExprNode::Case {
        scrutinee,
        branches,
    } = e.node
    else {
        unreachable!("a fanned-out comprehension element is a value `Case`")
    };
    let last = branches.len().saturating_sub(1);
    let branches = branches
        .into_iter()
        .enumerate()
        .map(|(i, branch)| {
            let nested = i == last && crate::ccl::ccl_utils::is_trailing_nested_case(&branch);
            Branch {
                pattern: branch.pattern,
                guard: branch.guard,
                body: if nested {
                    normalize_fan_out_arms(branch.body)
                } else {
                    normalize(branch.body, &Muts::new())
                },
            }
        })
        .collect();
    let mut out = Expr::preserve(
        id,
        TypedExprNode::Case {
            scrutinee,
            branches,
        },
    )
    .with_ty(ty);
    out.user_annotation = annotation;
    out
}

/// Normalize `e` and, if the result is not atomic, hoist it into one fresh
/// `let`-binding rather than sealing it locally — used at every position
/// that must itself be atomic (an operator's operands, a collection's
/// elements, an `Apply` argument, ...). Returns the bindings the caller must
/// wrap around its own reconstruction (via [`let_chain`]), plus the atomic
/// term to use in `e`'s original position.
fn atomize(e: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
    let (mut binds, core) = peel(normalize(e, muts), muts);
    if is_atomic(&core, muts) {
        return (binds, core);
    }
    let name = Name::anf_temp();
    let binding = TypedBinding::new_unannotated(name.clone());
    let var_ref = Expr::var(name);
    binds.push((binding, core));
    (binds, var_ref)
}

/// Undo [`let_chain`] at the root of `e`: split the bindings this pass sealed
/// around a normalized operand back off, so the caller re-seals them one level
/// out, beside its own.
///
/// A sealed chain in a position about to be hoisted nests one binding's scope
/// inside another's definiens — `let __anf₂ = (let __anf₁ = x in __anf₁ ^+ 1)`
/// — and inference refines a binding by the term that computed it, so
/// `__anf₂`'s type reads `{Int | __elem == __anf₁ ^+ 1}`: a type naming a
/// binder bound strictly inside the term it types, which the Barendregt check
/// in [`crate::ccl::subst`] reports the moment that type passes under the
/// binder. Peeled, the two are siblings on one spine and every type is written
/// where its binders are in scope.
///
/// Only a chain holding a read is peeled, and then all of it: peeling a
/// *subset* would move a read across a sibling binding that may write, which is
/// the mis-ordering this pass is sequencing the read to avoid. A chain of
/// ordinary hoists keeps its nesting, where every binder is discharged into the
/// types leaving its scope and a refinement stays written in closed terms.
///
/// Only this pass's own binders are peeled ([`Name::is_anf_temp`]). A `let` the
/// program wrote, or a statement spine in a value position, is a block of its
/// own whose writes belong where they stand.
fn peel(mut e: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if !seals_a_read(&e, muts) {
        return (Vec::new(), e);
    }
    let mut binds = Vec::new();
    loop {
        match &e.node {
            TypedExprNode::Let { binding, .. } if binding.name.is_anf_temp() => {}
            _ => return (binds, e),
        }
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = e.node
        else {
            unreachable!("matched immediately above")
        };
        binds.push((binding, *bound_expr));
        e = *body;
    }
}

/// [`atomize`], except at a **handle position**: a bare reference to a mutable
/// variable is left exactly where it stands.
///
/// A read is named to put it in sequence with the writes around it
/// ([`is_atomic`]), but two of the three positions a handle survives in are not
/// reads at all (`src/ccl/design/mutability.md`, "A mutable variable read is an
/// explicit operation"): an application's argument, where `emit_apply` relates
/// a bare reference to a `Mut` parameter, and an application's function, which
/// is where a keyed read `m[k]` puts the collection. A feed's value is the
/// third — `transact_phase::rewrite_as_of_reads` turns a history read fed out
/// of a read-only block into an as-of join, and it is the bare reference that
/// says so. Naming any of them leaves the recognizer a `Var` it cannot read
/// through, so each keeps whatever ordering it had.
///
/// Which argument positions are pass-by-reference is not knowable here —
/// it is a question about the callee's parameter, and inference has not run
/// (`crate::ccl::mut_read`, "What ends a segment"). So a read in an argument
/// position is still performed at the call, after any write an argument beside
/// it performs.
fn atomize_handle(e: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if is_mut_var(&e, muts) {
        return (Vec::new(), e);
    }
    atomize(e, muts)
}

fn atomize_list(elts: Vec<Expr>, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Vec<Expr>) {
    let mut binds = Vec::new();
    let mut out = Vec::with_capacity(elts.len());
    for e in elts {
        let (e_binds, e) = atomize(e, muts);
        binds.extend(e_binds);
        out.push(e);
    }
    (binds, out)
}

/// Atomize the effect an `ExprStmt` carries — the same threading
/// [`normalize_apply_spine`] gives an `Apply` spine, for the same reason.
/// `MutWrite`, `For`, `Case`, `Feed` and `Define` are structural markers
/// `mut_elim` recognizes by pattern-matching an `ExprStmt`'s effect directly
/// (e.g. `mut_elim::rewrite`). Sealing a hoisted binding locally around one of
/// them — the way [`normalize`] treats an ordinary child — wedges a `Let`
/// between the `ExprStmt` and the marker, exactly the shape that match doesn't
/// see through. So their hoisted bindings thread past the whole `ExprStmt`
/// instead: `for i in [1,2,3]: ...` becomes `let __anf = [1,2,3] in for i in
/// __anf: ...` (matching what
/// a programmer gets from writing `xs = [1,2,3]` ahead of the loop by hand),
/// not `(let __anf = [1,2,3] in for i in __anf: ...); cont` wedged inside
/// the `ExprStmt`.
///
/// `Case`, `Feed` and `Define` carry the same contract and get the same
/// treatment: `push_continuation_into_case` requires the effect to be the
/// `Case`, and `mut_elim`'s `collect_feed_only` and `transform_chain` require
/// it to be the `Feed`. Threading reorders nothing, because what moves is the
/// hoisted binding and not the statements: the feeds keep their spine
/// positions, which is what `channelize`'s outermost-first collection reads.
/// `mut_elim`'s `flatten_spine` leaves a `Feed`/`Define`-headed `ExprStmt`
/// chain nested for a different reason — reassociating there moves the
/// statements themselves, which would reorder the contributions.
///
/// Any other effect kind carries no recognition contract at all, so it too
/// falls back to [`normalize`] — sealing there is not just safe but
/// necessary, since a non-marker effect's own value may still be discarded
/// freely.
fn atomize_stmt_effect(expr: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
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
                    let (key_binds, key) = atomize(*key, muts);
                    binds.extend(key_binds);
                    Some(Box::new(key))
                }
                None => None,
            };
            let (value_binds, value) = atomize(*value, muts);
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
            let (binds, iter) = atomize(*iter, muts);
            (
                binds,
                rebuild(TypedExprNode::For {
                    target,
                    iter: Box::new(iter),
                    body: Box::new(normalize(*body, muts)),
                }),
            )
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let (binds, scrutinee) = match scrutinee {
                Some(scrutinee) => {
                    let (binds, scrutinee) = atomize(*scrutinee, muts);
                    (binds, Some(Box::new(scrutinee)))
                }
                None => (Vec::new(), None),
            };
            let branches = branches
                .into_iter()
                .map(|branch| Branch {
                    pattern: branch.pattern,
                    guard: normalize(branch.guard, muts),
                    body: normalize(branch.body, muts),
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
            let (binds, value) = atomize_handle(*value, muts);
            (
                binds,
                rebuild(TypedExprNode::Feed {
                    name,
                    value: Box::new(value),
                }),
            )
        }
        TypedExprNode::Define { name, value } => {
            let (binds, value) = atomize_handle(*value, muts);
            (
                binds,
                rebuild(TypedExprNode::Define {
                    name,
                    value: Box::new(value),
                }),
            )
        }
        _ => (Vec::new(), normalize(expr, muts)),
    }
}

/// Does the chain this pass sealed at the root of `e` hold a read — a binding
/// whose definiens is a bare reference to a mutable variable?
fn seals_a_read(e: &Expr, muts: &Muts) -> bool {
    let mut cursor = e;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &cursor.node
    {
        if !binding.name.is_anf_temp() {
            return false;
        }
        if is_mut_var(bound_expr, muts) {
            return true;
        }
        cursor = body;
    }
    false
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
fn atomize_tuple_elements(e: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if !matches!(e.node, TypedExprNode::Tuple(_)) {
        return atomize(e, muts);
    }
    let id = e.node_id();
    let ty = e.ty;
    let annotation = e.user_annotation;
    let TypedExprNode::Tuple(elts) = e.node else {
        unreachable!("guarded above")
    };
    let (binds, elts) = atomize_list(elts, muts);
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
fn normalize_apply_spine(e: Expr, muts: &Muts) -> (Vec<(TypedBinding, Expr)>, Expr) {
    if !matches!(e.node, TypedExprNode::Apply { .. }) {
        // The spine bottoms out at a non-`Apply` head: atomize it like any
        // other value in a position that must be atomic (its own bindings,
        // if any, still thread up rather than sealing here).
        return atomize_handle(e, muts);
    }
    let id = e.node_id();
    let ty = e.ty.clone();
    let annotation = e.user_annotation.clone();
    let TypedExprNode::Apply { function, argument } = e.node else {
        unreachable!("guarded above")
    };
    let (mut binds, function) = normalize_apply_spine(*function, muts);
    let (arg_binds, argument) = if takes_its_argument_as_a_tuple_term(&function) {
        atomize_tuple_elements(*argument, muts)
    } else {
        atomize_handle(*argument, muts)
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
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::{ArithmeticKind, BaseType, BinOpKind, HistoryKind, Lit, Type};

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
        assert!(is_atomic(&left, &Muts::new()));
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
        assert!(
            is_atomic(&argument, &Muts::new()),
            "outer argument must be atomic"
        );
        let TypedExprNode::Apply {
            function: head,
            argument: inner_arg,
        } = function.node
        else {
            panic!("function position must still be a directly-nested Apply, not a Let");
        };
        assert!(is_atomic(&head, &Muts::new()));
        assert!(is_atomic(&inner_arg, &Muts::new()));
    }

    #[test]
    fn lambda_is_atomic_as_a_value() {
        let lam = Expr::lambda(Name::Raw("x".into()), Type::Hole, var("x"));
        let e = Expr::apply(lam.clone(), var("map"));
        let out = run(e);
        // The lambda argument needs no naming; it stays inline.
        let TypedExprNode::Apply { argument, .. } = out.node else {
            panic!("expected Apply");
        };
        assert!(is_atomic(&argument, &Muts::new()));
    }

    /// `x := 0` over `body`, with `x` a mutable `Int`.
    fn accumulator(name: &Name, body: Expr) -> Expr {
        Expr::mut_decl(
            name.clone(),
            Type::History {
                value: Box::new(Type::Base(BaseType::Int)),
                domain: Box::new(Type::Hole),
                history_kind: HistoryKind::Overwrite,
            },
            lit(0),
            body,
        )
    }

    /// A read beside a hoisted sibling: the tuple's first element is a read and
    /// its second is a call, so the read is named ahead of the call rather than
    /// left to be performed after it.
    #[test]
    fn a_read_is_named_ahead_of_a_hoisted_sibling() {
        let x = Name::fresh("x");
        let call = Expr::apply(Expr::var(x.clone()), var("f"));
        let out = run(accumulator(
            &x,
            Expr::tuple(vec![Expr::var(x.clone()), call]),
        ));
        let s = symbolic(&out);
        assert!(
            s.contains("__anf = x") && s.contains("(__anf, __anf)"),
            "the read is named ahead of the call: {s}"
        );
        assert!(
            s.find("= x").unwrap() < s.find("▷ f").unwrap(),
            "the read is performed before the call: {s}"
        );
    }

    /// An application's argument is a handle position: a bare read there is
    /// what `emit_apply` relates to a `Mut` parameter, so it stays.
    #[test]
    fn a_read_in_an_argument_position_stays_bare() {
        let x = Name::fresh("x");
        let out = run(accumulator(&x, Expr::apply(Expr::var(x.clone()), var("g"))));
        let s = symbolic(&out);
        assert!(!s.contains("__anf"), "nothing is named: {s}");
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
