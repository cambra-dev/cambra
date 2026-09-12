//! Entry iteration — the `for k -> v in m` binder, which ranges over a
//! collection's **entries** rather than over its values.
//!
//! Every CHL collection is one primitive, a data function `𝐷 ⤇ 𝑉` whose domain
//! *is* its data (`src/ccl/design/collections.md`, "The six collection types").
//! A bare binder takes the codomain — `for v in m` binds `𝑉` — and that was all
//! a binder could take until this module, because nothing in the surface
//! language named the other side.
//!
//! ## Iterate the keys, then look the value up
//!
//! An entry-iterating generator lowers to
//!
//! ```text
//! λ __iter_record → __iter_record ▷ (m ▷ map_domain) ▷ (λ k → let v = m[k] in body)
//! ```
//!
//! — the source is [`Builtin::MapDomain`] applied to the collection, which is
//! the same collection re-viewed with its keys where its values were, and the
//! value comes back through the **proven** lookup `m[k]`. The key binder ranges
//! over the collection's own domain, so it carries that domain's refinement,
//! and for a re-keying producer that refinement *is* the present-key domain
//! `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}` — the proof the proven lookup asks for
//! (`src/ccl/design/collections.md`, "Lookup: membership discharge"). So the
//! lookup discharges by construction; a key from `for k -> v in m` is a key of
//! `m`, which is what the spec promises of one (`docs/chl-spec.md`, "4.6 `for` —
//! iteration").
//!
//! **The source has to come from the collection, and this is why.** Two shapes
//! are more obvious and both fail, for one reason. Binding the key to the
//! iteration position the encoding already has — `λ i → let k = i in i ▷ m ▷ …`
//! — and re-viewing the source as entry pairs — `λ k → (k, k ▷ m)`, which
//! lambda elimination turns into the fanout `⟨id, m⟩` — leave a site that is
//! not *iteration-bearing* (`src/ccl/planning/iterate.rs`), so planning sources
//! it from the site's domain **type** instead: a chain-head `iterate` over the
//! domain's unrefined base plus one `restrict` per refinement. For a map that
//! base is the bare key type — `String`, `(Int, String)` — which names no
//! extent, and the refinement it would be narrowed by is a
//! `collection_contains` membership term that is carried and never executed
//! (`src/ccl/ops.rs`, `CollectionContains`). `map_domain` is in the
//! iteration-internalising group, so a site headed by one is sourced from the
//! collection and planning adds nothing.
//!
//! That is also why the value is a lookup rather than a second read of the
//! position: the source's codomain is now the key, so there is no value flowing
//! down the chain to bind, and the collection has to be consulted at the key.
//! The collection subterm therefore appears twice — once under `map_domain`,
//! once under the lookup — as a recorded copy, the same fan-out idiom a
//! value-`Case` element uses for its arms.
//!
//! ## Why the binder's *shape* decides, and not the collection's type
//!
//! The spec's rule is type-directed: a `List(𝑇)` iterates values, a `Set(𝐾)`
//! its keys, a `Map(𝐾, 𝑉)` its entries (`docs/chl-spec.md`, "4.6 `for` —
//! iteration"). Lowering has no types, and the type that would decide is
//! exactly the one the checker cannot form: `Set(𝐾)` and `Map(𝐾, unit)` are the
//! same type, so nothing dispatches between them
//! (`src/ccl/design/collections.md`, "Telling `Set` and `Map` apart [Open]").
//!
//! So this takes the interim that document endorses — **uniform entry
//! iteration**, where a `Set`'s entry is `(𝐾, unit)` and the lossless
//! projection to `𝐾` is what a set binder wanted anyway — with one deviation
//! that costs nothing and buys compatibility. The interim as written makes
//! *every* keyed binder bind a pair, which changes what `for k in s` means;
//! here the **binder's arity** selects instead. A name binder keeps today's
//! codomain reading for every collection type, and only a two-tuple binder asks
//! for the entry, so nothing already written changes meaning and `for k -> v in
//! m` means what the spec says it will mean.
//!
//! What that trades away is the spec's other row: under the type-directed rule
//! `for (a, b) in xs` over a list *of pairs* destructures the value, where here
//! it binds the index and the pair. It is not a regression — no tuple binder
//! lowered at all before this — and it retires when the element choice becomes
//! type-directed, which is the work the `Set`/`Map` distinction blocks.

use super::*;
use crate::{
    ccl::{Builtin, Name, provenance::copy_frame},
    chl_parser::ast::{AssignTarget, Span, Spanned},
};

/// The synthetic binder a **key** side that is itself a pattern lands on.
///
/// Only a compound key needs one: `for k -> v in m` binds the key to the
/// lambda's parameter directly, a lambda binder and a name binder being the
/// same thing. A fixed name rather than a minted one, like `__iter_record` and
/// `__gb_k`: [`crate::ccl::uniquify`] gives every binding site its own uid
/// before any pass substitutes through one, so two nested entry binders shadow
/// by name and stay distinct by identity.
const ENTRY_KEY: &str = "__entry_key";

/// The synthetic binder a **value** side that is itself a pattern lands on.
const ENTRY_VALUE: &str = "__entry_value";

/// One name an entry pattern binds, against the projection path that reaches it
/// from the side's binder. The empty path means the binder *is* the name.
type PatternRow = (String, Vec<usize>);

/// What a `for` binder — in a loop or in a comprehension clause — asks its
/// collection for.
///
/// Built by [`IterBinder::classify`] from the surface target, then handed the
/// lowered collection by [`IterBinder::source`], and finally consulted by
/// [`IterBinder::open`] wherever a per-element body is assembled. The three
/// steps are one decision — what this generator iterates — taken once, so a
/// site cannot re-read the target's shape and reach a different answer in one
/// of the places.
pub(super) enum IterBinder {
    /// `for x in c` — one name, bound to the codomain value. The reading every
    /// collection type gets today.
    Value(String),
    /// `for k -> v in c`, or the parenthesised `for (k, v) in c` the pair arrow
    /// is sugar for (`docs/chl-spec.md`, "2.4 Atoms") — bound to the entry.
    Entry(Box<EntryBinder>),
}

/// An entry binder's two halves and the collection they are read out of.
///
/// Boxed inside [`IterBinder::Entry`] so a value binder — every binder written
/// before this feature — stays one `String` rather than paying for the entry
/// case's fields.
pub(super) struct EntryBinder {
    /// The binder the **key** lands on: the user's own name where the key side
    /// is one, and [`ENTRY_KEY`] where it is a pattern to be opened.
    key_param: String,
    /// One row per name the key side binds, with the projection path reaching it
    /// from `key_param` — empty when that parameter *is* the name. A path
    /// rather than a name, because a product keys a collection as well as a
    /// scalar does (`src/ccl/design/collections.md`, "The key domain is the key
    /// morphism's image"): the storefront's cart is keyed by
    /// `(account, ticker)`, so the key side is itself a pattern.
    keys: Vec<PatternRow>,
    /// The binder the **value** lands on, and the rows opened from it. The
    /// value is not the lambda's parameter here — the source produces keys —
    /// so this name is always `let`-bound to the lookup, and `values` opens a
    /// compound value off it.
    value_param: String,
    values: Vec<PatternRow>,
    /// The collection, as lowered — the term the lookup consults.
    ///
    /// Held rather than re-derived because the generator's *source* is a
    /// different term built from the same collection (`m ▷ map_domain`), and
    /// the two have to be the same collection: re-lowering the surface
    /// expression would lower its effects twice as well.
    collection: Option<Expr>,
}

impl IterBinder {
    /// Read the binder out of a surface target.
    ///
    /// `context` names the construct for the error message, as
    /// [`extract_name_target`]'s does — and every leaf goes through that
    /// function rather than matching [`AssignTarget::Name`] directly, so a
    /// capitalized binder and a subscript are refused with the same words
    /// wherever they appear.
    pub(super) fn classify(
        target: &Spanned<AssignTarget>,
        context: &str,
    ) -> Result<Self, LoweringError> {
        let AssignTarget::Tuple(parts) = &target.node else {
            return extract_name_target(target, context).map(Self::Value);
        };
        // Two components exactly. An entry is a pair — a key and what is stored
        // at it — so there is no third thing for a third component to name, and
        // a one-component binder asks for half of a pair the collection does
        // not have either. Refusing here rather than letting the projections
        // fail in inference is what lets the message say what the binder is
        // *for*.
        let [key, value] = parts.as_slice() else {
            return Err(LoweringError::unsupported(
                target.span,
                format!(
                    "{context}: a tuple binder iterates entries, so it takes exactly two \
                     components — the key and the value (`for k -> v in m`), not {}",
                    parts.len()
                ),
            ));
        };
        let (key_param, keys) = split_side(key, ENTRY_KEY, context)?;
        let (value_param, values) = split_side(value, ENTRY_VALUE, context)?;
        Ok(Self::Entry(Box::new(EntryBinder {
            key_param,
            keys,
            value_param,
            values,
            collection: None,
        })))
    }

    /// The collection this generator's lambda is applied to, and the binder
    /// holding on to what it needs from it.
    ///
    /// A value binder iterates the collection as written. An entry binder
    /// iterates its **keys** — `m ▷ map_domain` — and keeps a copy of the
    /// collection for the lookup [`open`](Self::open) mints. The copy is
    /// recorded as a copy, so both occurrences trace back to the one term the
    /// program wrote.
    pub(super) fn source(
        self,
        collection: Expr,
        span: Span,
        ctx: &mut LoweringContext,
    ) -> (Expr, Self) {
        let Self::Entry(mut entry) = self else {
            return (collection, self);
        };
        let sc = "lower.entry_keys";
        let kept = {
            let _frame = copy_frame("lower.entry_collection");
            collection.clone()
        };
        let op = ctx.tag_machinery(Expr::builtin(Builtin::MapDomain), span, sc);
        let keys = ctx.tag_machinery(Expr::apply(collection, op), span, sc);
        entry.collection = Some(kept);
        (keys, Self::Entry(entry))
    }

    /// The name the iteration lambda binds — the codomain value for a value
    /// binder, and the **key** for an entry binder, whose source produces keys.
    pub(super) fn param(&self) -> &str {
        match self {
            Self::Value(name) => name.as_str(),
            Self::Entry(entry) => entry.key_param.as_str(),
        }
    }

    /// The names the body sees — what has to be shadowed while the body and the
    /// guards are lowered, so a read of a like-named transactional mutable
    /// variable resolves to the iteration local.
    ///
    /// Not [`param`](Self::param): an entry binder introduces its value name
    /// too, and where a side is a pattern the parameter itself is synthetic and
    /// shadows nothing a program can spell.
    pub(super) fn bound_names(&self) -> Vec<String> {
        match self {
            Self::Value(name) => vec![name.clone()],
            Self::Entry(entry) => {
                let mut names: Vec<String> = entry.keys.iter().map(|(n, _)| n.clone()).collect();
                if entry.values.is_empty() {
                    names.push(entry.value_param.clone());
                } else {
                    names.extend(entry.values.iter().map(|(n, _)| n.clone()));
                }
                names
            }
        }
    }

    /// Wrap a per-element `body` in everything an entry binder owes it: the key
    /// pattern opened off the lambda's parameter, the value looked up, and the
    /// value pattern opened off that. A value binder needs none of it and
    /// passes `body` through.
    ///
    /// Goes *under* the iteration lambda, where the key parameter is in scope.
    pub(super) fn open(&self, body: Expr, span: Span, ctx: &mut LoweringContext) -> Expr {
        let sc = "lower.entry_open";
        self.open_with(body, ctx, &mut |e, ctx| ctx.tag_machinery(e, span, sc))
    }

    /// [`open`](Self::open) for a body that will live in a **refinement
    /// predicate** — a comprehension's loop-join filter.
    ///
    /// Predicate position sits in a type slot outside the `walk_children`
    /// domain, so its nodes are swept as a whole by `tag_predicate` once the
    /// predicate is finished rather than tagged as they are minted. Tagging
    /// them here would be the same claim made twice, in the wrong order.
    pub(super) fn open_in_predicate(&self, body: Expr, ctx: &mut LoweringContext) -> Expr {
        self.open_with(body, ctx, &mut |e, _| e)
    }

    /// The shared body of the two openings, with each minted node handed to
    /// `tag` so the caller decides whether it is main-tree machinery or
    /// predicate-slot scaffolding.
    fn open_with(
        &self,
        body: Expr,
        ctx: &mut LoweringContext,
        tag: &mut dyn FnMut(Expr, &mut LoweringContext) -> Expr,
    ) -> Expr {
        let Self::Entry(entry) = self else {
            return body;
        };
        // Innermost-first, so the chain reads in pattern order: the value
        // pattern opens closest to the body, then the lookup that supplies it,
        // then the key pattern the lookup's key is read from. Only the last
        // ordering constraint is real — the lookup's key comes from the key
        // parameter, which the lambda binds — but keeping the whole chain in
        // source order is what makes it read back as the binder that wrote it.
        let value_root = Name::raw(entry.value_param.as_str());
        let body = open_lets(body, &entry.values, &value_root, ctx, tag);
        let body = {
            // `m[k]` — the **proven** lookup, applied as the tupled `(c, k)`
            // pair every keyed access takes (`src/ccl/ops.rs`,
            // `Builtin::LookupProven`). Proven rather than checked because the
            // key came out of this collection's own domain: an `Option` here
            // would be one the program could never see a `` `none `` from, and
            // every use would have to unwrap it.
            let collection = {
                let _frame = copy_frame("lower.entry_collection");
                entry
                    .collection
                    .as_ref()
                    .expect("`source` runs before `open` and is what supplies the collection")
                    .clone()
            };
            let key = tag(Expr::var(Name::raw(entry.key_param.as_str())), ctx);
            let pair = tag(Expr::tuple(vec![collection, key]), ctx);
            let op = tag(Expr::builtin(Builtin::LookupProven), ctx);
            let lookup = tag(Expr::apply(pair, op), ctx);
            tag(Expr::let_bind(entry.value_param.clone(), lookup, body), ctx)
        };
        let key_root = Name::raw(entry.key_param.as_str());
        open_lets(body, &entry.keys, &key_root, ctx, tag)
    }
}

/// Split one side of an entry pattern into the binder it lands on and the rows
/// opened from it.
///
/// A bare name *is* the binder — a lambda parameter and a `let` name are the
/// same thing, so projecting out of a one-name pattern would mint a `let` whose
/// value is the binder itself. Only a compound side needs the synthetic
/// `fallback` name and the rows beneath it.
fn split_side(
    side: &Spanned<AssignTarget>,
    fallback: &str,
    context: &str,
) -> Result<(String, Vec<PatternRow>), LoweringError> {
    if !matches!(&side.node, AssignTarget::Tuple(_)) {
        return Ok((extract_name_target(side, context)?, Vec::new()));
    }
    let mut rows = Vec::new();
    open_pattern(side, &mut Vec::new(), &mut rows, context)?;
    Ok((fallback.to_string(), rows))
}

/// Bind each of `rows` to its read out of `root`, innermost-first, and wrap
/// `body` in the chain.
///
/// Order is not observable — every binding reads the same root and none reads
/// another — but a chain that mirrors the source reads back as the pattern that
/// wrote it.
fn open_lets(
    body: Expr,
    rows: &[PatternRow],
    root: &Name,
    ctx: &mut LoweringContext,
    tag: &mut dyn FnMut(Expr, &mut LoweringContext) -> Expr,
) -> Expr {
    let mut body = body;
    for (name, path) in rows.iter().rev() {
        let mut read = tag(Expr::var(root.clone()), ctx);
        for &index in path {
            let proj = tag(Expr::proj_index(index), ctx);
            read = tag(Expr::apply(read, proj), ctx);
        }
        body = tag(Expr::let_bind(name.clone(), read, body), ctx);
    }
    body
}

/// Walk one side of an entry pattern, recording each name against the
/// projection path that reaches it.
///
/// `path` is the prefix already descended through; it is pushed and popped
/// rather than copied per level so a deeply nested pattern costs one allocation
/// per *leaf* instead of one per edge.
fn open_pattern(
    target: &Spanned<AssignTarget>,
    path: &mut Vec<usize>,
    out: &mut Vec<PatternRow>,
    context: &str,
) -> Result<(), LoweringError> {
    let AssignTarget::Tuple(parts) = &target.node else {
        out.push((extract_name_target(target, context)?, path.clone()));
        return Ok(());
    };
    for (index, part) in parts.iter().enumerate() {
        path.push(index);
        open_pattern(part, path, out, context)?;
        path.pop();
    }
    Ok(())
}
