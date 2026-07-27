//! Structural diff of two CCL programs — the shared / new / deleted analysis
//! that whole-program branching is built on. See `src/ccl/design/diffing.md`.
//!
//! Given two [`TypedExpr`] trees, [`diff`] computes a node correspondence and
//! classifies it. It is a GumTree-style matcher (Falleri et al., *Fine-grained
//! and accurate source code differencing*, ASE 2014) over the α-invariant
//! [`content_hash`](super::content_hash::content_hash):
//!
//! 1. **Top-down anchors.** Map the *largest* subtrees whose content hash is
//!    equal — equal hash means isomorphic modulo α, so the whole subtree is
//!    *shared*. Larger subtrees are claimed first; once a node is matched its
//!    descendants are matched with it (paired by hash, which is correct for the
//!    order-insensitive nodes too).
//! 2. **Root anchoring.** Two programs being diffed are two versions of *one*
//!    program, so their roots correspond by construction ([`anchor_roots`]).
//!    Nothing else can establish that — a root that gained a statement scores
//!    too low for step 3 to pair it, and the whole program would read as
//!    deleted-and-reinserted for a one-statement edit.
//! 3. **Bottom-up container recovery.** An interior node left unmatched is
//!    paired with the best same-kind candidate in the other tree that
//!    *contains* enough of its already-matched descendants. This is what keeps
//!    an inserted statement from desynchronizing the whole `let`-spine below
//!    it: the unchanged tail anchors in step 1, and the containers above it are
//!    recovered here rather than reported as wholesale rewrites.
//! 4. **Optimal recovery inside a paired container.** Two containers paired in
//!    step 2 or 3 still have unmatched descendants — near-identical subtrees
//!    whose hashes differ somewhere inside. [`recover`] maps those *optimally*,
//!    by tree edit distance ([`ted`]), so an edit deep inside a large subtree
//!    does not read as a wholesale replacement of everything around it.
//!
//! The result is then classified along two independent axes ([`Match`]):
//! whether the node's **content** changed ([`Content`]) and whether its
//! **placement** did ([`Placement`]). A source-only node is **deleted**; a
//! target-only node is **new**.
//!
//! # Stage-agnostic: one core, two modes
//!
//! [`diff`] is a pure function of two [`TypedExpr`] trees — it does not care
//! which pipeline stage produced them, so the *same* implementation serves both
//! supported modes; the caller picks the mode by choosing which trees to pass:
//!
//! * **Pre-uniquify** (lowered CCL, `Raw` names, most types still `Hole`) —
//!   close to source, minimal diffs, the default target.
//! * **Post-inference** (uniquified, fully typed) — binders carry run-varying
//!   `uid`s and nodes carry concrete types, so the diff reflects type
//!   differences the earlier stage cannot see.
//!
//! Nothing in the matcher is stage-specific: [`content_hash`] is uid-robust
//! (free names by spelling) and type-aware, which is exactly what lets one core
//! handle both. See the `content_hash` module.
//!
//! # Scope of this implementation
//!
//! This is the analysis, not a rewrite: it does **not** construct the unified
//! `Versioned`-node tree (see `src/ccl/design/diffing.md`, "Beyond the
//! analysis: Versioned nodes"). The one place it departs from full GumTree is
//! candidate selection in step 3, which picks the best-scoring container
//! greedily rather than solving a global assignment — GumTree does the same.

use std::cmp::Reverse;
use std::collections::HashMap;
use std::mem::Discriminant;

use super::TypedExpr;
use super::content_hash::{cast_target_predicate, content_hash};
use super::context::{CompileError, CompileStage, compile_to};

/// A node's bottom-up similarity must reach this fraction of its descendants
/// for container recovery to pair it. The GumTree default.
const SIMILARITY_THRESHOLD: f64 = 0.5;

/// Subtree-size ceiling for the optimal recovery step ([`recover`]). Tree edit
/// distance is `O(n²m²)` in the worst case, so a pair of containers larger than
/// this keeps only the matches steps 1–2 found; their unmatched interiors are
/// reported as deleted/new rather than aligned. GumTree's default, for the same
/// reason.
const MAX_RECOVERY_SIZE: u32 = 100;

/// Whether a matched node's *content* changed. Orthogonal to [`Placement`]: a
/// node can keep its content and move, or stay put and change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Content {
    /// Equal content hash — identical computation, reusable wholesale.
    Same,
    /// The node corresponds but its content differs. The actual divergence is
    /// in the children; these are the points a `Versioned` node would sit.
    Changed,
}

/// Whether a matched node's *position in the tree* changed. Orthogonal to
/// [`Content`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    /// The node hangs off the corresponding parent, in a corresponding
    /// position among its matched siblings.
    InPlace,
    /// The node was relocated: either its parent does not correspond, or it
    /// crossed one of its matched siblings within an order-sensitive parent.
    /// Reported once, at the root of the relocated subtree — a moved subtree's
    /// descendants stay `InPlace` relative to it.
    Moved,
}

/// One node correspondence between the two programs, classified along both
/// axes.
#[derive(Debug, Clone, Copy)]
pub struct Match<'a> {
    /// The node in the old program.
    pub src: &'a TypedExpr,
    /// The node it corresponds to in the new program.
    pub dst: &'a TypedExpr,
    /// Did the content change?
    pub content: Content,
    /// Did the position change?
    pub placement: Placement,
}

/// The classified correspondence between two programs. All references borrow
/// the two input trees.
#[derive(Debug, Default)]
pub struct Diff<'a> {
    /// Every node correspondence, in source pre-order.
    pub matched: Vec<Match<'a>>,
    /// Source-only nodes: present in the old program, gone in the new.
    pub deleted: Vec<&'a TypedExpr>,
    /// Target-only nodes: introduced by the new program.
    pub new: Vec<&'a TypedExpr>,
}

impl<'a> Diff<'a> {
    /// Correspondences whose content is identical ([`Content::Same`]) — the
    /// computation the two versions share, whether or not it moved.
    pub fn shared(&self) -> impl Iterator<Item = &Match<'a>> {
        self.matched.iter().filter(|m| m.content == Content::Same)
    }

    /// Correspondences that changed ([`Content::Changed`]) — "the same place in
    /// both programs, different content".
    pub fn updated(&self) -> impl Iterator<Item = &Match<'a>> {
        self.matched
            .iter()
            .filter(|m| m.content == Content::Changed)
    }

    /// Correspondences that were relocated ([`Placement::Moved`]), independent
    /// of whether their content also changed.
    pub fn moved(&self) -> impl Iterator<Item = &Match<'a>> {
        self.matched
            .iter()
            .filter(|m| m.placement == Placement::Moved)
    }

    /// `true` when the two programs correspond node-for-node with no change in
    /// content or placement anywhere — the "these are the same program" test.
    pub fn is_identical(&self) -> bool {
        self.deleted.is_empty()
            && self.new.is_empty()
            && self
                .matched
                .iter()
                .all(|m| m.content == Content::Same && m.placement == Placement::InPlace)
    }
}

/// Diff two programs (`src` = old, `dst` = new). See the module docs.
pub fn diff<'a>(src: &'a TypedExpr, dst: &'a TypedExpr) -> Diff<'a> {
    let s = Indexed::build(src);
    let d = Indexed::build(dst);
    let mut m = Matching::new(s.len(), d.len());

    top_down(&s, &d, &mut m);
    anchor_roots(&s, &d, &mut m);
    bottom_up(&s, &d, &mut m);

    classify(&s, &d, &m)
}

/// Anchor the two roots to each other when phase 1 has not already.
///
/// Two programs being diffed are two *versions of one program*, so their roots
/// correspond by construction — neither has anywhere else to go. Bottom-up
/// recovery cannot reach that conclusion on its own: its Dice test weighs a
/// container's matched descendants against the *combined* size of both
/// subtrees, so a root that gained one substantial statement scores below
/// [`SIMILARITY_THRESHOLD`] and the entire program reads as
/// deleted-and-reinserted for a one-statement edit. Anchoring the roots turns
/// that back into an insertion, and gives phase 3 a pair to align the spine
/// inside.
///
/// Requiring the same node kind keeps the anchor honest: two genuinely
/// unrelated programs (a `BinOp` against a `Lit`) still correspond nowhere.
fn anchor_roots(s: &Indexed, d: &Indexed, m: &mut Matching) {
    const ROOT: usize = 0;
    if m.src_matched(ROOT) || m.dst_matched(ROOT) || s.nodes[ROOT].kind != d.nodes[ROOT].kind {
        return;
    }
    m.map(ROOT, ROOT);
    recover(s, d, ROOT, ROOT, m);
}

/// Compile two source programs to `stage` and diff them — the end-to-end entry
/// point from source. The classified [`Diff`] borrows the two compiled trees,
/// which live only for the duration of this call, so the result is delivered to
/// `f`; return out of it whatever you need to keep (e.g. counts, cloned nodes).
///
/// ```ignore
/// let (shared, new) = diff_programs(v1_src, v2_src, CompileStage::Inferred,
///     |d| (d.shared().count(), d.new.len()))?;
/// ```
pub fn diff_programs<R>(
    src: &str,
    dst: &str,
    stage: CompileStage,
    f: impl FnOnce(&Diff) -> R,
) -> Result<R, Vec<CompileError>> {
    let a = compile_to(src, stage)?;
    let b = compile_to(dst, stage)?;
    Ok(f(&diff(&a, &b)))
}

// ---------------------------------------------------------------------------
// Flattened tree index
// ---------------------------------------------------------------------------

/// One node of a tree, flattened into pre-order. The subtree rooted at index
/// `i` occupies the contiguous range `[i, i + size)`, so descendants of `i` are
/// exactly the indices in `(i, i + size)`.
struct NodeInfo<'a> {
    expr: &'a TypedExpr,
    kind: Discriminant<super::TypedExprNode>,
    hash: u64,
    /// Subtree node count, self included.
    size: u32,
    /// Leaf = 1; interior = 1 + max child height.
    height: u32,
    /// Root = 0; a child is its parent's depth plus one.
    depth: u32,
    /// `None` at the root.
    parent: Option<usize>,
    children: Vec<usize>,
    /// `true` for the nodes whose children are a *set*, not a sequence
    /// (`Record`, `CollectionUnion`) — the content hash folds them
    /// permutation-invariantly, so reordering them is not a move.
    unordered: bool,
}

struct Indexed<'a> {
    nodes: Vec<NodeInfo<'a>>,
}

impl<'a> Indexed<'a> {
    fn build(root: &'a TypedExpr) -> Self {
        let mut nodes = Vec::new();
        Self::add(root, None, 0, &mut nodes);
        Indexed { nodes }
    }

    /// Append `e`'s subtree in pre-order, returning `e`'s index.
    fn add(
        e: &'a TypedExpr,
        parent: Option<usize>,
        depth: u32,
        nodes: &mut Vec<NodeInfo<'a>>,
    ) -> usize {
        let idx = nodes.len();
        nodes.push(NodeInfo {
            expr: e,
            kind: std::mem::discriminant(&e.node),
            hash: content_hash(e).0,
            size: 1,
            height: 1,
            depth,
            parent,
            children: Vec::new(),
            unordered: has_unordered_children(e),
        });
        let child_refs = child_exprs(e);
        let mut children = Vec::with_capacity(child_refs.len());
        let (mut size, mut max_h) = (1u32, 0u32);
        for c in child_refs {
            let ci = Self::add(c, Some(idx), depth + 1, nodes);
            size += nodes[ci].size;
            max_h = max_h.max(nodes[ci].height);
            children.push(ci);
        }
        nodes[idx].size = size;
        nodes[idx].height = 1 + max_h;
        nodes[idx].children = children;
        idx
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Exclusive upper bound of the subtree rooted at `i`.
    fn subtree_end(&self, i: usize) -> usize {
        i + self.nodes[i].size as usize
    }

    /// `true` if `node` lies strictly inside the subtree rooted at `root`.
    fn is_descendant(&self, node: usize, root: usize) -> bool {
        root < node && node < self.subtree_end(root)
    }
}

/// Do this node's children denote a set rather than a sequence? Mirrors the
/// `unordered` fold in `content_hash`'s `hash_rel`: if the hash is
/// permutation-invariant over these children, the differ must not call a
/// permutation of them a move.
fn has_unordered_children(e: &TypedExpr) -> bool {
    use super::TypedExprNode as N;
    matches!(e.node, N::Record(_) | N::CollectionUnion(_))
}

/// The direct child expressions of `e`, borrowed for `e`'s lifetime.
///
/// The lifetime-preserving companion to [`TypedExpr::walk_children`], which it
/// mirrors arm-for-arm **except for `Cast`**: a cast-target domain-refinement
/// predicate is a load-bearing term (a comprehension filter/join condition), so
/// the differ descends into it; `walk_children` excludes it (a type child,
/// reached via type walks). The match is exhaustive — no wildcard — so adding a
/// `TypedExprNode` variant is a compile error here until its children are
/// declared.
//
// NOTE (recurring shape): this duplicates `walk_children`'s child enumeration.
// The two could share a private `for_each_child<'a>(&'a self, &mut dyn
// FnMut(&'a TypedExpr))`, but that adds dynamic dispatch to the hot
// `walk_children` traversal, so it isn't folded in here.
fn child_exprs(e: &TypedExpr) -> Vec<&TypedExpr> {
    use super::TypedExprNode as N;
    match &e.node {
        N::Lit(_) | N::Var(_) | N::Builtin(_) | N::Proj(_) | N::Source(_) | N::Defer | N::Error => {
            vec![]
        }
        N::Apply { function, argument } => vec![function, argument],
        N::Cast { value, target } => match cast_target_predicate(target) {
            Some(pred) => vec![value, pred],
            None => vec![value],
        },
        N::BinOp { left, right, .. } => vec![left, right],
        N::UnaryOp(_, inner) => vec![inner],
        N::Lambda { body, .. } => vec![body],
        N::Aggregate { input, .. } => vec![input],
        N::Let {
            bound_expr, body, ..
        } => vec![bound_expr, body],
        N::List(xs) | N::Tuple(xs) | N::Compose(xs) | N::CollectionUnion(xs) => xs.iter().collect(),
        N::Case {
            scrutinee,
            branches,
        } => {
            let mut v: Vec<&TypedExpr> = scrutinee.as_deref().into_iter().collect();
            for b in branches {
                v.push(&b.guard);
                v.push(&b.body);
            }
            v
        }
        N::VariantCtor { payload, .. } => vec![payload],
        N::Record(fields) => fields.iter().map(|(_, e)| e).collect(),
        N::Transact { keys, writers, .. } => {
            let mut v: Vec<&TypedExpr> = keys.iter().map(|k| &k.init).collect();
            for w in writers {
                v.push(&w.source);
                v.push(&w.body);
            }
            v
        }
        N::LetRec { bindings, body } => {
            let mut v: Vec<&TypedExpr> = bindings.iter().map(|(_, def)| def).collect();
            v.push(body);
            v
        }
        N::For { iter, body, .. } => vec![iter, body],
        N::Begin { body } => vec![body],
        N::ExprStmt { expr, body } => vec![expr, body],
        N::Feed { value, .. } | N::Define { value, .. } | N::MutWrite { value, .. } => vec![value],
    }
}

// ---------------------------------------------------------------------------
// Matching state
// ---------------------------------------------------------------------------

struct Matching {
    src_to_dst: Vec<Option<usize>>,
    dst_to_src: Vec<Option<usize>>,
}

impl Matching {
    fn new(n_src: usize, n_dst: usize) -> Self {
        Matching {
            src_to_dst: vec![None; n_src],
            dst_to_src: vec![None; n_dst],
        }
    }

    fn map(&mut self, s: usize, d: usize) {
        self.src_to_dst[s] = Some(d);
        self.dst_to_src[d] = Some(s);
    }

    fn src_matched(&self, s: usize) -> bool {
        self.src_to_dst[s].is_some()
    }

    fn dst_matched(&self, d: usize) -> bool {
        self.dst_to_src[d].is_some()
    }
}

// ---------------------------------------------------------------------------
// Phase 1: top-down isomorphic anchoring
// ---------------------------------------------------------------------------

fn top_down(s: &Indexed, d: &Indexed, m: &mut Matching) {
    // Index dst nodes by hash for candidate lookup.
    let mut dst_by_hash: HashMap<u64, Vec<usize>> = HashMap::new();
    for (i, n) in d.nodes.iter().enumerate() {
        dst_by_hash.entry(n.hash).or_default().push(i);
    }

    // Tallest (and, tie-broken, largest) subtrees first, so a big anchor claims
    // its descendants before any smaller subtree inside it is considered. For
    // identical trees the root (a unique hash) is anchored first and maps
    // everything in one pass.
    let mut order: Vec<usize> = (0..s.len()).collect();
    order.sort_by_key(|&i| Reverse((s.nodes[i].height, s.nodes[i].size)));

    // Anchor each unmatched src subtree to an unmatched dst subtree of equal
    // hash. Equal hash means isomorphic-modulo-α, so *every* such pairing is a
    // valid "shared" classification — but not every one is equally *useful*:
    // when a subtree shape repeats (and small ones always do — `0`, `true`,
    // `x`), the copy we pick decides whether the node reads as sitting still or
    // as having moved, and it decides which of its siblings are left over for
    // the later phases to pair. So among equal-hash candidates, take the one in
    // the most structurally corresponding position ([`best_candidate`]).
    // Refusing to anchor ambiguous duplicates at all would instead strand them
    // with no bottom-up seed, which is strictly worse.
    for u in order {
        if m.src_matched(u) {
            continue;
        }
        let Some(cands) = dst_by_hash.get(&s.nodes[u].hash) else {
            continue;
        };
        if let Some(w) = best_candidate(s, d, u, cands, m) {
            map_isomorphic(s, d, u, w, m);
        }
    }
}

/// Pick the free candidate in `cands` (all of which are isomorphic to `u`) that
/// sits in the most structurally corresponding position, by three criteria in
/// descending priority:
///
/// 1. **Its parent already corresponds to `u`'s.** Exact information, when the
///    enclosing structure happens to be matched already.
/// 2. **The longest agreeing chain of ancestor kinds.** `1` in a branch body
///    and `1` in that branch's guard are indistinguishable as subtrees; their
///    ancestor chains (`Case, Let` vs `BinOp, Case, Let`) are not.
/// 3. **The closest depth**, then source order, as a deterministic tie-break.
///
/// Without this the choice is arbitrary, and an arbitrary choice manufactures a
/// spurious move plus a spurious delete/insert pair for the copy it displaced.
fn best_candidate(
    s: &Indexed,
    d: &Indexed,
    u: usize,
    cands: &[usize],
    m: &Matching,
) -> Option<usize> {
    let mut free = cands.iter().copied().filter(|&w| !m.dst_matched(w));
    let first = free.next()?;
    let Some(second) = free.next() else {
        return Some(first); // unambiguous: no scoring needed
    };

    let parent_corresponds = |w: usize| match (s.nodes[u].parent, d.nodes[w].parent) {
        (Some(pu), Some(pw)) => m.src_to_dst[pu] == Some(pw),
        (None, None) => true,
        _ => false,
    };
    let u_ancestors = ancestor_kinds(s, u);
    let score = |w: usize| {
        let agree = ancestor_kinds(d, w)
            .iter()
            .zip(&u_ancestors)
            .take_while(|(a, b)| a == b)
            .count();
        let depth_gap = s.nodes[u].depth.abs_diff(d.nodes[w].depth);
        (parent_corresponds(w), agree, Reverse(depth_gap))
    };
    [first, second]
        .into_iter()
        .chain(free)
        .max_by_key(|&w| (score(w), Reverse(w)))
}

/// The kinds of `n`'s ancestors, innermost (its parent) first.
fn ancestor_kinds(t: &Indexed, n: usize) -> Vec<Discriminant<super::TypedExprNode>> {
    let mut out = Vec::new();
    let mut cur = t.nodes[n].parent;
    while let Some(p) = cur {
        out.push(t.nodes[p].kind);
        cur = t.nodes[p].parent;
    }
    out
}

/// Map two subtrees known to be isomorphic (equal content hash). Children are
/// paired by hash, not position, so the correspondence is correct even for the
/// order-insensitive nodes (`Record`, `CollectionUnion`), whose children may be
/// stored in a different order despite equal hashes. Already-matched nodes are
/// skipped so a recursive mapping can never overwrite an existing pairing —
/// reachable when a subtree shape repeats and two separate anchors descend into
/// overlapping dst regions.
fn map_isomorphic(s: &Indexed, d: &Indexed, u: usize, w: usize, m: &mut Matching) {
    m.map(u, w);
    let wc = &d.nodes[w].children;
    let mut used = vec![false; wc.len()];
    for &cu in &s.nodes[u].children {
        if m.src_matched(cu) {
            continue;
        }
        let hu = s.nodes[cu].hash;
        if let Some(pos) = wc
            .iter()
            .enumerate()
            .position(|(i, &cw)| !used[i] && !m.dst_matched(cw) && d.nodes[cw].hash == hu)
        {
            used[pos] = true;
            map_isomorphic(s, d, cu, wc[pos], m);
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 2: bottom-up container recovery
// ---------------------------------------------------------------------------

fn bottom_up(s: &Indexed, d: &Indexed, m: &mut Matching) {
    // Children before parents: process unmatched interior nodes by ascending
    // height, so a container's similarity reflects matches already made below.
    let mut order: Vec<usize> = (0..s.len())
        .filter(|&i| !s.nodes[i].children.is_empty())
        .collect();
    order.sort_by_key(|&i| s.nodes[i].height);

    for u in order {
        if m.src_matched(u) {
            continue;
        }
        // Where do u's matched descendants land in dst?
        let targets: Vec<usize> = (u + 1..s.subtree_end(u))
            .filter_map(|x| m.src_to_dst[x])
            .collect();
        if targets.is_empty() {
            continue;
        }

        // Two questions, two measures. *Containment* decides whether `w` is a
        // plausible counterpart at all; *tightness* picks between the plausible
        // ones. Conflating them is what made a container that gained a
        // statement look implausible — see the note on the two below.
        let src_desc = f64::from(s.nodes[u].size - 1);
        let mut best: Option<(usize, f64)> = None;
        for w in 0..d.len() {
            if d.nodes[w].children.is_empty()
                || m.dst_matched(w)
                || d.nodes[w].kind != s.nodes[u].kind
            {
                continue;
            }
            let common = targets.iter().filter(|&&t| d.is_descendant(t, w)).count();
            if common == 0 {
                continue;
            }
            let dst_desc = f64::from(d.nodes[w].size - 1);
            // Containment (the overlap coefficient): "is one of these two
            // essentially inside the other?" Normalizing by the *smaller*
            // subtree is what makes it survive an edit that grows or shrinks
            // one side — the case Dice alone gets wrong.
            let contained = common as f64 / src_desc.min(dst_desc);
            if contained < SIMILARITY_THRESHOLD {
                continue;
            }
            // Tightness (Dice): among the plausible candidates — which are
            // necessarily nested in one another, since they all contain the
            // same matched descendants — the growing denominator prefers the
            // innermost, i.e. the container that fits `u` best.
            let dice = 2.0 * common as f64 / (src_desc + dst_desc);
            if best.is_none_or(|(_, b)| dice > b) {
                best = Some((w, dice));
            }
        }

        if let Some((w, _)) = best {
            m.map(u, w);
            recover(s, d, u, w, m);
        }
    }
}

/// Optimally align the still-unmatched interiors of a freshly recovered
/// container pair `(u, w)`.
///
/// Steps 1–2 match by *whole-subtree* equality and by container similarity;
/// neither can pair two subtrees that are nearly identical but differ somewhere
/// inside. That leaves a real gap: an edit deep in a large subtree would report
/// the whole surrounding structure as deleted-and-reinserted. This step closes
/// it by computing the minimum-cost edit mapping between the two subtrees
/// ([`ted::mapping`]) and adopting every pair it aligns whose nodes are
/// same-kind and still unmatched.
///
/// The mapping is *optimal* under unit edit costs. (GumTree reaches for RTED,
/// which computes the same optimal mapping as the Zhang–Shasha dynamic program
/// used here, faster, by choosing a better decomposition strategy — the
/// difference is asymptotic cost, not the result.) Subtrees above
/// [`MAX_RECOVERY_SIZE`] are left to steps 1–2 alone.
fn recover(s: &Indexed, d: &Indexed, u: usize, w: usize, m: &mut Matching) {
    if s.nodes[u].size > MAX_RECOVERY_SIZE || d.nodes[w].size > MAX_RECOVERY_SIZE {
        return;
    }
    for (x, y) in ted::mapping(s, u, d, w) {
        if !m.src_matched(x) && !m.dst_matched(y) && s.nodes[x].kind == d.nodes[y].kind {
            m.map(x, y);
        }
    }
}

/// Zhang–Shasha tree edit distance, specialized to recovering the *mapping*
/// between two subtrees of already-indexed trees.
///
/// Node labels are content hashes: relabelling is free when the hashes agree
/// and costs one otherwise; deleting or inserting a node costs one. The
/// returned mapping is the node correspondence induced by a minimum-cost edit
/// script.
mod ted {
    use super::Indexed;

    /// A subtree flattened into post-order, the indexing Zhang–Shasha needs.
    /// Post-order numbering is 1-based; index 0 is the empty-forest sentinel
    /// used by the dynamic program's boundary row and column.
    struct Post {
        /// `global[k]` is the enclosing [`Indexed`] index of post-order node `k`.
        global: Vec<usize>,
        /// `leftmost[k]` is the post-order index of `k`'s leftmost-leaf
        /// descendant. In post-order a subtree occupies a contiguous range
        /// ending at its root, so this is just `k - size(k) + 1`.
        leftmost: Vec<usize>,
        /// Nodes that head a distinct `leftmost` chain — the roots of the
        /// subproblems the dynamic program is decomposed over.
        keyroots: Vec<usize>,
    }

    impl Post {
        fn build(t: &Indexed, root: usize) -> Self {
            let mut global = vec![usize::MAX]; // sentinel at index 0
            fn walk(t: &Indexed, n: usize, global: &mut Vec<usize>) {
                for &c in &t.nodes[n].children {
                    walk(t, c, global);
                }
                global.push(n);
            }
            walk(t, root, &mut global);

            let leftmost: Vec<usize> = (0..global.len())
                .map(|k| {
                    if k == 0 {
                        0
                    } else {
                        k - t.nodes[global[k]].size as usize + 1
                    }
                })
                .collect();

            // The last node of each distinct `leftmost` chain is its keyroot.
            let mut last_of_chain = vec![0usize; global.len()];
            for k in 1..global.len() {
                last_of_chain[leftmost[k]] = k;
            }
            let mut keyroots: Vec<usize> = last_of_chain
                .into_iter()
                .skip(1)
                .filter(|&k| k > 0)
                .collect();
            keyroots.sort_unstable();
            keyroots.dedup();

            Post {
                global,
                leftmost,
                keyroots,
            }
        }

        fn n(&self) -> usize {
            self.global.len() - 1
        }
    }

    /// The forest-distance table for one keyroot pair, indexed
    /// `[i - l(ki) + 1][j - l(kj) + 1]` with row/column 0 the empty forest.
    struct Forest {
        rows: usize,
        cols: usize,
        d: Vec<u32>,
    }

    impl Forest {
        fn get(&self, i: usize, j: usize) -> u32 {
            self.d[i * self.cols + j]
        }
        fn set(&mut self, i: usize, j: usize, v: u32) {
            self.d[i * self.cols + j] = v;
        }
    }

    /// Relabelling cost: free when the two nodes are the same computation.
    fn relabel(a: &Indexed, ga: usize, b: &Indexed, gb: usize) -> u32 {
        u32::from(a.nodes[ga].hash != b.nodes[gb].hash)
    }

    /// Fill the forest-distance table for keyroot pair `(ki, kj)`, writing any
    /// whole-subtree distances it settles into `tree`.
    fn forest_dist(
        s: &Indexed,
        ps: &Post,
        d: &Indexed,
        pd: &Post,
        ki: usize,
        kj: usize,
        tree: &mut [u32],
    ) -> Forest {
        let (li, lj) = (ps.leftmost[ki], pd.leftmost[kj]);
        let (rows, cols) = (ki - li + 2, kj - lj + 2);
        let mut f = Forest {
            rows,
            cols,
            d: vec![0; rows * cols],
        };
        for i in 1..rows {
            f.set(i, 0, f.get(i - 1, 0) + 1);
        }
        for j in 1..cols {
            f.set(0, j, f.get(0, j - 1) + 1);
        }
        for i in 1..rows {
            for j in 1..cols {
                let (pi, pj) = (li + i - 1, lj + j - 1); // post-order indices
                let del = f.get(i - 1, j) + 1;
                let ins = f.get(i, j - 1) + 1;
                if ps.leftmost[pi] == li && pd.leftmost[pj] == lj {
                    // Both are whole subtrees rooted here: this cell *is* the
                    // tree distance, so record it for the outer decomposition.
                    let ren = f.get(i - 1, j - 1) + relabel(s, ps.global[pi], d, pd.global[pj]);
                    let best = del.min(ins).min(ren);
                    f.set(i, j, best);
                    tree[(pi - 1) * pd.n() + (pj - 1)] = best;
                } else {
                    // Peel both subtrees off and reuse their settled distance.
                    let (bi, bj) = (ps.leftmost[pi] - li, pd.leftmost[pj] - lj);
                    let sub = f.get(bi, bj) + tree[(pi - 1) * pd.n() + (pj - 1)];
                    f.set(i, j, del.min(ins).min(sub));
                }
            }
        }
        f
    }

    /// The node correspondence induced by a minimum-cost edit script between
    /// the subtree of `s` rooted at `su` and the subtree of `d` rooted at `dw`.
    /// Pairs are `(Indexed` index in `s`, `Indexed` index in `d)`.
    pub(super) fn mapping(s: &Indexed, su: usize, d: &Indexed, dw: usize) -> Vec<(usize, usize)> {
        let ps = Post::build(s, su);
        let pd = Post::build(d, dw);
        let mut tree = vec![0u32; ps.n() * pd.n()];
        for &ki in &ps.keyroots {
            for &kj in &pd.keyroots {
                forest_dist(s, &ps, d, &pd, ki, kj, &mut tree);
            }
        }

        // Trace an optimal script back through the same recurrence. Each entry
        // of `todo` is a keyroot pair whose forest table has to be re-derived;
        // re-deriving costs one table each and there are `O(n + m)` of them,
        // which is cheaper than retaining every table from the fill above.
        let mut out = Vec::new();
        let mut todo = vec![(ps.n(), pd.n())];
        while let Some((ki, kj)) = todo.pop() {
            let f = forest_dist(s, &ps, d, &pd, ki, kj, &mut tree);
            let (li, lj) = (ps.leftmost[ki], pd.leftmost[kj]);
            let (mut i, mut j) = (f.rows - 1, f.cols - 1);
            while i > 0 || j > 0 {
                if i > 0 && f.get(i, j) == f.get(i - 1, j) + 1 {
                    i -= 1; // delete
                } else if j > 0 && f.get(i, j) == f.get(i, j - 1) + 1 {
                    j -= 1; // insert
                } else {
                    let (pi, pj) = (li + i - 1, lj + j - 1);
                    if ps.leftmost[pi] == li && pd.leftmost[pj] == lj {
                        out.push((ps.global[pi], pd.global[pj]));
                        i -= 1;
                        j -= 1;
                    } else {
                        todo.push((pi, pj));
                        i = ps.leftmost[pi] - li;
                        j = pd.leftmost[pj] - lj;
                    }
                }
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

fn classify<'a>(s: &Indexed<'a>, d: &Indexed<'a>, m: &Matching) -> Diff<'a> {
    let in_place = align_children(s, d, m);
    let mut out = Diff::default();
    for (u, &dst) in m.src_to_dst.iter().enumerate() {
        match dst {
            Some(w) => out.matched.push(Match {
                src: s.nodes[u].expr,
                dst: d.nodes[w].expr,
                content: if s.nodes[u].hash == d.nodes[w].hash {
                    Content::Same
                } else {
                    Content::Changed
                },
                placement: if in_place[u] {
                    Placement::InPlace
                } else {
                    Placement::Moved
                },
            }),
            None => out.deleted.push(s.nodes[u].expr),
        }
    }
    for (w, &src) in m.dst_to_src.iter().enumerate() {
        if src.is_none() {
            out.new.push(d.nodes[w].expr);
        }
    }
    out
}

/// Decide, for every matched src node, whether it kept its position — the
/// child-alignment step of Chawathe et al.'s edit-script derivation, which
/// GumTree inherits.
///
/// A node is in place iff it hangs off the corresponding parent **and** it did
/// not cross any of its matched siblings. Within one matched container pair,
/// "did not cross" is decided by taking a longest increasing subsequence of the
/// matched children's destination positions: the children on it kept their
/// relative order and stay put, and the rest are the minimum set of moves that
/// explains the permutation. Order-insensitive containers skip the test —
/// permuting their children is not an edit at all.
fn align_children(s: &Indexed, d: &Indexed, m: &Matching) -> Vec<bool> {
    let mut in_place = vec![false; s.len()];

    for (u, &dst) in m.src_to_dst.iter().enumerate() {
        // A matched pair of roots has no parent to disagree with.
        if let Some(w) = dst
            && s.nodes[u].parent.is_none()
            && d.nodes[w].parent.is_none()
        {
            in_place[u] = true;
        }
    }

    for pu in 0..s.len() {
        let Some(pw) = m.src_to_dst[pu] else {
            continue;
        };
        // Children of `pu` that matched into a child of `pw`, with the
        // destination slot each landed in. A child matched somewhere else in
        // the target tree is absent here, and so stays `Moved`.
        let paired: Vec<(usize, usize)> = s.nodes[pu]
            .children
            .iter()
            .filter_map(|&c| {
                let w = m.src_to_dst[c]?;
                let slot = d.nodes[pw].children.iter().position(|&x| x == w)?;
                Some((c, slot))
            })
            .collect();

        if s.nodes[pu].unordered || d.nodes[pw].unordered {
            for (c, _) in paired {
                in_place[c] = true;
            }
            continue;
        }
        let slots: Vec<usize> = paired.iter().map(|&(_, slot)| slot).collect();
        for i in longest_increasing(&slots) {
            in_place[paired[i].0] = true;
        }
    }
    in_place
}

/// Indices of one longest strictly-increasing subsequence of `seq`, ascending.
/// Patience sorting: `tails[k]` is the index of the smallest tail among the
/// increasing subsequences of length `k + 1` found so far.
fn longest_increasing(seq: &[usize]) -> Vec<usize> {
    let mut tails: Vec<usize> = Vec::new();
    let mut prev: Vec<Option<usize>> = vec![None; seq.len()];
    for i in 0..seq.len() {
        let pos = tails.partition_point(|&t| seq[t] < seq[i]);
        if pos > 0 {
            prev[i] = Some(tails[pos - 1]);
        }
        if pos == tails.len() {
            tails.push(i);
        } else {
            tails[pos] = i;
        }
    }
    let mut out = Vec::new();
    let mut cur = tails.last().copied();
    while let Some(i) = cur {
        out.push(i);
        cur = prev[i];
    }
    out.reverse();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::content_hash::content_hash;
    use crate::ccl::{ArithmeticKind, BinOpKind, Lit, Type, TypedExpr, TypedExprNode};

    fn var(name: &str) -> TypedExpr {
        TypedExpr::var(name)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    fn str_lit(s: &str) -> TypedExpr {
        TypedExpr::lit(Lit::String(s.into()))
    }
    fn add(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Add), r)
    }
    fn mul(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Mul), r)
    }
    fn let_in(name: &str, value: TypedExpr, body: TypedExpr) -> TypedExpr {
        TypedExpr::let_bind(name, value, body)
    }

    /// The src sides of the matches whose content changed, as a convenience for
    /// asserting "this literal is an update, not a delete+insert".
    fn updated_pairs<'a>(d: &Diff<'a>) -> Vec<(&'a TypedExpr, &'a TypedExpr)> {
        d.updated().map(|m| (m.src, m.dst)).collect()
    }

    #[test]
    fn identical_programs_are_entirely_shared() {
        let a = let_in("x", int(1), add(var("x"), var("y")));
        let b = a.clone();
        let r = diff(&a, &b);
        assert!(r.is_identical());
        // The root, and every node under it, is shared.
        assert!(r.shared().any(|m| std::ptr::eq(m.src, &a)));
        assert_eq!(r.shared().count(), 5); // Let, 1, BinOp, x, y
    }

    #[test]
    fn motivating_example_isolates_one_inserted_node() {
        // ("idx", index)  ->  ("idx", 2 * index)
        let v1 = TypedExpr::tuple(vec![str_lit("idx"), var("index")]);
        let v2 = TypedExpr::tuple(vec![str_lit("idx"), mul(int(2), var("index"))]);
        let r = diff(&v1, &v2);

        // Nothing is deleted: the old value `index` survives inside `2 * index`.
        assert!(r.deleted.is_empty(), "deleted: {:?}", r.deleted);
        // The divergence is one site: a single new *container* (the `2 * _`
        // BinOp). Its literal `2` is also new, but `index` is reused, not
        // re-inserted — that is the whole point of structural sharing.
        assert_eq!(
            r.new
                .iter()
                .filter(|e| matches!(e.node, TypedExprNode::BinOp { .. }))
                .count(),
            1,
            "new: {:?}",
            r.new
        );
        assert!(
            !r.new
                .iter()
                .any(|e| matches!(&e.node, TypedExprNode::Var(_))),
            "the shared `index` must not be re-inserted",
        );
        // The unchanged key and the surviving `index` are shared.
        assert!(
            r.shared()
                .any(|m| content_hash(m.src) == content_hash(&str_lit("idx")))
        );
        assert!(
            r.shared()
                .any(|m| content_hash(m.src) == content_hash(&var("index")))
        );
        // The two tuples correspond but differ → an update (a Versioned site).
        assert!(
            r.updated()
                .any(|m| matches!(m.src.node, TypedExprNode::Tuple(_)))
        );
    }

    #[test]
    fn inserting_a_statement_does_not_desync_the_spine() {
        // let a = 1 in (let b = 2 in a + b)
        // let a = 1 in (let c = 9 in (let b = 2 in a + b))   <- middle insertion
        let tail = || let_in("b", int(2), add(var("a"), var("b")));
        let v1 = let_in("a", int(1), tail());
        let v2 = let_in("a", int(1), let_in("c", int(9), tail()));
        let r = diff(&v1, &v2);

        // The unchanged tail subtree anchors as shared rather than the whole
        // body below `a` reading as rewritten.
        let tail_expr = tail();
        assert!(
            r.shared()
                .any(|m| content_hash(m.src) == content_hash(&tail_expr)),
            "tail subtree should be shared",
        );
        // Nothing deleted; the inserted `let c = 9` shows up as new.
        assert!(r.deleted.is_empty(), "deleted: {:?}", r.deleted);
        assert!(!r.new.is_empty());
        assert!(
            r.new
                .iter()
                .any(|e| matches!(e.node, TypedExprNode::Let { .. }))
        );
    }

    #[test]
    fn unrelated_programs_share_nothing_structural() {
        let a = add(var("p"), var("q"));
        let b = str_lit("hello");
        let r = diff(&a, &b);
        assert_eq!(r.shared().count(), 0);
        // a's nodes are all deleted, b's all new.
        assert_eq!(r.deleted.len(), 3); // BinOp, p, q
        assert_eq!(r.new.len(), 1); // the string
    }

    #[test]
    fn repeated_subtrees_match_without_corruption() {
        // Two identical `x + 1` subtrees, one edited to `x + 2`. A repeated
        // shape means top-down anchors the duplicates arbitrarily and recursive
        // mappings can touch overlapping dst regions — the already-matched guard
        // in `map_isomorphic` keeps that sound. The diff should localize to the
        // edited literal, not rewrite the world.
        let v1 = TypedExpr::tuple(vec![add(var("x"), int(1)), add(var("x"), int(1))]);
        let v2 = TypedExpr::tuple(vec![add(var("x"), int(1)), add(var("x"), int(2))]);
        let r = diff(&v1, &v2);
        assert!(r.deleted.is_empty(), "deleted: {:?}", r.deleted);
        assert!(r.new.is_empty(), "new: {:?}", r.new);
        // The one divergence is the literal, recovered as an in-place update.
        let lit_updates: Vec<_> = updated_pairs(&r)
            .into_iter()
            .filter(|(s, _)| matches!(s.node, TypedExprNode::Lit(_)))
            .collect();
        assert_eq!(lit_updates.len(), 1, "exactly one literal changed");
        assert!(matches!(
            lit_updates[0].0.node,
            TypedExprNode::Lit(Lit::Int(1))
        ));
        assert!(matches!(
            lit_updates[0].1.node,
            TypedExprNode::Lit(Lit::Int(2))
        ));
        // An unchanged `x + 1` (and its operands) survive as shared.
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::BinOp { .. })),
            "an unchanged x+1 stays shared",
        );
    }

    // -----------------------------------------------------------------------
    // Placement: moves, reorders, and the order-insensitive exemption
    // -----------------------------------------------------------------------

    #[test]
    fn relocated_subtree_is_matched_and_labelled_moved() {
        // Content-hash matching is position-independent, so a subtree relocated
        // to a new parent is recognized (shared content) rather than reported
        // as a delete + insert — and the placement axis says it moved.
        let moved = add(var("a"), var("b"));
        let v1 = TypedExpr::tuple(vec![moved.clone(), int(9)]);
        // `a + b` is now nested inside `(a + b) * 2`, in the other tuple slot.
        let v2 = TypedExpr::tuple(vec![int(9), mul(moved.clone(), int(2))]);
        let r = diff(&v1, &v2);

        let relocated: Vec<_> = r
            .moved()
            .filter(|m| content_hash(m.src) == content_hash(&moved))
            .collect();
        assert_eq!(relocated.len(), 1, "`a + b` is reported moved, once");
        assert_eq!(
            relocated[0].content,
            Content::Same,
            "its content is unchanged — the two axes are independent",
        );
        // The move is reported at the subtree root only; `a` and `b` came along.
        assert!(
            !r.moved()
                .any(|m| matches!(m.src.node, TypedExprNode::Var(_))),
            "a moved subtree's descendants stay in place relative to it",
        );
        assert!(r.deleted.is_empty(), "the moved subtree is not deleted");
    }

    #[test]
    fn sibling_swap_moves_the_minimum_number_of_children() {
        // Tuples are ordered: swapping two elements leaves both matched, and
        // exactly one of them has to move to explain the permutation.
        let (tup_12, tup_21) = (
            TypedExpr::tuple(vec![int(1), int(2)]),
            TypedExpr::tuple(vec![int(2), int(1)]),
        );
        let r = diff(&tup_12, &tup_21);
        assert!(
            r.deleted.is_empty() && r.new.is_empty(),
            "no element is lost"
        );
        assert_eq!(r.shared().count(), 2, "both elements stay shared");
        // A tuple is ordered, so the container's own content changed too.
        assert!(
            r.updated()
                .any(|m| matches!(m.src.node, TypedExprNode::Tuple(_)))
        );
        assert_eq!(r.moved().count(), 1, "one crossing explains the swap");
        assert!(matches!(
            r.moved().next().unwrap().src.node,
            TypedExprNode::Lit(_)
        ));
    }

    #[test]
    fn record_field_reorder_is_not_a_move() {
        let rec = |fields: Vec<(&str, TypedExpr)>| TypedExpr {
            ty: Type::Hole,
            node: TypedExprNode::Record(
                fields
                    .into_iter()
                    .map(|(n, e)| (n.to_string(), e))
                    .collect(),
            ),
            user_annotation: None,
        };
        // Records are order-insensitive, so a field swap is a no-op to the diff
        // — on the content axis *and* the placement axis.
        let (rec_ab, rec_ba) = (
            rec(vec![("a", int(1)), ("b", int(2))]),
            rec(vec![("b", int(2)), ("a", int(1))]),
        );
        let r = diff(&rec_ab, &rec_ba);
        assert!(r.is_identical(), "record field reorder is a no-op");
    }

    #[test]
    fn shifted_siblings_are_not_moves() {
        // Inserting a statement shifts everything after it by one slot. That is
        // an insertion, not a pile of moves: the longest increasing subsequence
        // keeps the untouched children in place.
        let v1 = TypedExpr::tuple(vec![int(1), int(2), int(3)]);
        let v2 = TypedExpr::tuple(vec![int(9), int(1), int(2), int(3)]);
        let r = diff(&v1, &v2);
        assert_eq!(r.moved().count(), 0, "a shift is not a move");
        assert_eq!(r.new.len(), 1);
        assert!(r.deleted.is_empty());
    }

    #[test]
    fn an_ambiguous_leaf_anchors_where_it_belongs() {
        // `(1, v > 0)` -> `(1, v > 1)`. The new version has *two* `1` leaves,
        // so the tuple's `1` has two isomorphic candidates and the choice is
        // not free: anchoring it to the guard's `1` would strand the tuple slot
        // (a spurious insert), strand `0` (a spurious delete), and report a move
        // that never happened. Structural position picks the tuple slot, and
        // optimal recovery then reads the guard edit as `0 -> 1`.
        let guard = |n: i64| {
            TypedExpr::binop(
                var("v"),
                BinOpKind::Compare(crate::ccl::CompareKind::Greater),
                int(n),
            )
        };
        let v1 = TypedExpr::tuple(vec![int(1), guard(0)]);
        let v2 = TypedExpr::tuple(vec![int(1), guard(1)]);
        let r = diff(&v1, &v2);

        assert!(r.deleted.is_empty(), "deleted: {:?}", r.deleted);
        assert!(r.new.is_empty(), "new: {:?}", r.new);
        assert_eq!(r.moved().count(), 0, "nothing actually moved");
        assert!(
            r.updated().any(|m| {
                matches!(m.src.node, TypedExprNode::Lit(Lit::Int(0)))
                    && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(1)))
            }),
            "the guard threshold reads as one in-place update",
        );
        // The tuple's own `1` kept its slot rather than being reused elsewhere.
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))
                    && m.placement == Placement::InPlace),
        );
    }

    #[test]
    fn variant_ctor_changes_are_detected() {
        // `VariantCtor` has no surface syntax (later passes introduce it), so
        // build it directly.
        let some1 = TypedExpr::variant_ctor("Some", int(1));

        // Payload change `1 -> 2`. Nothing under the ctor is isomorphic, so
        // there is no seed for container recovery — but the two ctors are the
        // two programs' *roots*, which correspond by construction, and phase 3
        // then aligns the payloads. The edit reads as an update, not a rebuild.
        let some2 = TypedExpr::variant_ctor("Some", int(2));
        let r = diff(&some1, &some2);
        assert!(r.deleted.is_empty() && r.new.is_empty(), "{r:?}");
        assert!(r.updated().any(|m| {
            matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))
                && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(2)))
        }));

        // Same one level down, where the ctor is not itself a root: the tuple
        // roots correspond, and recovery reaches the payload through them.
        let nested =
            |n: i64| TypedExpr::tuple(vec![int(0), TypedExpr::variant_ctor("Some", int(n))]);
        let (n1, n2) = (nested(1), nested(2));
        let r = diff(&n1, &n2);
        assert!(r.deleted.is_empty() && r.new.is_empty(), "{r:?}");
        assert!(r.updated().any(|m| {
            matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))
                && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(2)))
        }));

        // Tag change `Some -> None`: the payload `1` stays shared and seeds
        // bottom-up recovery, so the ctor is recognized as *updated* (the tag
        // changed in place) rather than rebuilt.
        let none1 = TypedExpr::variant_ctor("None", int(1));
        let r = diff(&some1, &none1);
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))),
            "the unchanged payload stays shared",
        );
        assert!(
            r.updated()
                .any(|m| matches!(m.src.node, TypedExprNode::VariantCtor { .. })),
            "the tag change marks the ctor updated",
        );
    }

    // -----------------------------------------------------------------------
    // Real lowered / inferred CCL, from CHL source
    // -----------------------------------------------------------------------

    /// Pre-uniquify CCL (`Raw` names, before inference), via the public API.
    fn lower(code: &str) -> TypedExpr {
        compile_to(code, CompileStage::Lowered).expect("compile to lowered stage should succeed")
    }

    /// Post-inference CCL (uniquified, fully typed), via the public API — the
    /// differ's other supported mode.
    fn lower_and_infer(code: &str) -> TypedExpr {
        compile_to(code, CompileStage::Inferred).expect("compile to inferred stage should succeed")
    }

    // Realistic CHL programs exercising records, list comprehensions, filters,
    // aggregates, projections, joins, def/yield generators, groupby, induction
    // accumulators, and transactional registers. Between them they cover every
    // node kind that reaches these two stages: `Defer`/`Feed` (generators),
    // `Case` (guards), `Cast` (comprehension filters), `For`/`MutWrite`
    // (accumulators), and `Begin` (transaction blocks). `LetRec` and `Transact`
    // are born *below* the inferred stage — the mutability phases build them —
    // so no source program can exercise them here; `content_hash` covers them
    // structurally instead.
    const FILTER_AGG: &str = "users = [\n  (name=\"alice\", age=30, score=85),\n  (name=\"bob\", age=17, score=92),\n]\nsum([u.score for u in users if u.age >= 18])\n";
    const FILTER_AGG_21: &str = "users = [\n  (name=\"alice\", age=30, score=85),\n  (name=\"bob\", age=17, score=92),\n]\nsum([u.score for u in users if u.age >= 21])\n";
    const GENERATORS: &str = "def positives(xs):\n    for x in xs:\n        if x > 0:\n            yield x\n\ndef squared(xs):\n    for x in xs:\n        yield x * x\n\nmax(squared(positives([-3, 4, -1, 2, 5, -7])))\n";
    const JOIN: &str = "users = [(id=1, name=\"alice\"), (id=2, name=\"bob\")]\norders = [(user_id=1, amount=50), (user_id=2, amount=75)]\n[(customer=u.name, total=o.amount) for u in users for o in orders if u.id == o.user_id]\n";
    const GROUPBY: &str = "sales = [(region=\"west\", amount=100), (region=\"east\", amount=50)]\n[sum([s.amount for s in g]) for g in groupby(sales, \\r -> r.region)]\n";
    const ACCUM: &str = "acc := 0\nfor i in [1, 2, 3, 4, 5]:\n    acc := acc + i\nacc\n";
    const TXN: &str = "pool: Mut(Int, Txn) := 100\nreqs = [1, 2, 3]\nfor r in reqs:\n    with begin():\n        pool := pool - r\n";

    #[test]
    fn lowered_source_is_stable_across_independent_compilations() {
        // The point of diffing pre-uniquify on Raw names: lowering the same
        // source twice, through independent contexts, yields trees that diff as
        // identical — no spurious divergence from fresh binder identities.
        let src = "x = 1\ny = x + 2\ny\n";
        let (a, b) = (lower(src), lower(src));
        let r = diff(&a, &b);
        assert!(r.is_identical(), "{r:?}");
        assert!(r.shared().count() > 0);
    }

    #[test]
    fn lowered_one_literal_edit_is_localized() {
        // A single changed literal in *real* lowered CCL. Optimal recovery pairs
        // the changed leaf with its counterpart, so the edit reads as one
        // in-place update rather than a delete plus an insert — and nothing
        // around it is disturbed.
        let v1 = lower("x = 1\ny = x + 2\ny\n");
        let v2 = lower("x = 1\ny = x + 3\ny\n");
        let r = diff(&v1, &v2);

        assert!(r.deleted.is_empty(), "deleted: {:?}", r.deleted);
        assert!(r.new.is_empty(), "new: {:?}", r.new);
        assert_eq!(r.moved().count(), 0, "nothing moved");
        let lit_updates: Vec<_> = r
            .updated()
            .filter(|m| matches!(m.src.node, TypedExprNode::Lit(_)))
            .collect();
        assert_eq!(lit_updates.len(), 1, "exactly one literal changed");
        assert!(matches!(
            lit_updates[0].src.node,
            TypedExprNode::Lit(Lit::Int(2))
        ));
        assert!(matches!(
            lit_updates[0].dst.node,
            TypedExprNode::Lit(Lit::Int(3))
        ));
        // The unchanged `x = 1` binding value survives as shared.
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))),
            "the unchanged literal 1 should be shared",
        );
    }

    #[test]
    fn adding_a_statement_is_an_insertion_not_a_rewrite() {
        // `a = 1; a` gains a substantial statement. The root `let` has only two
        // descendants and the new one brings a dozen, so a similarity test that
        // weighs the two subtrees *together* scores the root far too low to
        // pair — and the whole program reads as deleted-and-reinserted for a
        // one-statement edit. The roots correspond by construction instead.
        let v1 = lower("a = 1\na\n");
        let v2 = lower("a = 1\nb = sum([i * 2 for i in [1,2,3]])\na + b\n");
        let r = diff(&v1, &v2);
        assert!(
            r.deleted.is_empty(),
            "nothing was removed, so nothing should be deleted: {:?}",
            r.deleted
        );
        assert!(
            r.updated().any(
                |m| std::ptr::eq(m.src, &v1) && matches!(m.src.node, TypedExprNode::Let { .. })
            ),
            "the root corresponds, as an update",
        );
        // The pre-existing `a = 1` value is still recognized.
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1)))),
        );
    }

    #[test]
    fn a_container_that_grew_still_corresponds() {
        // The same shape one level down, where root anchoring cannot help: a
        // `def` body gains a statement. The enclosing container is matched on
        // *containment* of what it already had, not on its size relative to
        // what was added.
        let v1 = lower("def f(x):\n    a = 1\n    a + x\nf(2)\n");
        let v2 = lower(
            "def f(x):\n    a = 1\n    b = sum([i * 2 for i in [1,2,3]])\n    a + x + b\nf(2)\n",
        );
        let r = diff(&v1, &v2);
        assert!(
            r.deleted.is_empty(),
            "the grown container corresponds rather than being rebuilt: {:?}",
            r.deleted
        );
        assert!(
            r.shared().count() >= 6,
            "the untouched body is still shared"
        );
    }

    /// Assert a construct survives the two properties that matter on real
    /// lowered CCL: lowering the same source twice diffs as identical, and an
    /// edit that *wraps* an existing subexpression localizes (nothing deleted,
    /// the wrapper shows up as new, the bulk stays shared).
    fn assert_stable_and_localizing(src: &str, edited: &str) {
        let (a, b) = (lower(src), lower(src));
        let stable = diff(&a, &b);
        assert!(stable.is_identical(), "same source must diff as identical");

        let v2 = lower(edited);
        let edit = diff(&a, &v2);
        assert!(
            edit.deleted.is_empty(),
            "no spurious deletions, got {}",
            edit.deleted.len()
        );
        assert!(
            edit.new
                .iter()
                .any(|e| matches!(e.node, TypedExprNode::BinOp { .. })),
            "the wrapping operator should show up as new",
        );
        assert!(
            edit.shared().count() > edit.new.len(),
            "the bulk should stay shared"
        );
    }

    #[test]
    fn induction_accumulator_is_stable_and_localizes() {
        // `acc := acc + i` inside a `for` lowers to a `For` carrying a
        // `MutWrite`; the loop binder is hashed positionally, so none of the
        // mutation machinery leaks into the diff.
        assert_stable_and_localizing(
            ACCUM,
            "acc := 0\nfor i in [1, 2, 3, 4, 5]:\n    acc := acc + i * 2\nacc\n",
        );
    }

    #[test]
    fn transactional_register_is_stable_and_localizes() {
        // A `Mut(Int, Txn)` register written under `with begin():` lowers to a
        // `Begin` block wrapping the `MutWrite`. Same story: stable across
        // compilations, and an edit inside the block localizes to it.
        assert_stable_and_localizing(
            TXN,
            "pool: Mut(Int, Txn) := 100\nreqs = [1, 2, 3]\nfor r in reqs:\n    with begin():\n        pool := pool - r - 1\n",
        );
    }

    #[test]
    fn rich_programs_are_stable_across_lowerings() {
        // Records, list comprehensions, filters, aggregates, projections, joins,
        // def/yield generators, and groupby all diff as identical when the same
        // source is lowered twice. `groupby` in particular exercises the
        // free-variable seam: lowering uniquifies the comprehension source, so
        // some binders carry run-varying `uid`s — matching free variables by
        // spelling (not uid) keeps the diff stable regardless.
        for src in [FILTER_AGG, GENERATORS, JOIN, GROUPBY, ACCUM, TXN] {
            let (a, b) = (lower(src), lower(src));
            let r = diff(&a, &b);
            assert!(
                r.is_identical(),
                "expected identical diff for:\n{src}\n{r:?}"
            );
        }
    }

    #[test]
    fn comprehension_filter_predicate_change_is_visible() {
        // A comprehension filter lowers into a cast-target *refinement
        // predicate* — a term living in a type position. The content hash is
        // type-aware (and the differ descends into refinement predicate terms),
        // so a threshold change is visible and localizes to the threshold.
        let (v1, v2) = (lower(FILTER_AGG), lower(FILTER_AGG_21));
        let r = diff(&v1, &v2);
        assert!(
            r.updated().any(|m| {
                matches!(m.src.node, TypedExprNode::Lit(Lit::Int(18)))
                    && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(21)))
            }),
            "the threshold change should read as one in-place update: {r:?}",
        );
    }

    #[test]
    fn diff_is_robust_to_uid_nondeterminism() {
        // Lowering uniquifies some subexpressions, minting globally-fresh,
        // run-varying uids, so two lowerings of `groupby` are *structurally*
        // unequal (`g1 != g2`) yet denote the same program. The diff must treat
        // them as identical — matching free variables by spelling, not uid.
        let (g1, g2) = (lower(GROUPBY), lower(GROUPBY));
        assert_ne!(g1, g2, "precondition: lowering assigns run-varying uids");
        assert!(diff(&g1, &g2).is_identical());
    }

    #[test]
    fn conditional_branches_diff_cleanly() {
        // A ternary `1 if v > 0 else 2` lowers to a guard-based `Case`.
        let base = "v = 5\n1 if v > 0 else 2\n";
        let (a, b) = (lower(base), lower(base));
        assert!(diff(&a, &b).is_identical());

        // Editing the else-branch value localizes to that literal.
        let (e1, e2) = (lower(base), lower("v = 5\n1 if v > 0 else 3\n"));
        let r = diff(&e1, &e2);
        assert!(r.updated().any(|m| {
            matches!(m.src.node, TypedExprNode::Lit(Lit::Int(2)))
                && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(3)))
        }));

        // Editing the guard threshold localizes to that literal.
        let (g1, g2) = (lower(base), lower("v = 5\n1 if v > 1 else 2\n"));
        let r = diff(&g1, &g2);
        assert!(r.updated().any(|m| {
            matches!(m.src.node, TypedExprNode::Lit(Lit::Int(0)))
                && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(1)))
        }));
    }

    #[test]
    fn inferred_program_is_stable_across_compilations() {
        // The post-inference mode works and is uid/Infer-robust: lowering +
        // uniquifying + inferring the same source twice (independent global
        // counters) diffs as identical. Same shared `diff` core as pre-uniquify.
        let (a, b) = (lower_and_infer(FILTER_AGG), lower_and_infer(FILTER_AGG));
        assert_ne!(
            a, b,
            "precondition: independent compilations assign fresh uids"
        );
        assert!(diff(&a, &b).is_identical());
    }

    #[test]
    fn inference_adds_type_signal() {
        // The body `(x, x)` is structurally identical in both programs — `x` is
        // free there, matched by spelling — so *pre-inference* (types still
        // `Hole`) the two bodies hash equal. After inference the element type
        // diverges (`x: Int` vs `x: String`), so the *same* subterm no longer
        // matches: types carry signal the term structure alone does not. This
        // is the payoff of diffing post-inference.
        let prog_int = "x = 1\n(x, x)\n";
        let prog_str = "x = \"a\"\n(x, x)\n";

        // The `(x, x)` tuple is the root `let`'s body.
        let body = |e: &TypedExpr| match &e.node {
            TypedExprNode::Let { body, .. } => content_hash(body),
            other => panic!("expected a top-level let, got {other:?}"),
        };

        assert_eq!(
            body(&lower(prog_int)),
            body(&lower(prog_str)),
            "pre-inference: the `(x, x)` bodies are indistinguishable",
        );
        assert_ne!(
            body(&lower_and_infer(prog_int)),
            body(&lower_and_infer(prog_str)),
            "post-inference: the element type (Int vs String) diverges",
        );
    }

    #[test]
    fn diff_programs_end_to_end_from_source() {
        // The public single-call entry: compile both sources to a stage and
        // diff, results delivered through the closure.
        //
        // A filter-threshold edit (`>= 18` → `>= 21`) is reflected at the
        // lowered stage.
        let changed = diff_programs(FILTER_AGG, FILTER_AGG_21, CompileStage::Lowered, |d| {
            d.updated().count()
        })
        .expect("compile + diff should succeed");
        assert!(changed > 0, "the edit is reflected");

        // Identical programs diff as identical at the inferred stage.
        let identical = diff_programs(FILTER_AGG, FILTER_AGG, CompileStage::Inferred, |d| {
            d.is_identical()
        })
        .expect("compile + diff should succeed");
        assert!(
            identical,
            "identical source diffs as identical post-inference"
        );
    }

    #[test]
    fn diff_programs_handles_source_using_programs() {
        // A program reading `stdin()` compiles end-to-end — the source is
        // registered for inference — and diffs cleanly against itself. Proves
        // the public API handles sources, not just literal programs.
        let prog = "[\"> \" + line for line in stdin()]\n";
        let identical = diff_programs(prog, prog, CompileStage::Inferred, |d| d.is_identical())
            .expect("stdin program should compile to the inferred stage and diff");
        assert!(identical);
    }
}
