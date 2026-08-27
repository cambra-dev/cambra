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
//! That classification is complete but says the same thing many times — every
//! *ancestor* of an edit has changed content, and every *descendant* of an
//! inserted subtree is new. [`Diff::divergences`] reduces it to the places the programs actually
//! disagree, and [`Diff::shared_roots`] to the largest pieces they have in
//! common. Those two are the actionable form: the first says where a version
//! guard goes, the second says what the two versions can compute once.
//!
//! # Phase-agnostic
//!
//! [`diff`] is a pure function of two [`TypedExpr`] trees and does not care
//! which pipeline phase produced them, so one implementation serves every
//! [`Phase`]: the caller chooses how much of the compiler's own
//! rewriting to diff through by choosing which trees to pass. Nothing in the
//! matcher is phase-specific — [`content_hash`] is uid-robust (free names by
//! spelling) and type-aware, which is what lets one core cover the lot,
//! including the `LetRec` and `Transact` shapes that exist only below the
//! mutability phases. Which phase answers which question is
//! `src/ccl/design/diffing.md`, "Which phase to diff".
//!
//! # Scope of this implementation
//!
//! This is the analysis, not a rewrite: it computes a correspondence and says
//! nothing about what to build from it. The one place it departs from full
//! GumTree is candidate selection in step 3, which picks the best-scoring
//! container greedily rather than solving a global assignment — GumTree does
//! the same.

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::mem::Discriminant;

use super::content_hash::{cast_target_predicates, content_hash, own_hash, resolved_hash};
use super::context::{CompileError, Phase, compile_to};
use super::scope::{ScopedItem, for_each_scoped_item};
use super::{Name, TypedExpr};

/// How much of the smaller of two subtrees must be common before container
/// recovery will pair them — see the containment gate in [`bottom_up`]. The
/// GumTree default, applied to a different measure than GumTree's.
const SIMILARITY_THRESHOLD: f64 = 0.5;

/// Node-count ceiling for the optimal recovery step ([`recover`]), applied to
/// each of the two subtrees it is asked to align.
///
/// Recovery runs Zhang–Shasha tree edit distance, which is `O(n²m²)` in the
/// worst case. When either subtree holds more than this many nodes, recovery
/// declines: the pair keeps whatever the top-down and bottom-up phases matched,
/// and their still-unmatched interiors are reported as deleted and new rather
/// than aligned node-for-node. GumTree's default, for the same reason.
const MAX_RECOVERY_SIZE: u32 = 100;

/// Whether a matched node's *content* changed, and if so whether the change is
/// the node's own. Orthogonal to [`Placement`]: a node can keep its content and
/// move, or stay put and change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Content {
    /// Equal content hash — identical computation, reusable wholesale.
    Same,
    /// The subtree differs but the node's own content does not: same literal,
    /// operator, binder, annotation and cast target, over children that
    /// changed. The disagreement is under it and is reported there — see
    /// [`Diff::divergences`].
    ChangedBelow,
    /// The node itself differs, by [`own_hash`]. Its children may differ
    /// too, and report separately.
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
#[derive(Debug)]
pub struct Diff<'a> {
    /// Every node correspondence, in source pre-order.
    pub matched: Vec<Match<'a>>,
    /// Source-only nodes: present in the old program, gone in the new.
    pub deleted: Vec<&'a TypedExpr>,
    /// Target-only nodes: introduced by the new program.
    pub new: Vec<&'a TypedExpr>,
    /// The old program's root — retained so a [`Diff`] can render itself.
    pub src_root: &'a TypedExpr,
    /// The new program's root.
    pub dst_root: &'a TypedExpr,
}

impl<'a> Diff<'a> {
    /// Correspondences whose content is identical ([`Content::Same`]) — the
    /// computation the two versions share, whether or not it moved.
    pub fn shared(&self) -> impl Iterator<Item = &Match<'a>> {
        self.matched.iter().filter(|m| m.content == Content::Same)
    }

    /// Correspondences whose subtree changed — "the same place in both
    /// programs, different content", whether the change is the node's own
    /// ([`Content::Changed`]) or entirely below it ([`Content::ChangedBelow`]).
    pub fn updated(&self) -> impl Iterator<Item = &Match<'a>> {
        self.matched.iter().filter(|m| m.content != Content::Same)
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

    /// The places the two programs disagree, reduced to the node that owns each
    /// disagreement, in new-program order (deletions, which have no place there,
    /// come last).
    ///
    /// This is the actionable form of the diff, and where a version guard would
    /// be placed. `matched`/`deleted`/`new` are complete but say the same thing
    /// many times: every *ancestor* of an edit has changed content too, and every
    /// *descendant* of an inserted subtree is itself new. One literal edited at
    /// the bottom of a forty-binding spine leaves forty-two changed nodes, of
    /// which exactly one is the edit. Divergences report that one.
    ///
    /// Two rules decide what is reported, and neither is a minimality theorem —
    /// the set is small in the shapes the tests measure, not provably smallest:
    ///
    /// - A node whose own content is intact ([`Content::ChangedBelow`]) is
    ///   reported only when nothing below it was, so the child that explains it
    ///   is not joined by its container.
    /// - A node whose own content changed ([`Content::Changed`]) is reported
    ///   whatever its children did. Suppressing it would leave a real change with
    ///   no site.
    ///
    /// Each kind is reported at its own root, so no two divergences of the same
    /// kind nest. Across kinds they can: the walk descends under an inserted
    /// region, because a new expression can wrap content that survived, so a
    /// `Changed` may sit inside an `Inserted` or a `Deleted`. A consumer placing
    /// a guard per divergence gets nested guards there.
    pub fn divergences(&self) -> Vec<Divergence<'a>> {
        let by_dst: HashMap<*const TypedExpr, &Match<'a>> = self
            .matched
            .iter()
            .map(|m| (m.dst as *const TypedExpr, m))
            .collect();

        let gone: HashSet<*const TypedExpr> = self
            .deleted
            .iter()
            .map(|e| *e as *const TypedExpr)
            .collect();
        let mut roots: Vec<(&TypedExpr, bool)> = Vec::new();
        collect_deleted_roots(self.src_root, &gone, &mut roots);
        // Deletions are found on the src side but suppress a site on the dst
        // side: a node that lost a child has changed content, and the `Deleted`
        // below it is the whole explanation. Map each deleted root's src parent
        // to its dst counterpart so the walk can see that.
        let deleted_roots: HashSet<*const TypedExpr> =
            roots.iter().map(|(e, _)| *e as *const TypedExpr).collect();
        let lost_a_child = self.parents_of(&deleted_roots);

        let mut out = Vec::new();
        /// Returns whether anything in this subtree — this node included — was
        /// reported.
        fn walk<'a>(
            e: &'a TypedExpr,
            parent_matched: bool,
            by_dst: &HashMap<*const TypedExpr, &Match<'a>>,
            lost_a_child: &HashSet<*const TypedExpr>,
            out: &mut Vec<Divergence<'a>>,
        ) -> bool {
            let Some(m) = by_dst.get(&(e as *const TypedExpr)) else {
                // Target-only. It is the *root* of an inserted region exactly
                // when the node above it is not also new. Keep descending
                // regardless: a matched node can sit inside a new region — the
                // new expression wrapping content that survived — and whatever
                // diverges under it still has to be reported.
                let mut reported = parent_matched;
                if parent_matched {
                    out.push(Divergence::Inserted(e));
                }
                for c in child_exprs(e) {
                    reported |= walk(c, false, by_dst, lost_a_child, out);
                }
                return reported;
            };
            let mut reported_below = lost_a_child.contains(&(e as *const TypedExpr));
            for c in child_exprs(e) {
                reported_below |= walk(c, true, by_dst, lost_a_child, out);
            }
            // The node's own content changed: that is a site regardless of what
            // its children did — a renamed binder over an edited body has two
            // things to say. A node whose own content is intact is a site only
            // when nothing below was reported, which leaves the changes no
            // child accounts for: a reordering, or a type resolved from outside.
            if m.content == Content::Changed
                || (m.content == Content::ChangedBelow && !reported_below)
            {
                out.push(Divergence::Changed(**m));
                return true;
            }
            reported_below
        }
        walk(self.dst_root, true, &by_dst, &lost_a_child, &mut out);

        out.extend(roots.into_iter().map(|(e, _)| Divergence::Deleted(e)));
        out
    }

    /// The dst counterparts of the src nodes that directly contain one of
    /// `children`. Used to carry a src-side finding (a deletion) over to the
    /// dst-side walk that decides sites.
    fn parents_of(&self, children: &HashSet<*const TypedExpr>) -> HashSet<*const TypedExpr> {
        let by_src: HashMap<*const TypedExpr, *const TypedExpr> = self
            .matched
            .iter()
            .map(|m| (m.src as *const TypedExpr, m.dst as *const TypedExpr))
            .collect();
        let mut out = HashSet::new();
        fn walk(
            e: &TypedExpr,
            children: &HashSet<*const TypedExpr>,
            by_src: &HashMap<*const TypedExpr, *const TypedExpr>,
            out: &mut HashSet<*const TypedExpr>,
        ) {
            let kids = child_exprs(e);
            if kids
                .iter()
                .any(|c| children.contains(&(*c as *const TypedExpr)))
                && let Some(dst) = by_src.get(&(e as *const TypedExpr))
            {
                out.insert(*dst);
            }
            for c in kids {
                walk(c, children, by_src, out);
            }
        }
        walk(self.src_root, children, &by_src, &mut out);
        out
    }

    /// The largest subtrees the two programs have in common: every node whose
    /// content is unchanged and whose parent's is not, in new-program order.
    ///
    /// These are the units of reuse — a `Same` node's whole subtree is `Same`,
    /// so reporting the descendants as well would say nothing more.
    ///
    /// Reuse here means *the term is the same term*, which is what a unified
    /// tree needs. It does **not** mean the term evaluates to the same value in
    /// both versions: `let x = 1 in x` and `let x = 2 in x` share the body `x`,
    /// and that is right — the two `let`s are a divergence, and it is the
    /// binding that differs, not the read.
    pub fn shared_roots(&self) -> Vec<&Match<'a>> {
        let by_dst: HashMap<*const TypedExpr, &Match<'a>> = self
            .matched
            .iter()
            .map(|m| (m.dst as *const TypedExpr, m))
            .collect();
        let mut out = Vec::new();
        fn walk<'a, 'm>(
            e: &TypedExpr,
            by_dst: &HashMap<*const TypedExpr, &'m Match<'a>>,
            out: &mut Vec<&'m Match<'a>>,
        ) {
            if let Some(m) = by_dst.get(&(e as *const TypedExpr))
                && m.content == Content::Same
            {
                out.push(m);
                return;
            }
            for c in child_exprs(e) {
                walk(c, by_dst, out);
            }
        }
        walk(self.dst_root, &by_dst, &mut out);
        out
    }
}

/// One place the two programs disagree, at the granularity a version guard is
/// placed. Each kind is reported at its own root, so no two divergences of the
/// same kind nest; across kinds a [`Changed`] can sit inside an [`Inserted`] or
/// a [`Deleted`], because a new expression can wrap content that survived.
///
/// [`Changed`]: Divergence::Changed
/// [`Inserted`]: Divergence::Inserted
/// [`Deleted`]: Divergence::Deleted
#[derive(Debug, Clone, Copy)]
pub enum Divergence<'a> {
    /// Both programs have a node here and this node is the one that changed:
    /// either its own content differs ([`Content::Changed`]) or its subtree
    /// differs with nothing under it reported ([`Content::ChangedBelow`]).
    Changed(Match<'a>),
    /// A subtree the new program has and the old one does not, at its root.
    Inserted(&'a TypedExpr),
    /// A subtree the old program had and the new one does not, at its root.
    Deleted(&'a TypedExpr),
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
/// correspond by construction — neither has anywhere else to go. [`bottom_up`]
/// cannot reach that on its own because it is seeded by already-matched
/// descendants and gives up when a node has none, which is exactly the case
/// where two roots correspond but nothing *inside* them does: `Some(1)` against
/// `Some(2)` would otherwise be a wholesale rebuild rather than an edited
/// payload. Anchoring also hands step 4 a pair to align the interiors within.
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

/// Compile two source programs to `phase` and diff them — the end-to-end entry
/// point from source. The classified [`Diff`] borrows the two compiled trees,
/// which live only for the duration of this call, so the result is delivered to
/// `f`; return out of it whatever you need to keep (e.g. counts, cloned nodes).
///
/// ```ignore
/// let (shared, new) = diff_programs(v1_src, v2_src, Phase::Infer,
///     |d| (d.shared().count(), d.new.len()))?;
/// ```
pub fn diff_programs<R>(
    src: &str,
    dst: &str,
    phase: Phase,
    f: impl FnOnce(&Diff) -> R,
) -> Result<R, Vec<CompileError>> {
    let a = compile_to(src, phase)?;
    let b = compile_to(dst, phase)?;
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
    /// (`Record`, `DisjointJoin`) — the content hash folds them
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
    matches!(e.node, N::Record(_) | N::DisjointJoin(_))
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
        N::Cast { value, target } => {
            let mut children = vec![&**value];
            children.extend(cast_target_predicates(target));
            children
        }
        N::BinOp { left, right, .. } => vec![left, right],
        N::UnaryOp(_, inner) => vec![inner],
        N::Lambda { body, .. } => vec![body],
        N::Aggregate { input, .. } => vec![input],
        N::Let {
            bound_expr, body, ..
        } => vec![bound_expr, body],
        N::List(xs) | N::Tuple(xs) | N::Compose(xs) | N::Copair(xs) | N::DisjointJoin(xs) => {
            xs.iter().collect()
        }
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
        N::MutDecl { init, body, .. } => vec![init, body],
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
/// order-insensitive nodes (`Record`, `DisjointJoin`), whose children may be
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
// Phase 3: bottom-up container recovery
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

// ---------------------------------------------------------------------------
// Phase 4: optimal recovery inside a paired container
// ---------------------------------------------------------------------------

/// Optimally align the still-unmatched interiors of a freshly paired
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
    for (x, y) in ted::mapping(s, u, d, w, m) {
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

    /// Relabelling cost.
    ///
    /// Free when the two nodes are the same computation, or when the earlier
    /// phases already paired them. **Prohibitive** when either node is already
    /// paired with somebody else: the edit distance is otherwise free to invent
    /// an alignment that contradicts an anchor, and since only its *unmatched*
    /// pairs are adopted, the contradiction survives as a silently wrong match
    /// — a `let` in a spine mapped to its own inner `let`, say, because the
    /// distance was happy to shift the whole chain by one. Three exceeds the
    /// cost of deleting and inserting instead (two), so a conflicting pair is
    /// never on an optimal script.
    fn relabel(a: &Indexed, ga: usize, b: &Indexed, gb: usize, m: &super::Matching) -> u32 {
        match (m.src_to_dst[ga], m.dst_to_src[gb]) {
            (Some(y), _) if y == gb => 0,
            (None, None) => u32::from(a.nodes[ga].hash != b.nodes[gb].hash),
            _ => 3,
        }
    }

    /// Fill the forest-distance table for keyroot pair `(ki, kj)`, writing any
    /// whole-subtree distances it settles into `tree`.
    #[allow(clippy::too_many_arguments)]
    fn forest_dist(
        s: &Indexed,
        ps: &Post,
        d: &Indexed,
        pd: &Post,
        ki: usize,
        kj: usize,
        m: &super::Matching,
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
                    let ren = f.get(i - 1, j - 1) + relabel(s, ps.global[pi], d, pd.global[pj], m);
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
    pub(super) fn mapping(
        s: &Indexed,
        su: usize,
        d: &Indexed,
        dw: usize,
        m: &super::Matching,
    ) -> Vec<(usize, usize)> {
        let ps = Post::build(s, su);
        let pd = Post::build(d, dw);
        let mut tree = vec![0u32; ps.n() * pd.n()];
        for &ki in &ps.keyroots {
            for &kj in &pd.keyroots {
                forest_dist(s, &ps, d, &pd, ki, kj, m, &mut tree);
            }
        }

        // Trace an optimal script back through the same recurrence. Each entry
        // of `todo` is a keyroot pair whose forest table has to be re-derived;
        // re-deriving costs one table each and there are `O(n + m)` of them,
        // which is cheaper than retaining every table from the fill above.
        let mut out = Vec::new();
        let mut todo = vec![(ps.n(), pd.n())];
        while let Some((ki, kj)) = todo.pop() {
            let f = forest_dist(s, &ps, d, &pd, ki, kj, m, &mut tree);
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

/// The [`resolved_hash`] of every node of `t`, indexed the same way `t` is.
///
/// Distinguishes the `j`th binder a node introduces from its siblings, without
/// letting two nodes' correspondents collide: the multiplier is the 64-bit
/// golden-ratio constant, so a one-bit change in either input spreads across the
/// result.
fn mix(correspondent: u64, j: u64) -> u64 {
    correspondent.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ j
}

/// A node's two scope-resolved hashes: the whole subtree's, and the node's own.
/// Comparing both is what separates "this node changed" from "something under it
/// changed" — see [`Content`].
#[derive(Debug, Clone, Copy, Default)]
struct NodeHashes {
    resolved: u64,
    own: u64,
}

/// Walks top-down carrying the binders each node sits under, each tagged with
/// the correspondent `correspondent_of` gives its owner, so a free variable
/// inside a subterm
/// hashes to *which binder it resolves to* rather than to how that binder
/// happens to be spelled.
///
/// The binders a node puts over each of its children come from
/// [`for_each_scoped_item`], the crate's single statement of CCL's binding
/// structure — this walk does not restate them. It is keyed by child pointer
/// because the differ descends into one child the scope walk does not: a cast
/// target's refinement predicate, which is a type slot. That predicate sits in
/// its cast's own scope, so an absent entry meaning "no binders" is exactly
/// right for it.
fn resolved_hashes(t: &Indexed<'_>, correspondent_of: &dyn Fn(usize) -> u64) -> Vec<NodeHashes> {
    fn go<'a>(
        t: &Indexed<'a>,
        i: usize,
        scope: &mut Vec<(&'a Name, u64)>,
        correspondent_of: &dyn Fn(usize) -> u64,
        out: &mut [NodeHashes],
    ) {
        out[i] = NodeHashes {
            resolved: resolved_hash(t.nodes[i].expr, scope).0,
            own: own_hash(t.nodes[i].expr, scope).0,
        };

        let mut introduced: HashMap<*const TypedExpr, Vec<&'a Name>> = HashMap::new();
        for_each_scoped_item(t.nodes[i].expr, &mut |item| {
            if let ScopedItem::Child { expr, binders } = item
                && !binders.is_empty()
            {
                introduced.insert(
                    expr as *const TypedExpr,
                    binders.iter().map(|b| &b.name).collect(),
                );
            }
        });

        let correspondent = correspondent_of(i);
        for &c in &t.nodes[i].children {
            let added = introduced
                .get(&(t.nodes[c].expr as *const TypedExpr))
                .map_or(0, |names| {
                    // Each binder a node introduces needs its own
                    // correspondent: they are distinct binders, and one token
                    // for the whole node would make `letrec p = …; q = … in p`
                    // and `… in q` hash
                    // equal — a `Content::Same` on two different computations,
                    // which is the unsound direction (`src/ccl/design/diffing.md`,
                    // "Direction of error"). Position within the group is the
                    // correspondence, matching how `child_exprs` pairs the
                    // group's definitions.
                    for (j, n) in names.iter().enumerate() {
                        scope.push((n, mix(correspondent, j as u64)));
                    }
                    names.len()
                });
            go(t, c, scope, correspondent_of, out);
            scope.truncate(scope.len() - added);
        }
    }

    let mut out = vec![NodeHashes::default(); t.len()];
    go(t, 0, &mut Vec::new(), correspondent_of, &mut out);
    out
}

fn classify<'a>(s: &Indexed<'a>, d: &Indexed<'a>, m: &Matching) -> Diff<'a> {
    let in_place = align_children(s, d, m);
    // A binder's *correspondent*: the binder it corresponds to in the other
    // program, as a token both sides share. A src binder's is the dst node it
    // matched; an unmatched one gets a token out of dst's index range, so it
    // corresponds to nothing and can never look like a match.
    let src_correspondent = |u: usize| m.src_to_dst[u].unwrap_or(d.len() + u) as u64;
    let dst_correspondent = |w: usize| w as u64;
    let src_resolved = resolved_hashes(s, &src_correspondent);
    let dst_resolved = resolved_hashes(d, &dst_correspondent);
    let mut out = Diff {
        matched: Vec::new(),
        deleted: Vec::new(),
        new: Vec::new(),
        src_root: s.nodes[0].expr,
        dst_root: d.nodes[0].expr,
    };
    for (u, &dst) in m.src_to_dst.iter().enumerate() {
        match dst {
            Some(w) => out.matched.push(Match {
                src: s.nodes[u].expr,
                dst: d.nodes[w].expr,
                content: {
                    // `own_hash` folds a subset of what `resolved_hash` does,
                    // plus a record's labels — which `resolved_hash` folds
                    // paired with the children they label. So an equal subtree
                    // hash implies an equal own hash, and the `Same` arm below
                    // is safe to take on the subtree hash alone. Were that to
                    // stop holding, a node whose own content changed would
                    // classify `Same`: an unsound share, the direction
                    // `src/ccl/design/diffing.md`, "Direction of error" rules
                    // out.
                    debug_assert!(
                        src_resolved[u].resolved != dst_resolved[w].resolved
                            || src_resolved[u].own == dst_resolved[w].own,
                        "own_hash must refine resolved_hash: equal subtrees, differing own content",
                    );
                    if src_resolved[u].resolved == dst_resolved[w].resolved {
                        Content::Same
                    } else if src_resolved[u].own == dst_resolved[w].own {
                        Content::ChangedBelow
                    } else {
                        Content::Changed
                    }
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

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// How wide a single node's term rendering may get before it is elided.
const RENDER_WIDTH: usize = 68;

/// One node's own line in a rendered diff: the head of its symbolic form.
///
/// A node is shown by rendering its whole subterm with
/// [`symbolic`](crate::ccl::symbolic::symbolic) and keeping the first line, cut
/// to [`RENDER_WIDTH`]. That reads naturally — a leaf prints exactly, an
/// interior node prints its head (`let a = 1 in …`) — and it costs nothing to
/// keep in step with the AST, which a second shallow-label vocabulary would
/// not. The price is `O(n²)` text for the whole tree; this is a debugging and
/// inspection surface, not a hot path.
fn head(e: &TypedExpr) -> String {
    let full = crate::ccl::symbolic::symbolic(e);
    let line = full.lines().next().unwrap_or("").trim_end();
    let mut out: String = line.chars().take(RENDER_WIDTH).collect();
    if line.chars().count() > RENDER_WIDTH || full.lines().nth(1).is_some() {
        out.push('…');
    }
    out
}

/// Renders as an annotated tree of the **new** program, plus whatever the old
/// program had that the new one dropped.
///
/// Every node of the new program is marked with what the diff concluded about
/// it. An inserted or deleted subtree is shown by its **root** only, with its
/// node count — printing every node of a pasted-in block is noise, and the root
/// is the actionable unit.
///
/// ```text
/// 15 shared · 3 changed · 1 moved · 0 deleted · 4 new
///
/// ~ let a = 1 in let b = sum(…) in a + b…
///   = 1
///   + let b = sum([i ▷ (λ i → i * 2) for …    (+13 nodes)
///   ~ a + b
///     = a
/// ```
///
/// Markers: `=` unchanged, `~` content changed, `+` new, `-` deleted, and a
/// trailing `»` on a node whose placement changed.
impl std::fmt::Display for Diff<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let by_dst: HashMap<*const TypedExpr, &Match> = self
            .matched
            .iter()
            .map(|m| (m.dst as *const TypedExpr, m))
            .collect();
        let inserted: HashSet<*const TypedExpr> =
            self.new.iter().map(|e| *e as *const TypedExpr).collect();

        writeln!(
            f,
            "{} shared · {} changed · {} moved · {} deleted · {} new",
            self.shared().count(),
            self.updated().count(),
            self.moved().count(),
            self.deleted.len(),
            self.new.len(),
        )?;
        writeln!(f)?;

        render_node(f, self.dst_root, 0, &by_dst, &inserted)?;

        // Anything the old program had that the new one does not.
        let gone: HashSet<*const TypedExpr> = self
            .deleted
            .iter()
            .map(|e| *e as *const TypedExpr)
            .collect();
        let mut roots: Vec<(&TypedExpr, bool)> = Vec::new();
        collect_deleted_roots(self.src_root, &gone, &mut roots);
        if !roots.is_empty() {
            writeln!(f)?;
            for (e, whole) in roots {
                let note = if whole { size_note(e) } else { String::new() };
                writeln!(f, "- {}{note}", head(e))?;
            }
        }
        Ok(())
    }
}

/// Is every node of `e`'s subtree in `set`?
///
/// This is what decides whether a wholly-inserted or wholly-deleted region may
/// collapse to its root in the rendering. A node in `set` whose *interior* is
/// still matched is a different thing entirely — a wrapper that appeared or
/// vanished around content that survived — and collapsing it would claim its
/// surviving children changed too.
///
/// Walks [`child_exprs`], not `all_children`, because that is the child set the
/// differ indexed: a cast target's refinement predicate is a node the matcher
/// can match and `all_children` does not reach. Testing the narrower set would
/// call a cast wholly-gone while a matched node still lives in its predicate.
fn subtree_entirely_in(e: &TypedExpr, set: &HashSet<*const TypedExpr>) -> bool {
    set.contains(&(e as *const TypedExpr))
        && child_exprs(e)
            .into_iter()
            .all(|c| subtree_entirely_in(c, set))
}

/// `    (+N nodes)` when `e` has descendants, so an elided subtree still
/// reports how much it stands for; empty for a leaf. Counts over
/// [`child_exprs`], the differ's child set, so the note matches what collapsed.
fn size_note(e: &TypedExpr) -> String {
    let mut n = 0;
    fn count(e: &TypedExpr, n: &mut usize) {
        *n += 1;
        for c in child_exprs(e) {
            count(c, n);
        }
    }
    for c in child_exprs(e) {
        count(c, &mut n);
    }
    if n == 0 {
        String::new()
    } else {
        format!("    (+{n} nodes)")
    }
}

fn render_node(
    f: &mut std::fmt::Formatter<'_>,
    e: &TypedExpr,
    depth: usize,
    by_dst: &HashMap<*const TypedExpr, &Match>,
    inserted: &HashSet<*const TypedExpr>,
) -> std::fmt::Result {
    let indent = "  ".repeat(depth);
    match by_dst.get(&(e as *const TypedExpr)) {
        // Target-only. A wholly-new region collapses to its root; a new node
        // wrapping content that survived is shown with that content under it.
        None if subtree_entirely_in(e, inserted) => {
            writeln!(f, "{indent}+ {}{}", head(e), size_note(e))
        }
        None => {
            writeln!(f, "{indent}+ {}", head(e))?;
            for c in child_exprs(e) {
                render_node(f, c, depth + 1, by_dst, inserted)?;
            }
            Ok(())
        }
        Some(m) => {
            let mark = match m.content {
                Content::Same => '=',
                Content::ChangedBelow | Content::Changed => '~',
            };
            let moved = if m.placement == Placement::Moved {
                " »"
            } else {
                ""
            };
            writeln!(f, "{indent}{mark} {}{moved}", head(e))?;
            // An unchanged subtree is unchanged all the way down; descending
            // would print it verbatim for no information.
            if m.content != Content::Same {
                for c in child_exprs(e) {
                    render_node(f, c, depth + 1, by_dst, inserted)?;
                }
            }
            Ok(())
        }
    }
}

/// Collect the topmost deleted nodes of `root`, each flagged with whether its
/// whole subtree went with it. A wholly-deleted region is reported once, at its
/// root; a deleted node whose children survived is reported alone, and the walk
/// continues through it to find whatever else was dropped further down.
fn collect_deleted_roots<'a>(
    e: &'a TypedExpr,
    gone: &HashSet<*const TypedExpr>,
    out: &mut Vec<(&'a TypedExpr, bool)>,
) {
    if gone.contains(&(e as *const TypedExpr)) {
        let whole = subtree_entirely_in(e, gone);
        out.push((e, whole));
        if whole {
            return;
        }
    }
    for c in child_exprs(e) {
        collect_deleted_roots(c, gone, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::content_hash::content_hash;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::{
        ArithmeticKind, BaseType, BinOpKind, CompareKind, FunKind, Lit, Name, Refinement,
        RefinementSet, Type, TypedBinding, TypedExpr, TypedExprNode,
    };
    use indoc::indoc;
    use std::rc::Rc;

    use TypedExprNode as N;

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
        // The two tuples correspond but differ → an update.
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
        let rec = |fields: Vec<(&str, TypedExpr)>| {
            TypedExpr::new(TypedExprNode::Record(
                fields
                    .into_iter()
                    .map(|(n, e)| (n.to_string(), e))
                    .collect(),
            ))
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
        let guard =
            |n: i64| TypedExpr::binop(var("v"), BinOpKind::Compare(CompareKind::Greater), int(n));
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
        compile_to(code, Phase::Lower).expect("compile to lowered phase should succeed")
    }

    /// Post-inference CCL (uniquified, fully typed), via the public API.
    fn lower_and_infer(code: &str) -> TypedExpr {
        compile_to(code, Phase::Infer).expect("compile to inferred phase should succeed")
    }

    // Realistic CHL programs exercising records, list comprehensions, filters,
    // aggregates, projections, joins, def/yield generators, groupby, induction
    // accumulators, and transactional registers. Between them they cover every
    // node kind that reaches these two phases: `Defer`/`Feed` (generators),
    // `Case` (guards), `Cast` (comprehension filters), `For`/`MutWrite`
    // (accumulators), and `Begin` (transaction blocks). `LetRec` and `Transact`
    // are born *below* the inferred phase — the mutability phases build them —
    // so no source program can exercise them here; `content_hash` covers them
    // structurally instead.
    const FILTER_AGG: &str = indoc! {r#"
        users = [
          (name="alice", age=30, score=85),
          (name="bob", age=17, score=92),
        ]
        sum([u.score for u in users if u.age >= 18])
    "#};
    const FILTER_AGG_21: &str = indoc! {r#"
        users = [
          (name="alice", age=30, score=85),
          (name="bob", age=17, score=92),
        ]
        sum([u.score for u in users if u.age >= 21])
    "#};
    const GENERATORS: &str = indoc! {"
        def positives(xs):
            for x in xs:
                if x > 0:
                    yield x

        def squared(xs):
            for x in xs:
                yield x * x

        max(squared(positives([-3, 4, -1, 2, 5, -7])))
    "};
    const JOIN: &str = indoc! {r#"
        users = [(id=1, name="alice"), (id=2, name="bob")]
        orders = [(user_id=1, amount=50), (user_id=2, amount=75)]
        [(customer=u.name, total=o.amount) for u in users for o in orders if u.id == o.user_id]
    "#};
    const GROUPBY: &str = indoc! {r#"
        sales = [(region="west", amount=100), (region="east", amount=50)]
        [sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)]
    "#};
    const ACCUM: &str = indoc! {"
        acc := 0
        for i in [1, 2, 3, 4, 5]:
            acc := acc + i
        acc
    "};
    const TXN: &str = indoc! {"
        pool: Mut(Int, Txn) := 100
        reqs = [1, 2, 3]
        for r in reqs:
            with begin():
                pool := pool - r
    "};

    #[test]
    fn lowered_source_is_stable_across_independent_compilations() {
        // The point of diffing pre-uniquify on Raw names: lowering the same
        // source twice, through independent contexts, yields trees that diff as
        // identical — no spurious divergence from fresh binder identities.
        let src = indoc! {"
            x = 1
            y = x + 2
            y
        "};
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
        let v1 = lower(indoc! {"
            x = 1
            y = x + 2
            y
        "});
        let v2 = lower(indoc! {"
            x = 1
            y = x + 3
            y
        "});
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
        let v1 = lower(indoc! {"
            a = 1
            a
        "});
        let v2 = lower(indoc! {"
            a = 1
            b = sum([i * 2 for i in [1,2,3]])
            a + b
        "});
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
        let v1 = lower(indoc! {"
            def f(x):
                a = 1
                a + x
            f(2)
        "});
        let v2 = lower(indoc! {"
            def f(x):
                a = 1
                b = sum([i * 2 for i in [1,2,3]])
                a + x + b
            f(2)
        "});
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

    #[test]
    fn render_collapses_whole_regions_but_not_wrappers() {
        // `a = 1; a` gains a statement that both introduces new structure and
        // reuses `a`. The wholly-new `sum(…)` subtree collapses to one line
        // with a node count; the new `a + b` does *not*, because `a` survived
        // underneath it and hiding that would claim it changed.
        let v1 = lower(indoc! {"
            a = 1
            a
        "});
        let v2 = lower(indoc! {"
            a = 1
            b = sum([i * 2 for i in [1,2,3]])
            a + b
        "});
        let out = diff(&v1, &v2).to_string();

        assert!(
            out.starts_with("2 shared · 1 changed"),
            "summary line: {out}"
        );
        assert!(
            out.contains("(+"),
            "a wholly-new subtree collapses with a node count:\n{out}"
        );
        // The surviving `a` is still shown, under the new node that wraps it.
        assert!(
            out.lines().any(|l| l.trim_start().starts_with("= a")),
            "the reused `a` is rendered as shared:\n{out}"
        );
        // Every line after the summary carries exactly one marker.
        for l in out.lines().skip(2).filter(|l| !l.trim().is_empty()) {
            let m = l.trim_start().chars().next().unwrap();
            assert!("=~+-".contains(m), "unmarked line {l:?} in:\n{out}");
        }
    }

    #[test]
    fn render_does_not_overstate_a_deletion() {
        // `let c = 9 in …` is dropped, but the statements under it survive. The
        // deleted wrapper must be reported on its own — not as a subtree of
        // everything it used to contain.
        let v1 = lower(indoc! {"
            a = 1
            c = 9
            b = 2
            a + b + c
        "});
        let v2 = lower(indoc! {"
            a = 1
            b = 2
            a + b
        "});
        let d = diff(&v1, &v2);
        let out = d.to_string();

        let deleted_lines: Vec<&str> = out.lines().filter(|l| l.starts_with("- ")).collect();
        assert_eq!(
            deleted_lines.len(),
            d.deleted.len(),
            "one line per deleted node when none of them collapse:\n{out}"
        );
        assert!(
            deleted_lines.iter().all(|l| !l.contains("(+")),
            "no deleted node claims a subtree it did not take with it:\n{out}"
        );
    }

    #[test]
    fn renaming_a_binding_is_not_a_change() {
        // Renaming is a denotational no-op, and the two roots hash equal, so
        // the diff has to agree all the way down. It only does because
        // classification resolves a free variable to *which binder it means*
        // rather than to how that binder is spelled.
        for (a, b) in [
            (
                indoc! {"
                    x = 1
                    y = x + 2
                    y
                "},
                indoc! {"
                    q = 1
                    y = q + 2
                    y
                "},
            ),
            (
                indoc! {r#"
                    users = [(name="a", age=30)]
                    sum([u.age for u in users])
                "#},
                indoc! {r#"
                    users = [(name="a", age=30)]
                    sum([q.age for q in users])
                "#},
            ),
        ] {
            let (v1, v2) = (lower(a), lower(b));
            assert!(
                diff(&v1, &v2).is_identical(),
                "a pure rename must diff as identical:\n{a}\n{}",
                diff(&v1, &v2)
            );
        }
    }

    #[test]
    fn a_binder_inserted_above_a_subterm_does_not_change_it() {
        // The trap the binder-correspondent scheme exists to avoid. `b`'s binding and
        // the tail below it still reach `a` through one more enclosing `let`
        // than before; if a free variable were identified by its distance to
        // its binder rather than by the binder itself, every reference reaching
        // past the new one would shift and the whole tail would read as
        // changed.
        let v1 = lower(indoc! {"
            a = 1
            b = 2
            a + b
        "});
        let v2 = lower(indoc! {"
            a = 1
            c = 9
            b = 2
            a + b
        "});
        let r = diff(&v1, &v2);
        assert!(r.deleted.is_empty(), "{r}");
        assert!(
            r.shared()
                .any(|m| matches!(m.src.node, TypedExprNode::BinOp { .. })),
            "the untouched `a + b` tail is still shared:\n{r}",
        );
    }

    // -----------------------------------------------------------------------
    // The divergence frontier
    // -----------------------------------------------------------------------

    /// A 40-binding `let` spine whose final expression uses a different
    /// literal — one edit, as deep in the tree as this corpus goes.
    fn deep_spine(tweak: bool) -> String {
        let mut s = String::from("a0 = 1\n");
        for i in 1..40 {
            s.push_str(&format!("a{i} = a{} + {i}\n", i - 1));
        }
        s.push_str(&format!("a39 + {}\n", if tweak { 99 } else { 1 }));
        s
    }

    #[test]
    fn one_edit_is_one_divergence() {
        // Every ancestor of an edit has changed content, so `matched` reports
        // 42 changed nodes here. Exactly one of them is the edit.
        let (v1, v2) = (lower(&deep_spine(false)), lower(&deep_spine(true)));
        let r = diff(&v1, &v2);
        assert!(
            r.updated().count() > 40,
            "the ancestors are all changed too"
        );

        let dv = r.divergences();
        assert_eq!(dv.len(), 1, "{dv:?}");
        let Divergence::Changed(m) = dv[0] else {
            panic!("expected a content change, got {:?}", dv[0])
        };
        assert!(matches!(m.src.node, TypedExprNode::Lit(Lit::Int(1))));
        assert!(matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(99))));
    }

    #[test]
    fn an_inserted_region_is_reported_at_its_root() {
        // 16 new nodes, one insertion.
        let v1 = lower(indoc! {"
            a = 1
            a
        "});
        let v2 = lower(indoc! {"
            a = 1
            b = sum([i * 2 for i in [1,2,3]])
            a + b
        "});
        let r = diff(&v1, &v2);
        assert!(r.new.len() > 10, "the inserted block is substantial");

        let inserted: Vec<_> = r
            .divergences()
            .into_iter()
            .filter(|d| matches!(d, Divergence::Inserted(_)))
            .collect();
        assert_eq!(inserted.len(), 1, "{inserted:?}");
        let Divergence::Inserted(e) = inserted[0] else {
            unreachable!()
        };
        assert!(matches!(e.node, TypedExprNode::Let { .. }));
    }

    #[test]
    fn identical_programs_have_no_divergences() {
        let (v1, v2) = (lower(&deep_spine(false)), lower(&deep_spine(false)));
        let r = diff(&v1, &v2);
        assert!(r.divergences().is_empty());
        // ...and reuse is the whole program, in one piece.
        let roots = r.shared_roots();
        assert_eq!(roots.len(), 1);
        assert!(std::ptr::eq(roots[0].dst, &v2));
    }

    #[test]
    fn shared_roots_are_maximal_and_disjoint() {
        let v1 = lower(indoc! {"
            a = 1
            b = 2
            a + b
        "});
        let v2 = lower(indoc! {"
            a = 1
            c = 9
            b = 2
            a + b
        "});
        let r = diff(&v1, &v2);
        let roots = r.shared_roots();
        assert!(!roots.is_empty());

        // No shared root sits inside another: each is the top of its region.
        let tops: Vec<*const TypedExpr> = roots.iter().map(|m| m.dst as *const _).collect();
        for m in &roots {
            let mut inner = 0;
            m.dst.walk_children(|c| {
                fn any(e: &TypedExpr, tops: &[*const TypedExpr], n: &mut usize) {
                    if tops.contains(&(e as *const TypedExpr)) {
                        *n += 1;
                    }
                    e.walk_children(|c| any(c, tops, n));
                }
                any(c, &tops, &mut inner);
            });
            assert_eq!(inner, 0, "a shared root contains another: {}", head(m.dst));
        }
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
            indoc! {"
                acc := 0
                for i in [1, 2, 3, 4, 5]:
                    acc := acc + i * 2
                acc
            "},
        );
    }

    #[test]
    fn transactional_register_is_stable_and_localizes() {
        // A `Mut(Int, Txn)` register written under `with begin():` lowers to a
        // `Begin` block wrapping the `MutWrite`. Same story: stable across
        // compilations, and an edit inside the block localizes to it.
        assert_stable_and_localizing(
            TXN,
            indoc! {"
                pool: Mut(Int, Txn) := 100
                reqs = [1, 2, 3]
                for r in reqs:
                    with begin():
                        pool := pool - r - 1
            "},
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
        let base = indoc! {"
            v = 5
            1 if v > 0 else 2
        "};
        let (a, b) = (lower(base), lower(base));
        assert!(diff(&a, &b).is_identical());

        // Editing the else-branch value localizes to that literal.
        let (e1, e2) = (
            lower(base),
            lower(indoc! {"
                v = 5
                1 if v > 0 else 3
            "}),
        );
        let r = diff(&e1, &e2);
        assert!(r.updated().any(|m| {
            matches!(m.src.node, TypedExprNode::Lit(Lit::Int(2)))
                && matches!(m.dst.node, TypedExprNode::Lit(Lit::Int(3)))
        }));

        // Editing the guard threshold localizes to that literal.
        let (g1, g2) = (
            lower(base),
            lower(indoc! {"
                v = 5
                1 if v > 1 else 2
            "}),
        );
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
        let prog_int = indoc! {"
            x = 1
            (x, x)
        "};
        let prog_str = indoc! {r#"
            x = "a"
            (x, x)
        "#};

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
    fn inlining_erases_function_boundaries() {
        // Extracting a subexpression into a `def` is invisible once the
        // pipeline's own inlining has run: the two versions are the same tree.
        let plain = indoc! {"
            a = 1
            (a + 2) * 3
        "};
        let extracted = indoc! {"
            def g(y):
                y + 2
            a = 1
            g(a) * 3
        "};

        let (v1, v2) = (
            compile_to(plain, Phase::Infer).unwrap(),
            compile_to(extracted, Phase::Infer).unwrap(),
        );
        assert!(
            !diff(&v1, &v2).divergences().is_empty(),
            "the function boundary is still part of the program here",
        );

        let (v1, v2) = (
            compile_to(plain, Phase::Inline).unwrap(),
            compile_to(extracted, Phase::Inline).unwrap(),
        );
        assert!(
            diff(&v1, &v2).is_identical(),
            "inlined, the two are the same program:\n{}",
            diff(&v1, &v2)
        );
    }

    #[test]
    fn inlining_costs_locality_in_a_shared_helper() {
        // The other side of that trade, stated as a test so it cannot be
        // mistaken for a strict improvement: a body called twice is inlined
        // twice, so one edit inside it diverges at both call sites.
        //
        // The two calls pass *different* arguments that nonetheless share one
        // specialization: monomorphization keys on instantiation identity, and
        // a join of two singletons keeps neither refinement, so `a` and `b`
        // both arrive as plain `Int`. Literal arguments would key apart and
        // clone the helper during inference — the baseline would already be
        // delocalized, and the contrast below would not be inlining's doing.
        // See `src/ccl/design/diffing.md`, "How much to normalize".
        let v1 = indoc! {"
            def g(y):
                y + 2
            a = 1 + 1
            b = 2 + 2
            g(a) * g(b)
        "};
        let v2 = indoc! {"
            def g(y):
                y + 5
            a = 1 + 1
            b = 2 + 2
            g(a) * g(b)
        "};

        let (a, b) = (
            compile_to(v1, Phase::Infer).unwrap(),
            compile_to(v2, Phase::Infer).unwrap(),
        );
        assert_eq!(
            diff(&a, &b).divergences().len(),
            1,
            "one edit, one divergence, while the two calls still share one function",
        );

        let (a, b) = (
            compile_to(v1, Phase::Inline).unwrap(),
            compile_to(v2, Phase::Inline).unwrap(),
        );
        assert!(
            diff(&a, &b).divergences().len() > 1,
            "inlined, the same edit lands once per call site",
        );
    }

    #[test]
    fn every_phase_diffs_identical_source_as_identical() {
        // The property the whole analysis rests on, over the shapes the corpus
        // reaches: compiling one source twice — independent contexts, fresh
        // binder uids — must produce trees the differ cannot tell apart. A
        // failure means some pass has let a run-varying identity leak into the
        // hash, which would make every real diff untrustworthy.
        //
        // It covers every phase because that is exactly how the leak was found:
        // `Transact` labelled its mutable variable record with
        // `Name::field_key()`, which folded the binder uid into a `String`, and
        // once a name is a record label no amount of uid-robustness in the
        // hasher can see through it.
        let corpus = [
            (
                "pure",
                indoc! {"
                    a = 1
                    b = 2
                    a + b
                "},
            ),
            ("comprehension", FILTER_AGG),
            ("generators", GENERATORS),
            ("join", JOIN),
            ("groupby", GROUPBY),
            ("accumulator", ACCUM),
            ("transaction", TXN),
            ("source", "[\"> \" + line for line in stdin()]\n"),
        ];
        for phase in [
            Phase::Lower,
            Phase::Uniquify,
            Phase::Infer,
            Phase::Inline,
            Phase::Transact,
            Phase::Letrec,
            Phase::Channelize,
            Phase::AsOfRead,
            Phase::LambdaElim,
            Phase::Planning,
        ] {
            for (label, src) in corpus {
                let (a, b) = (
                    compile_to(src, phase).expect(label),
                    compile_to(src, phase).expect(label),
                );
                assert!(
                    diff(&a, &b).is_identical(),
                    "{label} at {phase:?} is not stable across compilations:\n{}",
                    diff(&a, &b)
                );
            }
        }
    }

    #[test]
    fn a_container_that_only_gained_or_lost_a_child_is_not_a_site() {
        // The insertion (or deletion) is the whole story: the container's own
        // content — its operator, binder, annotation — did not change, so
        // reporting it alongside would put a second guard around the first.
        let (small, big) = (
            TypedExpr::list(vec![var("a")]),
            TypedExpr::list(vec![var("a"), int(7)]),
        );
        let grew = diff(&small, &big).divergences();
        assert!(
            matches!(grew.as_slice(), [Divergence::Inserted(_)]),
            "a gained child is one site: {grew:?}",
        );
        let shrank = diff(&big, &small).divergences();
        assert!(
            matches!(shrank.as_slice(), [Divergence::Deleted(_)]),
            "a lost child is one site: {shrank:?}",
        );
    }

    #[test]
    fn a_container_that_changed_and_gained_a_child_reports_both() {
        // The suppression above is about a container whose *own* content is
        // intact. A record that both relabelled a field and gained one has two
        // things to say, and both are reported.
        let rec = |fields: Vec<(&str, TypedExpr)>| {
            TypedExpr::new(N::Record(
                fields
                    .into_iter()
                    .map(|(n, e)| (n.to_string(), e))
                    .collect(),
            ))
        };
        let v1 = rec(vec![("a", var("x"))]);
        let v2 = rec(vec![("b", var("x")), ("c", int(7))]);
        let sites = diff(&v1, &v2).divergences();
        assert_eq!(sites.len(), 2, "{sites:?}");
        assert!(
            sites
                .iter()
                .any(|d| matches!(d, Divergence::Changed(m) if matches!(m.dst.node, N::Record(_)))),
            "the relabelling is a site: {sites:?}",
        );
        assert!(
            sites.iter().any(|d| matches!(d, Divergence::Inserted(_))),
            "the new field is a site: {sites:?}",
        );
    }

    #[test]
    fn a_relabelled_field_is_reported_beside_an_edited_sibling() {
        // The under-report the own-content fold exists to prevent: the edited
        // literal is a site of its own, and the record's own change — its
        // labels — must not be swallowed by it.
        let rec = |a: &str, n: i64| {
            TypedExpr::new(N::Record(vec![
                (a.to_string(), var("x")),
                ("c".to_string(), int(n)),
            ]))
        };
        let (v1, v2) = (rec("a", 1), rec("b", 2));
        let sites = diff(&v1, &v2).divergences();
        assert_eq!(sites.len(), 2, "{sites:?}");
    }

    #[test]
    fn a_reordering_is_a_site_at_the_container() {
        // Nothing below reports — every child corresponds and is unchanged —
        // so the container is where the disagreement is.
        let v1 = TypedExpr::tuple(vec![var("a"), var("b")]);
        let v2 = TypedExpr::tuple(vec![var("b"), var("a")]);
        let sites = diff(&v1, &v2).divergences();
        assert!(
            matches!(
                sites.as_slice(),
                [Divergence::Changed(m)] if matches!(m.dst.node, N::Tuple(_))
            ),
            "{sites:?}",
        );
    }

    #[test]
    fn a_deleted_cast_with_a_surviving_predicate_is_not_wholly_deleted() {
        // `child_exprs` descends into a cast target's refinement predicate — a
        // comprehension filter or join condition, a term the matcher can match.
        // The collapse tests must walk that same child set: over the narrower
        // `all_children` the cast reads as wholly gone while a matched node is
        // still live inside it, and `divergences()` then reports `Deleted` over
        // a subtree that survives in part.
        let pred = || {
            TypedExpr::binop(
                TypedExpr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                int(7),
            )
        };
        let cast = TypedExpr::new(N::Cast {
            value: Box::new(int(1)),
            target: Type::Fun {
                name: None,
                kind: FunKind::Compute,
                domain: Box::new(Type::Refinement(
                    Box::new(Type::Base(BaseType::Int)),
                    RefinementSet::one(Refinement {
                        predicate: Rc::new(pred()),
                    }),
                )),
                codomain: Box::new(Type::Base(BaseType::Int)),
            },
        });
        // The cast goes away; its predicate term survives as a sibling.
        let v1 = TypedExpr::tuple(vec![cast, pred(), int(0)]);
        let v2 = TypedExpr::tuple(vec![pred(), int(0)]);
        let r = diff(&v1, &v2);

        // The matcher pairs one of the two identical predicate terms with v2's,
        // leaving a `Cast` that is deleted at its root with a live node inside.
        let gone: HashSet<*const TypedExpr> =
            r.deleted.iter().map(|e| *e as *const TypedExpr).collect();
        let mut roots = Vec::new();
        collect_deleted_roots(&v1, &gone, &mut roots);
        assert!(
            roots.iter().any(|(e, _)| matches!(e.node, N::Cast { .. })),
            "the cast is deleted:\n{r}",
        );
        // The invariant `subtree_entirely_in` exists to state: a root marked
        // *whole* — the one that collapses in the rendering and stops the walk —
        // has nothing matched under it.
        let matched: HashSet<*const TypedExpr> = r
            .matched
            .iter()
            .map(|m| m.src as *const TypedExpr)
            .collect();
        fn any_matched(e: &TypedExpr, matched: &HashSet<*const TypedExpr>) -> bool {
            matched.contains(&(e as *const TypedExpr))
                || child_exprs(e).into_iter().any(|c| any_matched(c, matched))
        }
        for (root, whole) in roots {
            assert!(
                !whole || !any_matched(root, &matched),
                "a wholly-deleted root must not cover a matched node:\n{r}",
            );
        }
    }

    #[test]
    fn distinct_binders_of_one_group_get_distinct_correspondents() {
        // Every binder a node introduces gets its own correspondent token, so a
        // use of one does not hash equal to a use of another. Without that, a
        // `letrec`'s whole group collapsed to one correspondent and swapping
        // which binding the body reads classified `Same` — an unsound share.
        let group = |body: TypedExpr| {
            TypedExpr::letrec(
                vec![
                    (TypedBinding::new_unannotated("p"), int(1)),
                    (TypedBinding::new_unannotated("q"), int(2)),
                ],
                body,
            )
        };
        let a = group(mul(var("p"), int(10)));
        let b = group(mul(var("q"), int(10)));
        let r = diff(&a, &b);
        assert!(
            !r.is_identical(),
            "reading a different binding of the group is a change:\n{r}"
        );
        // And the divergence localizes to the variable, not to the `letrec`.
        let sites = r.divergences();
        assert_eq!(sites.len(), 1, "sites: {sites:?}");
        assert!(
            matches!(
                &sites[0],
                Divergence::Changed(m)
                    if matches!(&m.dst.node, TypedExprNode::Var(n) if n.base() == "q")
            ),
            "sites: {sites:?}",
        );
    }

    #[test]
    fn a_swapped_pair_of_registers_is_not_a_shared_root() {
        // The same defect on a real program: `channelize` emits one `LetRec`
        // group per transaction, so two mutable registers shared one
        // correspondent and a tuple returning them swapped claimed to be
        // reusable wholesale.
        let prog = |tail: &str| {
            format!(
                "{}{tail}\n",
                indoc! {"
                    a: Mut(Int, Txn) := 0
                    b: Mut(Int, Txn) := 0
                    for x in [1, 2]:
                        with begin():
                            a := a + x
                            b := b + a
                    "}
            )
        };
        let (v1, v2) = (
            prog("(await_final(a), await_final(b))"),
            prog("(await_final(b), await_final(a))"),
        );
        for phase in [Phase::Channelize, Phase::Planning] {
            let (a, b) = (
                compile_to(&v1, phase).expect("v1"),
                compile_to(&v2, phase).expect("v2"),
            );
            let r = diff(&a, &b);
            assert!(
                !r.is_identical(),
                "a swapped pair of registers is a change at {phase:?}:\n{r}"
            );
            // The swap is one site — the tuple — rather than the whole
            // recurrence: the two reads pair with their counterparts and move.
            let sites = r.divergences();
            assert!(
                matches!(
                    sites.as_slice(),
                    [Divergence::Changed(m)] if matches!(m.dst.node, TypedExprNode::Tuple(_))
                ),
                "at {phase:?} the swap must localize to the tuple:\n{r}",
            );
            // And the tuple itself is not offered for reuse: its two elements
            // returned swapped values.
            assert!(
                !r.shared_roots()
                    .iter()
                    .any(|m| matches!(m.src.node, TypedExprNode::Tuple(_))),
                "at {phase:?} the swapped tuple is not reusable wholesale:\n{r}",
            );
        }
    }

    #[test]
    fn compile_to_rejects_what_compile_program_rejects() {
        // `compile_to` is a second path through the frontend, so a program the
        // real pipeline refuses must not yield a phase snapshot: the differ
        // would otherwise be handed a tree whose illegal construct was silently
        // dropped, and two versions differing only in it would diff as
        // identical. `x := 2` writes to an immutable binding, which
        // `check_mut_write_targets` is what rejects.
        let src = indoc! {"
            x = 1
            x := 2
            x
        "};
        for phase in [
            Phase::Infer,
            Phase::Inline,
            Phase::Channelize,
            Phase::LambdaElim,
            Phase::Planning,
        ] {
            assert!(
                compile_to(src, phase).is_err(),
                "a write to an immutable binding must be rejected at {phase:?}",
            );
        }
        // `Lowered` is below every check by construction — it is the tree as
        // lowering built it, and the write is still a `MutWrite` node there.
        assert!(compile_to(src, Phase::Lower).is_ok());
    }

    #[test]
    fn both_entry_points_compile_to_one_tree() {
        // `compile_program` and `compile_to` run one frontend, so the tree a
        // diff is taken over is the tree the operator graph is built from.
        // Asserted with this differ, which is what makes it an equality modulo
        // the uids the two runs mint independently — `assert_eq!` on the two
        // `Expr`s would fail on those alone.
        //
        // Only `Phase::Planning` is checkable this way: it is the phase
        // `compile_program` runs to, and `CompiledProgram::ast` is its output.
        for src in [FILTER_AGG, JOIN, ACCUM, TXN] {
            let mut ctx = GlobalContext::new();
            let compiled = compile_program(&mut ctx, src, Box::new(|| {}))
                .unwrap_or_else(|e| panic!("compile_program failed on {src:?}: {e:?}"));
            let planned = compile_to(src, Phase::Planning)
                .unwrap_or_else(|e| panic!("compile_to failed on {src:?}: {e:?}"));
            let d = diff(&compiled.ast, &planned);
            assert!(
                d.is_identical(),
                "the two entry points disagree on {src:?}: {:?}",
                d.divergences(),
            );
        }
    }

    #[test]
    fn both_entry_points_agreement_is_not_vacuous() {
        // The agreement above would pass on any two trees the differ happened to
        // match wholesale, so pin that a genuinely different phase output fails
        // it. `LambdaElim`'s output is one phase above `Planning`.
        let src = FILTER_AGG;
        let mut ctx = GlobalContext::new();
        let compiled = compile_program(&mut ctx, src, Box::new(|| {})).expect("compiles");
        let earlier = compile_to(src, Phase::LambdaElim).expect("compiles");
        assert!(
            !diff(&compiled.ast, &earlier).is_identical(),
            "a pre-planning tree must not read as the planned one",
        );
    }

    #[test]
    fn diff_programs_end_to_end_from_source() {
        // The public single-call entry: compile both sources to a phase and
        // diff, results delivered through the closure.
        //
        // A filter-threshold edit (`>= 18` → `>= 21`) is reflected at the
        // lowered phase.
        let changed = diff_programs(FILTER_AGG, FILTER_AGG_21, Phase::Lower, |d| {
            d.updated().count()
        })
        .expect("compile + diff should succeed");
        assert!(changed > 0, "the edit is reflected");

        // Identical programs diff as identical at the inferred phase.
        let identical = diff_programs(FILTER_AGG, FILTER_AGG, Phase::Infer, |d| d.is_identical())
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
        let identical = diff_programs(prog, prog, Phase::Infer, |d| d.is_identical())
            .expect("stdin program should compile to the inferred phase and diff");
        assert!(identical);
    }
}
