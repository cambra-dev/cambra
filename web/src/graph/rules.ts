// The rules that merge drawn boxes into composites.
//
// `drawGraphOf` suppresses two operator kinds and draws the rest one box each.
// Most of those boxes are plumbing — a run of unary maps, a `Memo` with one
// consumer, the `MakeRecord` half of a binop — and each rule below merges one
// such shape into the box that reads it.
//
// A merge is over the *drawn* graph, not the wire: the predicates are stated in
// box kinds, edge roles and degrees counted in boxes. Every rule but R10 merges
// a box into the box that reads it and shares the preconditions in
// [`absorbForward`].
//
// Every id stays addressable. A composite lists its members, and a suppressed
// operator riding an edge that a merge made internal becomes one of the
// composite's fan-outs — see `drawGraphOf`, which owns that step.

import type { DrawEdge, DrawNode } from "./model";

/** A box's kind, before any rule renames it. */
const MAPS = new Set([
  "MapResult",
  "MapResultWithSource",
  "MapResultToConst",
  "SelectField",
  "MapChain",
]);
/** Product constructors: `MakeRecord` over scalars, `Zip` over collections. */
const FANS = new Set(["Zip", "MakeRecord"]);
const GUARDS = new Set(["Filter", "Restrict"]);
/** Each folding aggregate, and the operator that reads its result out. */
const AGGREGATE_PAIRS = new Map([
  ["Aggregate", "ExtractAggregate"],
  ["MapAggregate", "MapExtractAggregate"],
]);
const FOLD_OF_EXTRACT = new Map([...AGGREGATE_PAIRS].map(([fold, extract]) => [extract, fold]));
const STORES = new Set(["InductionStore", "CommitOperator"]);

/**
 * The kinds R1 will fold into a constant cone.
 *
 * An allowlist rather than a list of kinds to exclude, because the two fail in
 * opposite directions. A denylist has to name every operator that reads the
 * world, so an operator added later is folded into a chip by default and its
 * value disappears from the drawing. An allowlist leaves a new operator drawn as
 * its own box until someone adds it, which is visible and harmless.
 *
 * Every kind here computes from its inputs alone.
 */
const CONSTANT_CONE = new Set([
  "Constant",
  "MapResult",
  "MapResultToConst",
  "MapResultWithSource",
  "SelectField",
  "MapChain",
  "Zip",
  "MakeRecord",
  "Binop",
  "Filter",
  "Restrict",
  "VariantWrap",
  "Memo",
]);

/**
 * The largest composite a rule will build.
 *
 * A bound on what one hover card has to explain. The rules are meant to
 * saturate below it, so a limit that starts binding means a rule has begun
 * over-reaching.
 */
export const MAX_MEMBERS = 6;

/**
 * The names the rules give a composite, which are not operator kinds. Every
 * other capitalized string in this file names one.
 */
export const COMPOSITE_NAMES = new Set(["Binop", "Iterate", "MapChain"]);

/**
 * One drawn edge between two classes, standing for the base edges in `parts`.
 *
 * Parallel edges of one role between two classes are one edge. It is a `share`
 * if any part is, and a back edge if any part is, so a recurrence into a merged
 * store still reads as one.
 */
export interface QEdge {
  from: number;
  to: number;
  role: string;
  kind: string;
  deferred: boolean;
  parts: DrawEdge[];
}

/**
 * The drawn graph's edges over the classes `find` names: the edges between two
 * classes, collapsed as [`QEdge`] says, and apart from them the base edges with
 * both ends in one class, which no drawing shows, keyed by that class.
 *
 * The one definition of which edges are the same, shared by the rules and by
 * the drawing they produce, so the two never disagree about a box's degree.
 */
export function collapse(
  base: readonly DrawEdge[],
  find: (id: number) => number,
): { edges: QEdge[]; internal: Map<number, DrawEdge[]> } {
  const edges: QEdge[] = [];
  const byKey = new Map<string, QEdge>();
  const internal = new Map<number, DrawEdge[]>();
  for (const e of base) {
    const from = find(e.from);
    const to = find(e.to);
    if (from === to) {
      const list = internal.get(from);
      if (list) list.push(e);
      else internal.set(from, [e]);
      continue;
    }
    const key = `${from}>${to}|${e.role}`;
    const prior = byKey.get(key);
    if (prior) {
      if (e.kind === "share") prior.kind = "share";
      prior.deferred = prior.deferred || e.deferred;
      prior.parts.push(e);
      continue;
    }
    const q: QEdge = { from, to, role: e.role, kind: e.kind, deferred: e.deferred, parts: [e] };
    byKey.set(key, q);
    edges.push(q);
  }
  return { edges, internal };
}

/**
 * The merge state: a union-find over drawn node ids, plus each class's name.
 *
 * The class root is the **representative** — the box the others merged into,
 * and the one whose output the composite produces, because every rule keeps the
 * downstream box.
 */
export class Merge {
  private readonly parent = new Map<number, number>();
  private readonly memberList = new Map<number, number[]>();
  private readonly tag = new Map<number, string>();
  private readonly node = new Map<number, DrawNode>();

  constructor(
    nodes: DrawNode[],
    private readonly base: DrawEdge[],
  ) {
    for (const n of nodes) {
      this.parent.set(n.id, n.id);
      this.memberList.set(n.id, [n.id]);
      this.node.set(n.id, n);
      // A boundary's label carries its name — `Sink(main)` — which is the name
      // to keep; every other box is named by its kind.
      this.tag.set(n.id, n.label);
    }
  }

  find(x: number): number {
    let root = x;
    while (this.parent.get(root) !== root) root = this.parent.get(root)!;
    let at = x;
    while (this.parent.get(at) !== at) {
      const next = this.parent.get(at)!;
      this.parent.set(at, root);
      at = next;
    }
    return root;
  }

  /** Every class root, in the drawn graph's own order. */
  classes(): number[] {
    return [...this.parent.keys()].filter((k) => this.find(k) === k);
  }

  members(c: number): number[] {
    return this.memberList.get(this.find(c))!;
  }

  name(c: number): string {
    return this.tag.get(this.find(c))!;
  }

  nodeOf(id: number): DrawNode {
    return this.node.get(id)!;
  }

  /** Merge `gone` into `kept`, which becomes the representative. */
  private union(kept: number, gone: number, name: string): void {
    const a = this.find(kept);
    const b = this.find(gone);
    if (a === b) return;
    this.parent.set(b, a);
    this.memberList.set(a, [...this.memberList.get(a)!, ...this.memberList.get(b)!]);
    this.memberList.delete(b);
    this.tag.set(a, name);
  }

  /** The edges between classes; see [`collapse`]. */
  edges(): QEdge[] {
    return collapse(this.base, (x) => this.find(x)).edges;
  }

  outgoing(): Map<number, QEdge[]> {
    return group(this.edges(), (e) => e.from);
  }

  incoming(): Map<number, QEdge[]> {
    return group(this.edges(), (e) => e.to);
  }

  chipCount(c: number): number {
    return this.members(c).reduce((a, m) => a + this.nodeOf(m).chips.length, 0);
  }

  /** A `Source` or a `Sink`: the program's edges with the world, never merged. */
  isBoundary(c: number): boolean {
    return this.members(c).some((m) => this.nodeOf(m).role !== "operator");
  }

  fits(a: number, b: number): boolean {
    return this.members(a).length + this.members(b).length <= MAX_MEMBERS;
  }

  merge(kept: number, gone: number, name: string): void {
    this.union(kept, gone, name);
  }
}

function group<T>(items: T[], key: (t: T) => number): Map<number, T[]> {
  const m = new Map<number, T[]>();
  for (const it of items) {
    const k = key(it);
    const list = m.get(k);
    if (list) list.push(it);
    else m.set(k, [it]);
  }
  return m;
}

const distinct = (edges: QEdge[] | undefined, end: (e: QEdge) => number): Set<number> =>
  new Set((edges ?? []).map(end));

interface Context {
  m: Merge;
  out: Map<number, QEdge[]>;
  in: Map<number, QEdge[]>;
}

/** Whether `c` merges into the box that reads it, given the edge to it. */
type Forward = (ctx: Context, c: number, edge: QEdge) => boolean;

/**
 * Merge a box into the one box that reads it, when `pred` holds.
 *
 * The five preconditions every such rule shares: exactly one box reads it; no
 * edge between the two, in either direction, is a back edge; it is not a
 * boundary; the box reading it is not a boundary; and the merged box holds at
 * most `MAX_MEMBERS`.
 *
 * A back edge is excluded because it is the recurrence. It runs from a writer to
 * the store it feeds, so merging either end into the other would make the edge
 * internal to one box, and an internal edge is dropped — the cycle would vanish
 * from the drawing. The forward edge runs from the store to the writer, so the
 * back edge can be an incoming edge of the box being absorbed.
 */
function absorbForward(
  m: Merge,
  pred: Forward,
  nameOf: (ctx: Context, host: number) => string,
): boolean {
  const ctx: Context = { m, out: m.outgoing(), in: m.incoming() };
  for (const c of m.classes()) {
    const edges = ctx.out.get(c) ?? [];
    if (edges.length === 0) continue;
    if (distinct(edges, (e) => e.to).size !== 1) continue;
    if (edges.some((e) => e.deferred)) continue;
    if (m.isBoundary(c)) continue;
    const host = edges[0].to;
    if ((ctx.in.get(c) ?? []).some((e) => e.deferred && e.from === host)) continue;
    if (m.isBoundary(host)) continue;
    if (!m.fits(c, host)) continue;
    if (!pred(ctx, c, edges[0])) continue;
    m.merge(host, c, nameOf(ctx, host));
    return true;
  }
  return false;
}

const keepHost = (ctx: Context, host: number) => ctx.m.name(host);

interface Rule {
  name: string;
  run: (m: Merge) => boolean;
}

export const RULES: Rule[] = [
  {
    // A subgraph that computes a fixed value, drawn as a chain of boxes. It
    // folds into the box that reads it as members of that composite.
    name: "R1 constant cone",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c) =>
          (ctx.in.get(c) ?? []).length === 0 &&
          // Test the members, not the composite's name: R6 names an
          // `IterateExtent` + `MapResult` composite `Iterate`, and a name-based
          // test then stops matching it, so R1 would absorb a whole extent read.
          ctx.m.members(c).every((x) => CONSTANT_CONE.has(ctx.m.nodeOf(x).label)),
        keepHost,
      ),
  },
  {
    // A tuple or record built from one field: two boxes wrapping one value.
    name: "R2 unary fan-in",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c) =>
          FANS.has(ctx.m.name(c)) &&
          (ctx.in.get(c) ?? []).length === 1 &&
          // A `MakeRecord` with one producer and one chip is a binop with a
          // literal operand, not a one-field wrap.
          ctx.m.chipCount(c) === 0,
        keepHost,
      ),
  },
  {
    // A `Memo` memoizes for its consumers; with one it memoizes for nobody the
    // reader can see. One with two or more stays drawn: it is a share point.
    name: "R3 pass-through Memo",
    run: (m) => absorbForward(m, (ctx, c) => ctx.m.name(c) === "Memo", keepHost),
  },
  {
    // `a + b` is a `MakeRecord` pairing the operands, a `Constant` holding the
    // function, and a `MapResult` applying it. The constant is already a chip.
    name: "R4 binop",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) => FANS.has(ctx.m.name(c)) && MAPS.has(ctx.m.name(e.to)),
        () => "Binop",
      ),
  },
  {
    // `sum(xs)` is always an `Aggregate` that folds and an `ExtractAggregate`
    // that reads the result out, and a group-by's is the keyed pair,
    // `MapAggregate` and `MapExtractAggregate`. The composite takes the folding
    // half's name, which says whether it is keyed.
    name: "R5 aggregate pair",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) => AGGREGATE_PAIRS.get(ctx.m.name(c)) === ctx.m.name(e.to),
        (ctx, host) => FOLD_OF_EXTRACT.get(ctx.m.name(host))!,
      ),
  },
  {
    // An `IterateExtent` produces the positions of a collection and exists to
    // feed the map that reads them. `MapResultWithSource` must be in the
    // consumer set: an extent read off a registered source feeds one.
    name: "R6 iterate + map",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) =>
          ctx.m.name(c) === "IterateExtent" && MAPS.has(ctx.m.name(e.to)) && e.role === "input",
        () => "Iterate",
      ),
  },
  {
    // Record projection and arithmetic lower to one map per step, so reading a
    // field and passing it on is a run of maps in a line.
    name: "R7 map chain",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) => MAPS.has(ctx.m.name(c)) && MAPS.has(ctx.m.name(e.to)) && e.role === "input",
        () => "MapChain",
      ),
  },
  {
    // A `Filter` takes its predicate from another box, which the wire records as
    // a stage ahead of it — the same shape it gives a `Constant` operand.
    name: "R8 guard",
    run: (m) =>
      absorbForward(m, (ctx, _c, e) => e.role === "predicate" && GUARDS.has(ctx.m.name(e.to)), keepHost),
  },
  {
    // A decision arm's constructor: one operator tagging its value with the arm
    // it belongs to, with no meaning apart from that arm.
    name: "R9 variant wrap",
    run: (m) => absorbForward(m, (ctx, c) => ctx.m.name(c) === "VariantWrap", keepHost),
  },
  {
    // A store and the driver that steps it are one mechanism. Not a forward
    // absorb: the driver's edge runs to its store.
    //
    // `TransactWriter` is the same shape and is excluded. The writer produces
    // the store's back edge, so merging it into the store makes that edge
    // internal and the drawing drops the recurrence.
    name: "R10 driver into its store",
    run: (m) => {
      const out = m.outgoing();
      const inc = m.incoming();
      for (const c of m.classes()) {
        const kind = m.name(c);
        if (kind !== "InductionDriver" && kind !== "TransactDriver") continue;
        const store = [...distinct(inc.get(c), (e) => e.from), ...distinct(out.get(c), (e) => e.to)].find(
          (n) => STORES.has(m.name(n)),
        );
        if (store === undefined || !m.fits(c, store)) continue;
        m.merge(store, c, m.name(store));
        return true;
      }
      return false;
    },
  },
];

/**
 * Run the rules to a fixed point.
 *
 * The list restarts from the first rule after every merge, so an earlier rule
 * keeps priority over a later one and a box that becomes eligible mid-cascade —
 * a `Memo` whose two consumers have themselves merged — is caught.
 */
export function applyRules(m: Merge): void {
  for (;;) {
    const moved = RULES.some((r) => r.run(m));
    if (!moved) return;
  }
}
