// The rules that merge drawn boxes into composites.
//
// `drawGraphOf` suppresses two operator kinds and draws the rest one box each,
// which is more boxes than a reader can follow: `order_ledger` draws 121 and
// `asset_cart` 270. Most of them are plumbing — a run of unary maps, a `Memo`
// with one consumer, the `ScalarFanIn` half of a binop — and each rule below
// merges one such shape into the box that reads it.
//
// A merge is over the *drawn* graph, not the wire: the predicates are stated in
// box kinds, edge roles and degrees counted in boxes. Nine of the eleven merge a
// box into the box that reads it and share the preconditions in
// [`absorbForward`]; R10's second shape and R11 do not.
//
// Every id stays addressable. A composite lists its members, and a suppressed
// operator riding an edge that a merge made internal becomes a member too —
// see `drawGraphOf`, which owns that step.

import type { DrawEdge, DrawNode } from "./model";

/** A box's kind, before any rule renames it. */
const MAPS = new Set(["MapResult", "MapResultWithSource", "MapResultToConst", "MapChain"]);
const FANS = new Set(["FanIn", "ScalarFanIn"]);
const GUARDS = new Set(["Filter", "Restrict"]);
const READS = new Set(["StoreDenseRead", "AsOf", "StoreValueStream"]);
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
  "MapChain",
  "FanIn",
  "ScalarFanIn",
  "Binop",
  "Filter",
  "Restrict",
  "VariantWrap",
  "Memo",
]);

/**
 * The largest composite a rule will build.
 *
 * The rules saturate here rather than being tuned to it: the largest composite
 * they build anywhere in the gallery is exactly 6, and limits of 6, 8, 12 and
 * 999 produce identical drawings. It stays as a bound on what one hover card
 * has to explain, and as a signal — a limit that starts binding means a rule
 * has begun over-reaching.
 */
export const MAX_MEMBERS = 6;

/** One quotient edge: an edge of the drawn graph with both ends resolved to boxes. */
interface QEdge {
  from: number;
  to: number;
  role: string;
  kind: string;
  deferred: boolean;
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

  /** The drawn edges, with both ends resolved to classes and self-edges dropped. */
  edges(): QEdge[] {
    const out: QEdge[] = [];
    const seen = new Set<string>();
    for (const e of this.base) {
      const from = this.find(e.from);
      const to = this.find(e.to);
      if (from === to) continue;
      const key = `${from}>${to}|${e.role}|${e.kind}|${e.deferred}`;
      if (seen.has(key)) continue;
      seen.add(key);
      out.push({ from, to, role: e.role, kind: e.kind, deferred: e.deferred });
    }
    return out;
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
 * The five preconditions every such rule shares: exactly one box reads it; none
 * of its outgoing edges is a back edge; it is not a boundary; the box reading it
 * is not a boundary; and the merged box holds at most `MAX_MEMBERS`.
 *
 * A back edge is excluded because it is the recurrence. It runs from a writer to
 * the store it feeds, so merging its producer into its consumer would make the
 * edge internal to one box, and an internal edge is dropped — the cycle would
 * vanish from the drawing.
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
    // folds into the box that reads it and becomes a chip there.
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
          // A `ScalarFanIn` with one producer and one chip is a binop with a
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
    // `a + b` is a `ScalarFanIn` pairing the operands, a `Constant` holding the
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
    // that reads the result out.
    name: "R5 aggregate pair",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) => ctx.m.name(c) === "Aggregate" && ctx.m.name(e.to) === "ExtractAggregate",
        () => "Aggregate",
      ),
  },
  {
    // An `IterateExtent` produces the positions of a collection and exists to
    // feed the map that reads them. `MapResultWithSource` must be in the
    // consumer set: every `IterateExtent` in `asset_cart` feeds one.
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
    // Reading a mutable variable after a loop costs an `IterateExtent` to
    // trigger it, the read itself, and an `ExtractFinal`.
    name: "R10 store read",
    run: (m) =>
      absorbForward(
        m,
        (ctx, c, e) => READS.has(ctx.m.name(c)) && ctx.m.name(e.to) === "ExtractFinal",
        () => "StoreRead",
      ) ||
      absorbForward(
        m,
        (ctx, c, e) =>
          ctx.m.name(c) === "IterateExtent" &&
          (READS.has(ctx.m.name(e.to)) || ctx.m.name(e.to) === "StoreRead") &&
          e.role === "trigger",
        keepHost,
      ),
  },
  {
    // A store and the driver that steps it are one mechanism. Not a forward
    // absorb: the driver's edge runs to its store.
    //
    // `TransactWriter` is the same shape and is excluded. The writer produces
    // the store's back edge, so merging it into the store makes that edge
    // internal and the drawing drops it — `asset_cart` would lose all six.
    name: "R11 driver into its store",
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
