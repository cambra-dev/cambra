//! One element-wise function of a column, built from a chain of element-wise operations and
//! applied as [`FunctionDef::Scalar`](super::FunctionDef).
//!
//! A `zip` of arms over one input converts to `Memo`, `FanOut`, one map per arm, a `Zip` and a
//! map over the pair. When every arm is element-wise, the whole chain is a function of the one
//! input column. [`fuse_prefix`] recognizes such a chain and [`ScalarExpr::eval`] computes it
//! without an operator or an intermediate pair per arm.
//!
//! `eval` works through the input in blocks of [`BLOCK_ROWS`] rows. Every node of the tree but the
//! root writes one block-sized column into a buffer of its own, which later blocks reuse, so the
//! intermediates of a chain are a few kilobytes each, allocated once per `eval`, and each node's
//! kernel runs over a column that is still in cache. The root appends to the result column.

use std::mem::replace;

use smol_str::SmolStr;

use crate::ccl::{Builtin, Expr, Lit, ProjKey, TypedExprNode};

use super::{
    BaseType, BinOpKind as InterpreterBinOp, ColumnValue, Extent, UnaryOpKind, apply_binop_into,
    apply_unaryop_into, binop_output_extent, binop_result_column, tuple_field,
};

/// An element-wise expression over the input column.
///
/// Each node has one parent, so a subterm that two operations read appears once under each of
/// them. Only the input is read more than once, and it is a leaf.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Tree {
    /// The input column.
    Arg,
    /// A literal, repeated at every position.
    Lit(Lit),
    /// A field of a record column.
    Field(Box<Tree>, SmolStr),
    Bin(InterpreterBinOp, Box<Tree>, Box<Tree>),
    Un(UnaryOpKind, Box<Tree>),
}

impl Tree {
    /// How many nodes the tree has: one slot of a [`Scratch`] each.
    fn nodes(&self) -> usize {
        1 + match self {
            Tree::Arg | Tree::Lit(_) => 0,
            Tree::Field(a, _) | Tree::Un(_, a) => a.nodes(),
            Tree::Bin(_, a, b) => a.nodes() + b.nodes(),
        }
    }
}

/// A function of one column, as an expression tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScalarExpr {
    root: Tree,
}

/// Rows evaluated at a time: 8 KiB per column of 64-bit values, so a node's operands and result
/// stay in L1.
const BLOCK_ROWS: usize = 1024;

/// The column in `slot`, leaving the unwritten marker behind.
fn take(slot: &mut ColumnValue) -> ColumnValue {
    replace(slot, ColumnValue::Units(0))
}

/// The columns of an evaluation, one per node of the tree but the root, kept from block to block.
///
/// A node writes its block into its own slot with the `_into` kernels, so a slot's buffer is
/// allocated while the first block is evaluated and reused for every later one, instead of
/// each block allocating a column per node. Nodes number their slots in the order `eval`
/// visits them, which is the same for every block.
struct Scratch<'a> {
    input: &'a ColumnValue,
    /// A slot is `Units(0)` until its node first writes it; no node's result is a `Units`
    /// column, so the marker is unambiguous.
    slots: Vec<ColumnValue>,
    /// The next slot to hand out in the current block.
    next: usize,
    /// The current block: the rows `start..start + len` of the input. A literal column takes
    /// `len`.
    start: usize,
    len: usize,
}

impl<'a> Scratch<'a> {
    fn new(input: &'a ColumnValue, tree: &Tree) -> Self {
        Self {
            input,
            slots: vec![ColumnValue::Units(0); tree.nodes()],
            next: 0,
            start: 0,
            len: 0,
        }
    }

    /// Evaluate `tree` over the rows `start..start + len` and append the block's result to `out`.
    ///
    /// The root's kernel appends straight to `out`, so the result is written once, with no slot
    /// of its own and no copy out of one. `out` is created at the first block with room for
    /// `total` rows, the length of the whole input.
    fn block(
        &mut self,
        tree: &Tree,
        start: usize,
        len: usize,
        total: usize,
        out: &mut Option<ColumnValue>,
    ) {
        self.next = 1;
        self.start = start;
        self.len = len;
        let created = |mut column: ColumnValue| {
            column.reserve(total);
            column
        };
        match tree {
            Tree::Un(op, a) => {
                let a = self.eval(a);
                let out = out.get_or_insert_with(|| created(self.slots[a].empty_like()));
                apply_unaryop_into(*op, &self.slots[a], out);
            }
            Tree::Bin(op, a, b) => {
                let a = self.eval(a);
                let b = self.eval(b);
                let out =
                    out.get_or_insert_with(|| created(binop_result_column(*op, &self.slots[a])));
                apply_binop_into(*op, &self.slots[a], &self.slots[b], out);
            }
            // A root that is a column already has no kernel to write the result with.
            _ => {
                self.next = 0;
                let root = self.eval(tree);
                let out = out.get_or_insert_with(|| created(self.slots[root].empty_like()));
                out.extend_from(&self.slots[root]);
            }
        }
    }

    /// Evaluate `tree` into a fresh slot and return its index.
    fn eval(&mut self, tree: &Tree) -> usize {
        let slot = self.next;
        self.next += 1;
        let rows = self.start..self.start + self.len;
        match tree {
            Tree::Arg => self.input.slice_into(rows, &mut self.slots[slot]),
            Tree::Lit(lit) => fill_lit(lit, self.len, &mut self.slots[slot]),
            // A field of the input is sliced alone, not with the rest of the record column.
            Tree::Field(inner, name) if matches!(**inner, Tree::Arg) => {
                let ColumnValue::Records(fields) = self.input else {
                    panic!("a field of a column that is not a record column")
                };
                fields
                    .get(name)
                    .unwrap_or_else(|| panic!("Missing field {name}"))
                    .slice_into(rows, &mut self.slots[slot]);
            }
            Tree::Field(inner, name) => {
                let inner = self.eval(inner);
                let ColumnValue::Records(mut fields) = take(&mut self.slots[inner]) else {
                    panic!("a field of a column that is not a record column")
                };
                self.slots[slot] = fields
                    .remove(name)
                    .unwrap_or_else(|| panic!("Missing field {name}"));
            }
            Tree::Un(op, a) => {
                let a = self.eval(a);
                let mut out = take(&mut self.slots[slot]);
                if matches!(out, ColumnValue::Units(_)) {
                    out = self.slots[a].empty_like();
                } else {
                    out.clear();
                }
                apply_unaryop_into(*op, &self.slots[a], &mut out);
                self.slots[slot] = out;
            }
            Tree::Bin(op, a, b) => {
                let a = self.eval(a);
                let b = self.eval(b);
                let mut out = take(&mut self.slots[slot]);
                if matches!(out, ColumnValue::Units(_)) {
                    out = binop_result_column(*op, &self.slots[a]);
                } else {
                    out.clear();
                }
                apply_binop_into(*op, &self.slots[a], &self.slots[b], &mut out);
                self.slots[slot] = out;
            }
        }
        slot
    }
}

impl ScalarExpr {
    fn new(root: Tree) -> Self {
        Self { root }
    }

    /// Evaluate over `input`, the column of the values the function is applied to.
    ///
    /// The result is built block by block, with room for all of it reserved at the first block,
    /// so peak memory is the input, the result, and one block's slots.
    pub fn eval(&self, input: &ColumnValue) -> ColumnValue {
        let len = input.len();
        let mut scratch = Scratch::new(input, &self.root);
        let mut out = None;
        let mut start = 0;
        loop {
            let rows = BLOCK_ROWS.min(len - start);
            scratch.block(&self.root, start, rows, len, &mut out);
            start += rows;
            if start >= len {
                break;
            }
        }
        let out = out.expect("a block was evaluated, which created the result");
        debug_assert_eq!(
            out.len(),
            len,
            "ScalarExpr::eval: one result row per input row"
        );
        out
    }
}

impl std::fmt::Display for Tree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tree::Arg => write!(f, "_"),
            Tree::Lit(lit) => match lit {
                Lit::Int(n) => write!(f, "{n}"),
                Lit::String(s) => write!(f, "{s:?}"),
                Lit::Bool(b) => write!(f, "{b}"),
                Lit::Unit => write!(f, "unit"),
            },
            Tree::Field(a, name) => write!(f, "{a}.{name}"),
            Tree::Un(op, a) => write!(f, "{op:?}({a})"),
            Tree::Bin(op, a, b) => {
                write!(f, "{}({a}, {b})", crate::pretty_graph::fmt_binop(op))
            }
        }
    }
}

impl std::fmt::Display for ScalarExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.root.fmt(f)
    }
}

/// `lit` repeated `len` times.
fn lit_column(lit: &Lit, len: usize) -> ColumnValue {
    match lit {
        Lit::Int(n) => ColumnValue::Ints(vec![*n; len]),
        Lit::String(s) => ColumnValue::Strings(vec![s.clone(); len]),
        Lit::Bool(b) => ColumnValue::Bools(vec![*b; len]),
        Lit::Unit => unreachable!("a unit literal is never fused: the recognizer declines it"),
    }
}

/// `lit` repeated `len` times, written into `out`.
///
/// A literal node's slot is written by this function alone, so a column of the literal's kind
/// already holds that literal from an earlier block, and only its length can differ. `resize`
/// cuts it or extends it with the literal, and writes nothing when the length is the same,
/// which is every block but the last. Any other `out` is replaced.
fn fill_lit(lit: &Lit, len: usize, out: &mut ColumnValue) {
    match (lit, &mut *out) {
        (Lit::Int(n), ColumnValue::Ints(o)) => {
            debug_assert!(
                o.iter().all(|x| x == n),
                "a literal's slot holds the literal"
            );
            o.resize(len, *n);
        }
        (Lit::String(t), ColumnValue::Strings(o)) => {
            debug_assert!(
                o.iter().all(|x| x == t),
                "a literal's slot holds the literal"
            );
            o.resize(len, t.clone());
        }
        (Lit::Bool(b), ColumnValue::Bools(o)) => {
            debug_assert!(
                o.iter().all(|x| x == b),
                "a literal's slot holds the literal"
            );
            o.resize(len, *b);
        }
        _ => *out = lit_column(lit, len),
    }
}

/// A fused chain: the expression, the extents it is applied between, and how many of the
/// chain's elements it replaces.
pub struct Fused {
    pub expr: ScalarExpr,
    pub domain: Extent,
    pub codomain: Extent,
    pub consumed: usize,
}

/// The value a chain element is applied to, while the chain is being read. A product is
/// tracked structurally and is an expression only where an operation needs its column.
#[derive(Clone)]
enum Val {
    /// A column, with the extent of its values.
    Column(Tree, Extent),
    Tuple(Vec<Val>),
    Record(Vec<(SmolStr, Val)>),
}

struct Parser {
    /// How many operations the chain read so far: every element that is neither the
    /// identity nor a composition of others. Fusing replaces that many operators with one.
    ops: usize,
}

impl Parser {
    /// The column a value stands for. A product has none.
    fn column(v: &Val) -> Option<(Tree, Extent)> {
        match v {
            Val::Column(tree, extent) => Some((tree.clone(), extent.clone())),
            _ => None,
        }
    }

    fn literal(lit: &Lit) -> Option<Val> {
        let base = match lit {
            Lit::Int(_) => BaseType::Int,
            Lit::String(_) => BaseType::String,
            Lit::Bool(_) => BaseType::Bool,
            Lit::Unit => return None,
        };
        Some(Val::Column(Tree::Lit(lit.clone()), Extent::Base(base)))
    }

    fn project(v: Val, key: &ProjKey) -> Option<Val> {
        match (v, key) {
            (Val::Tuple(items), ProjKey::Index(i)) => items.get(*i).cloned(),
            (Val::Record(fields), ProjKey::Field(name)) => fields
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v.clone()),
            (Val::Column(tree, extent), key) => {
                let name = match key {
                    ProjKey::Index(i) => tuple_field(*i),
                    ProjKey::Field(name) => name.clone(),
                };
                let field = extent.record_fields()?.get(&name)?.clone();
                Some(Val::Column(Tree::Field(Box::new(tree), name), field))
            }
            _ => None,
        }
    }

    /// Read `e` as a function applied to `cur`.
    fn step(&mut self, e: &Expr, cur: Val) -> Option<Val> {
        if !matches!(
            &e.node,
            TypedExprNode::Compose(_) | TypedExprNode::Builtin(Builtin::Id)
        ) {
            self.ops += 1;
        }
        match &e.node {
            TypedExprNode::Compose(elts) => elts.iter().try_fold(cur, |cur, e| self.step(e, cur)),
            TypedExprNode::Builtin(Builtin::Id) => Some(cur),
            TypedExprNode::Proj(key) => Self::project(cur, key),
            TypedExprNode::Builtin(Builtin::BinOp(op)) => {
                let Val::Tuple(items) = &cur else { return None };
                let [a, b] = items.as_slice() else {
                    return None;
                };
                let ((a, _), (b, _)) = (Self::column(a)?, Self::column(b)?);
                let op: InterpreterBinOp = (*op).into();
                let extent = binop_output_extent(&op);
                Some(Val::Column(Tree::Bin(op, Box::new(a), Box::new(b)), extent))
            }
            TypedExprNode::Builtin(b @ (Builtin::Neg | Builtin::NotFn)) => {
                let (a, operand) = Self::column(&cur)?;
                let op = if *b == Builtin::Neg {
                    UnaryOpKind::Neg
                } else {
                    UnaryOpKind::Not
                };
                let extent = op.output_extent(&operand);
                Some(Val::Column(Tree::Un(op, Box::new(a)), extent))
            }
            TypedExprNode::Apply { argument, function } => match &function.node {
                // `𝑐 ▷ const` for a literal: the same value at every position.
                TypedExprNode::Builtin(Builtin::Const) => {
                    let TypedExprNode::Lit(lit) = &argument.node else {
                        return None;
                    };
                    Self::literal(lit)
                }
                // Every arm is a function of the value the zip is applied to.
                TypedExprNode::Builtin(Builtin::Zip) => match &argument.node {
                    TypedExprNode::Tuple(arms) => arms
                        .iter()
                        .map(|arm| self.step(arm, cur.clone()))
                        .collect::<Option<Vec<_>>>()
                        .map(Val::Tuple),
                    TypedExprNode::Record(arms) => arms
                        .iter()
                        .map(|(name, arm)| Some((name.clone(), self.step(arm, cur.clone())?)))
                        .collect::<Option<Vec<_>>>()
                        .map(Val::Record),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// The expression a chain ending at `v` yields. A product ends as a tile of its fields
    /// rather than as one column, which a column function cannot build, so a product has none.
    fn root_of(v: &Val) -> Option<(Tree, Extent)> {
        match v {
            // The argument itself: nothing to compute.
            Val::Column(Tree::Arg, _) => None,
            Val::Column(tree, extent) => Some((tree.clone(), extent.clone())),
            Val::Tuple(_) | Val::Record(_) => None,
        }
    }
}

/// Whether a column of `extent` is one `eval` can read: a base type or a record of them.
fn is_plain(extent: &Extent) -> bool {
    match extent {
        Extent::Base(_) => true,
        Extent::Record(fields) => fields.values().all(is_plain),
        _ => false,
    }
}

/// The longest prefix of `chain` that is a pointwise function of its input, as one expression.
/// `input` is the extent of the values the chain is applied to.
///
/// The recognizer reads the identity, projections, literal constants, binary and unary
/// operations, and `zip`s of such chains. The prefix ends before the first other element: an
/// aggregate, a lookup, a conditional, a store read, or a constant that is not a literal has a
/// domain or a value outside the input column. A prefix of one operation keeps its own
/// conversion, since fusing it would replace one operator with one. A binary operation takes its
/// operands from a `zip`, so a prefix that holds one is at least two operations: `x + 1` fuses,
/// and the single-operation prefixes are a lone unary operation (`neg`, `not`), a projection and
/// a literal.
pub fn fuse_prefix(chain: &[Expr], input: &Extent) -> Option<Fused> {
    if !is_plain(input) {
        return None;
    }
    let mut parser = Parser { ops: 0 };
    let mut cur = Val::Column(Tree::Arg, input.clone());
    let mut best: Option<(usize, Tree, Extent)> = None;
    for (k, e) in chain.iter().enumerate() {
        let Some(next) = parser.step(e, cur.clone()) else {
            break;
        };
        cur = next;
        if parser.ops >= 2
            && let Some((tree, extent)) = Parser::root_of(&cur)
        {
            best = Some((k + 1, tree, extent));
        }
    }
    let (consumed, tree, codomain) = best?;
    Some(Fused {
        expr: ScalarExpr::new(tree),
        domain: input.clone(),
        codomain,
        consumed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, LogicKind};

    fn id() -> Expr {
        Expr::builtin(Builtin::Id)
    }

    fn constant(n: i64) -> Expr {
        Expr::apply(Expr::lit(Lit::Int(n)), Expr::builtin(Builtin::Const))
    }

    fn zip(arms: Vec<Expr>) -> Expr {
        Expr::apply(Expr::tuple(arms), Expr::builtin(Builtin::Zip))
    }

    fn binop(op: BinOpKind) -> Expr {
        Expr::builtin(Builtin::from(op))
    }

    fn compare(op: CompareKind, n: i64) -> Expr {
        Expr::compose(vec![
            zip(vec![id(), constant(n)]),
            binop(BinOpKind::Compare(op)),
        ])
    }

    fn int() -> Extent {
        Extent::Base(BaseType::Int)
    }

    /// `x > 500 and x < 1500`, the arms reading the input through a zip with a constant.
    fn conjunction() -> Vec<Expr> {
        vec![
            zip(vec![
                compare(CompareKind::Greater, 500),
                compare(CompareKind::Less, 1500),
            ]),
            binop(BinOpKind::BoolLogic(LogicKind::And)),
        ]
    }

    fn bools(column: ColumnValue) -> Vec<bool> {
        let ColumnValue::Bools(bits) = column else {
            panic!("expected a Bool column, got {column:?}")
        };
        bits
    }

    #[test]
    fn a_conjunction_of_comparisons_is_one_expression() {
        let fused = fuse_prefix(&conjunction(), &int()).expect("every arm is element-wise");
        assert_eq!(fused.consumed, 2);
        assert_eq!(fused.codomain, Extent::Base(BaseType::Bool));
        let out = fused
            .expr
            .eval(&ColumnValue::Ints(vec![100, 600, 1499, 1500, 2000]));
        assert_eq!(bools(out), [false, true, true, false, false]);
    }

    /// `x * x + x` reads the input three times.
    #[test]
    fn an_expression_may_read_the_input_more_than_once() {
        let mul = BinOpKind::Arithmetic(ArithmeticKind::Mul);
        let add = BinOpKind::Arithmetic(ArithmeticKind::Add);
        let chain = vec![
            zip(vec![
                Expr::compose(vec![zip(vec![id(), id()]), binop(mul)]),
                id(),
            ]),
            binop(add),
        ];
        let fused = fuse_prefix(&chain, &int()).unwrap();
        assert_eq!(
            fused.expr.eval(&ColumnValue::Ints(vec![1, 2, 3])),
            ColumnValue::Ints(vec![2, 6, 12])
        );
    }

    /// A computed subterm that two operations read is one copy under each: the tree has no
    /// node that has two parents, so the sum is evaluated once per reader.
    #[test]
    fn a_shared_computed_subterm_appears_under_each_reader() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let mul = binop(BinOpKind::Arithmetic(ArithmeticKind::Mul));
        // `(x + 1) * (x + 1)`, as the chain `⟨id, 1⟩ ≫ add ≫ ⟨id, id⟩ ≫ mul`.
        let chain = vec![
            zip(vec![id(), constant(1)]),
            add,
            zip(vec![id(), id()]),
            mul,
        ];
        let fused = fuse_prefix(&chain, &int()).unwrap();
        assert_eq!(
            fused.expr.eval(&ColumnValue::Ints(vec![1, 2, 3])),
            ColumnValue::Ints(vec![4, 9, 16])
        );
    }

    /// `7 - x` and `x - 7` keep their operand order through the zip.
    #[test]
    fn operand_order_survives_the_zip() {
        let sub = binop(BinOpKind::Arithmetic(ArithmeticKind::Sub));
        let left = vec![zip(vec![constant(7), id()]), sub.clone()];
        let right = vec![zip(vec![id(), constant(7)]), sub];
        let input = || ColumnValue::Ints(vec![1, 10]);
        let eval = |chain: &[Expr]| fuse_prefix(chain, &int()).unwrap().expr.eval(&input());
        assert_eq!(eval(&left), ColumnValue::Ints(vec![6, -3]));
        assert_eq!(eval(&right), ColumnValue::Ints(vec![-6, 3]));
    }

    #[test]
    fn a_projection_reads_a_field_of_a_record_column() {
        let record = Extent::Record(
            [(tuple_field(0), int()), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![Expr::proj_index(0), Expr::proj_index(1)]), add];
        let fused = fuse_prefix(&chain, &record).unwrap();
        let input = ColumnValue::Records(
            [
                (tuple_field(0), ColumnValue::Ints(vec![1, 2])),
                (tuple_field(1), ColumnValue::Ints(vec![10, 20])),
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(fused.expr.eval(&input), ColumnValue::Ints(vec![11, 22]));
    }

    /// Fusing one operation would replace one operator with one.
    /// `x + 1` is the `zip` of the input with a constant and the `add`: two operations, so it
    /// fuses, where `neg x` and `not x` are one.
    #[test]
    fn adding_a_constant_fuses_and_a_lone_unary_operation_does_not() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let fused = fuse_prefix(&[zip(vec![id(), constant(1)]), add], &int()).unwrap();
        assert_eq!(fused.consumed, 2);
        assert_eq!(
            fused.expr.eval(&ColumnValue::Ints(vec![1, 2])),
            ColumnValue::Ints(vec![2, 3])
        );
        assert!(fuse_prefix(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
        let bools = Extent::Base(BaseType::Bool);
        assert!(fuse_prefix(&[Expr::builtin(Builtin::NotFn)], &bools).is_none());
    }

    #[test]
    fn a_lone_operation_is_left_to_its_own_conversion() {
        assert!(fuse_prefix(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
        assert!(
            fuse_prefix(&[binop(BinOpKind::Arithmetic(ArithmeticKind::Add))], &int()).is_none()
        );
    }

    /// Two operations fuse whether or not a `zip` joins them.
    #[test]
    fn a_chain_of_unary_operations_fuses_without_a_zip() {
        let chain = vec![Expr::builtin(Builtin::Neg), Expr::builtin(Builtin::Neg)];
        let fused = fuse_prefix(&chain, &int()).expect("two operations");
        assert_eq!(fused.consumed, 2);
        assert_eq!(
            fused.expr.eval(&ColumnValue::Ints(vec![1, -2, 3])),
            ColumnValue::Ints(vec![1, -2, 3])
        );
        let bools = Extent::Base(BaseType::Bool);
        let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
        let fused = fuse_prefix(&chain, &bools).expect("two operations");
        let input = vec![true, false, true];
        assert_eq!(
            fused.expr.eval(&ColumnValue::Bools(input.clone())),
            ColumnValue::Bools(input)
        );
    }

    /// The prefix stops before an element the recognizer does not read.
    #[test]
    fn the_prefix_ends_before_an_aggregate() {
        let mut chain = conjunction();
        chain.push(Expr::builtin(Builtin::Sum));
        assert_eq!(fuse_prefix(&chain, &int()).unwrap().consumed, 2);
    }

    /// A zip that ends the chain is a tile of fields, which one column cannot be.
    #[test]
    fn a_product_result_is_not_fused() {
        assert!(fuse_prefix(&[zip(vec![id(), constant(1)])], &int()).is_none());
    }

    #[test]
    fn an_arm_outside_the_element_wise_set_declines_the_chain() {
        let chain = vec![
            zip(vec![id(), Expr::builtin(Builtin::Sum)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ];
        assert!(fuse_prefix(&chain, &int()).is_none());
    }

    #[test]
    fn a_column_of_collections_is_not_read() {
        let function = Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(int()),
        };
        assert!(fuse_prefix(&conjunction(), &function).is_none());
    }

    /// A projection that picks one arm and an abandoned attempt both read more than the
    /// expression keeps. The expression holds none of it, so equal expressions compare equal.
    #[test]
    fn a_projection_and_an_abandoned_attempt_leave_the_same_expression() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let mul = binop(BinOpKind::Arithmetic(ArithmeticKind::Mul));
        let plain = vec![zip(vec![id(), constant(1)]), add.clone()];
        let plain = fuse_prefix(&plain, &int()).unwrap().expr;
        // `(x + 1, x * 2).0` reads the sum and abandons the product.
        let projected = vec![
            zip(vec![
                Expr::compose(vec![zip(vec![id(), constant(1)]), add.clone()]),
                Expr::compose(vec![zip(vec![id(), constant(2)]), mul]),
            ]),
            Expr::proj_index(0),
        ];
        let projected = fuse_prefix(&projected, &int()).unwrap().expr;
        // A good prefix, then a `zip` whose second arm is not element-wise.
        let abandoned = vec![
            zip(vec![id(), constant(1)]),
            add.clone(),
            zip(vec![
                Expr::compose(vec![zip(vec![id(), constant(9)]), add]),
                Expr::builtin(Builtin::Sum),
            ]),
        ];
        let abandoned = fuse_prefix(&abandoned, &int()).unwrap().expr;
        assert_eq!(projected, plain);
        assert_eq!(abandoned, plain);
        assert_eq!(
            plain.eval(&ColumnValue::Ints(vec![1, 2])),
            ColumnValue::Ints(vec![2, 3])
        );
    }

    /// A column of `n` rows, longer than one block when `n` is.
    fn ramp(n: usize) -> ColumnValue {
        ColumnValue::Ints((0..n as i64).map(|i| i * 7 % 3000).collect())
    }

    /// The blocks' results concatenate into the column a single pass would give, whether the
    /// length is empty, inside one block, a multiple of a block, or ends in a partial block.
    #[test]
    fn blocks_concatenate_into_the_whole_column() {
        let chain = conjunction();
        let fused = fuse_prefix(&chain, &int()).unwrap();
        for n in [
            0,
            1,
            BLOCK_ROWS - 1,
            BLOCK_ROWS,
            BLOCK_ROWS + 1,
            3 * BLOCK_ROWS,
            3 * BLOCK_ROWS + 37,
        ] {
            let ColumnValue::Ints(xs) = ramp(n) else {
                unreachable!()
            };
            let want: Vec<bool> = xs.iter().map(|&x| x > 500 && x < 1500).collect();
            assert_eq!(
                bools(fused.expr.eval(&ColumnValue::Ints(xs))),
                want,
                "n = {n}"
            );
        }
    }

    /// A projection reads its field's rows block by block.
    #[test]
    fn a_record_column_is_evaluated_block_by_block() {
        let record = Extent::Record(
            [(tuple_field(0), int()), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![Expr::proj_index(0), Expr::proj_index(1)]), add];
        let fused = fuse_prefix(&chain, &record).unwrap();
        let n = 2 * BLOCK_ROWS + 5;
        let column = |f: fn(i64) -> i64| ColumnValue::Ints((0..n as i64).map(f).collect());
        let input = ColumnValue::Records(
            [
                (tuple_field(0), column(|i| i)),
                (tuple_field(1), column(|i| 10 * i)),
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(fused.expr.eval(&input), column(|i| 11 * i));
    }

    /// A column of `Bool`s is cut into blocks like any other.
    #[test]
    fn a_bool_column_is_evaluated_block_by_block() {
        let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
        let fused = fuse_prefix(&chain, &Extent::Base(BaseType::Bool)).unwrap();
        let input: Vec<bool> = (0..2 * BLOCK_ROWS + 5).map(|i| i % 3 == 0).collect();
        assert_eq!(
            fused.expr.eval(&ColumnValue::Bools(input.clone())),
            ColumnValue::Bools(input)
        );
    }

    /// A node's buffer is the one its first block allocated: later blocks write into it, so
    /// the evaluation allocates per node, not per node and block. The root has no slot: it
    /// appends to the result, whose buffer the first block reserved in full.
    #[test]
    fn a_node_reuses_its_buffer_across_blocks() {
        let pointer = |column: &ColumnValue| -> *const u8 {
            match column {
                ColumnValue::Ints(v) => v.as_ptr().cast(),
                ColumnValue::Bools(v) => v.as_ptr().cast(),
                other => panic!("a column holds {other:?}"),
            }
        };
        let fused = fuse_prefix(&conjunction(), &int()).unwrap();
        let total = 3 * BLOCK_ROWS;
        let input = ramp(total);
        let mut scratch = Scratch::new(&input, &fused.expr.root);
        let mut out = None;
        scratch.block(&fused.expr.root, 0, BLOCK_ROWS, total, &mut out);
        let result = pointer(out.as_ref().unwrap());
        let (root, children) = scratch.slots.split_first().unwrap();
        assert!(
            matches!(root, ColumnValue::Units(0)),
            "the root writes to the result, not a slot"
        );
        let buffers: Vec<*const u8> = children.iter().map(pointer).collect();
        for start in [BLOCK_ROWS, 2 * BLOCK_ROWS] {
            scratch.block(&fused.expr.root, start, BLOCK_ROWS, total, &mut out);
            let children = &scratch.slots[1..];
            for (slot, &before) in children.iter().zip(&buffers) {
                assert_eq!(pointer(slot), before, "block at {start}");
            }
            assert_eq!(pointer(out.as_ref().unwrap()), result, "block at {start}");
        }
        assert_eq!(out.unwrap().len(), total);
    }

    /// A literal's slot keeps its contents between blocks: it grows or shrinks to the block's
    /// length, and a block of the same length writes nothing.
    #[test]
    fn a_literal_slot_follows_the_block_length() {
        let mut slot = ColumnValue::Units(0);
        for len in [4, 4, 2, 6, 0, 3] {
            fill_lit(&Lit::Int(7), len, &mut slot);
            assert_eq!(slot, ColumnValue::Ints(vec![7; len]), "len = {len}");
        }
        let mut slot = ColumnValue::Units(0);
        for len in [2, 5, 1] {
            fill_lit(&Lit::Bool(true), len, &mut slot);
            assert_eq!(slot, ColumnValue::Bools(vec![true; len]), "len = {len}");
        }
        let mut slot = ColumnValue::Units(0);
        for len in [3, 1, 4] {
            fill_lit(&Lit::String("a".into()), len, &mut slot);
            assert_eq!(
                slot,
                ColumnValue::Strings(vec!["a".into(); len]),
                "len = {len}"
            );
        }
    }
}
