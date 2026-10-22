//! One element-wise function of a column, built from a chain of element-wise operations and
//! applied as [`FunctionDef::Scalar`](super::FunctionDef).
//!
//! A `zip` of arms over one input converts to `Memo`, `FanOut`, one map per arm, a `Zip` and a
//! map over the pair. When every arm is element-wise, the whole chain is a function of the one
//! input column. [`fuse_prefix`] recognizes such a chain and [`ScalarProgram::eval`] computes it
//! without an operator or an intermediate pair per arm.
//!
//! A [`ScalarProgram`] is a straight-line program over slots: instruction 𝑖 names slot 𝑖, and
//! its operands name earlier slots. A value that two operations read is one slot, computed once.
//! Every `Input` reads a column of a base type and every `Const` is a value of one, so a program
//! has no record: [`fuse_prefix`] takes a comparison of two records apart into a comparison per
//! field.
//!
//! `eval` works through the input in blocks of [`BLOCK_ROWS`] rows. An `Input` or a `Const` is
//! read in place, as a region of the input or one value repeated. Every operation but the last
//! writes one block-sized column into a slot of its own, which later blocks reuse, so the
//! intermediates of a chain are a few kilobytes each, allocated once per `eval`, and each
//! kernel runs over columns that are still in cache. The last instruction appends to the result
//! column.

use std::collections::HashMap;
use std::mem::replace;

use smol_str::SmolStr;

use crate::ccl::{Builtin, Expr, ProjKey, TypedExprNode};

use crate::view::View;

use super::{
    BaseType, BinOpKind as InterpreterBinOp, ColumnValue, ColumnView, CompareKind, Extent,
    LogicKind, UnaryOpKind, Value, apply_binop_views, apply_unaryop_views, binop::compared_fields,
    binop_output_extent, binop_result_column, operator_conversion::expr_to_value, tuple_field,
};

/// The index of an instruction, which is also the slot it writes.
type Slot = u32;

/// One instruction of a [`ScalarProgram`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Instr {
    /// The column of a base type at `path` inside the map's input value; an empty path is the
    /// value itself.
    Input {
        path: Vec<SmolStr>,
    },
    /// One value of a base type at every row.
    Const(Value),
    Bin(InterpreterBinOp, Slot, Slot),
    Un(UnaryOpKind, Slot),
}

/// A function of one column, as a straight-line program over slots.
///
/// The last instruction is the output. Every instruction is an operand of a later one or the
/// output, so equal functions have equal programs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScalarProgram {
    instrs: Vec<Instr>,
}

/// Rows evaluated at a time: 8 KiB per column of 64-bit values, so an instruction's operands
/// and result stay in L1.
const BLOCK_ROWS: usize = 1024;

/// The column of `input` that `path` reads.
fn field<'i>(input: &'i ColumnValue, path: &[SmolStr]) -> &'i ColumnValue {
    path.iter().fold(input, |column, name| {
        let ColumnValue::Records(fields) = column else {
            panic!("a field of a column that is not a record column")
        };
        fields
            .get(name)
            .unwrap_or_else(|| panic!("Missing field {name}"))
    })
}

/// The values of a closed scalar as a view of the value itself, repeated over `len` rows.
fn const_view(value: &Value, len: usize) -> ColumnView<'_> {
    match value {
        Value::Int(n) => ColumnView::Ints(View::repeated(n, len)),
        Value::UInt(n) => ColumnView::UInts(View::repeated(n, len)),
        Value::String(s) => ColumnView::Strings(View::repeated(s, len)),
        Value::Bool(b) => ColumnView::Bools(View::repeated(b, len)),
        _ => unreachable!("a constant instruction holds a value of a base type, got {value:?}"),
    }
}

/// The columns of an evaluation, one per instruction, kept from block to block.
///
/// An operation writes its block into its own slot, so a slot's buffer is allocated while the
/// first block is evaluated and reused for every later one, instead of each block allocating a
/// column per operation. An `Input` or a `Const` writes no slot: its block is read in place as a
/// [`ColumnView`], a region of the input or one value repeated.
struct Scratch<'a> {
    input: &'a ColumnValue,
    /// The slot of an operation is `Units(0)` until its instruction first writes it; no
    /// operation's result is a `Units` column, so the marker is unambiguous. The slot of an
    /// `Input` or a `Const` stays unwritten, and so does the last instruction's, whose kernel
    /// appends to the result.
    slots: Vec<ColumnValue>,
    /// The current block: the rows `start..start + len` of the input.
    start: usize,
    len: usize,
}

impl<'a> Scratch<'a> {
    fn new(input: &'a ColumnValue, program: &ScalarProgram) -> Self {
        Self {
            input,
            slots: vec![ColumnValue::Units(0); program.instrs.len()],
            start: 0,
            len: 0,
        }
    }

    /// The block of instruction `slot` as a view.
    fn view<'s>(&'s self, program: &'s ScalarProgram, slot: usize) -> ColumnView<'s> {
        match &program.instrs[slot] {
            Instr::Input { path } => field(self.input, path)
                .view()
                .unwrap_or_else(|| panic!("the input at {path:?} is a column of a base type"))
                .range(self.start..self.start + self.len),
            Instr::Const(value) => const_view(value, self.len),
            Instr::Bin(..) | Instr::Un(..) => self.slots[slot]
                .view()
                .unwrap_or_else(|| panic!("the result s{slot} is a column of a base type")),
        }
    }

    /// Run `program` over the rows `start..start + len` and append the block's result to `out`.
    ///
    /// The last instruction's kernel appends straight to `out`, so the result is written once,
    /// with no slot of its own and no copy out of one. `out` is the result column of
    /// [`ScalarProgram::empty_output`], with room for the whole input reserved.
    fn block(&mut self, program: &ScalarProgram, start: usize, len: usize, out: &mut ColumnValue) {
        self.start = start;
        self.len = len;
        let (last, body) = program
            .instrs
            .split_last()
            .expect("a program has an output instruction");
        for (slot, instr) in body.iter().enumerate() {
            self.run(program, slot, instr);
        }
        match last {
            Instr::Un(op, a) => {
                apply_unaryop_views(*op, &self.view(program, *a as usize), out);
            }
            Instr::Bin(op, a, b) => {
                let (a, b) = (
                    self.view(program, *a as usize),
                    self.view(program, *b as usize),
                );
                apply_binop_views(*op, &a, &b, out);
            }
            Instr::Input { .. } | Instr::Const(_) => {
                unreachable!("the output of a prefix is an operation, which `root_of` checks")
            }
        }
    }

    /// Write the block of an operation into `slot`. An `Input` or a `Const` is read in place.
    fn run(&mut self, program: &ScalarProgram, slot: usize, instr: &Instr) {
        match instr {
            Instr::Input { .. } | Instr::Const(_) => {}
            Instr::Un(op, a) => {
                let mut out = take(&mut self.slots[slot]);
                let a = self.view(program, *a as usize);
                if matches!(out, ColumnValue::Units(_)) {
                    out = a.empty_like();
                } else {
                    out.clear();
                }
                apply_unaryop_views(*op, &a, &mut out);
                self.slots[slot] = out;
            }
            Instr::Bin(op, a, b) => {
                let mut out = take(&mut self.slots[slot]);
                let (a, b) = (
                    self.view(program, *a as usize),
                    self.view(program, *b as usize),
                );
                if matches!(out, ColumnValue::Units(_)) {
                    out = binop_result_column(*op, &a);
                } else {
                    out.clear();
                }
                apply_binop_views(*op, &a, &b, &mut out);
                self.slots[slot] = out;
            }
        }
    }
}

/// The column in `slot`, leaving the unwritten marker behind.
fn take(slot: &mut ColumnValue) -> ColumnValue {
    replace(slot, ColumnValue::Units(0))
}

impl ScalarProgram {
    /// Evaluate over `input`, the column of the values the function is applied to.
    ///
    /// The result is built block by block, with room for all of it reserved at the first block,
    /// so peak memory is the input, the result, and one block's slots.
    pub fn eval(&self, input: &ColumnValue) -> ColumnValue {
        let len = input.len();
        let mut scratch = Scratch::new(input, self);
        let mut out = self.empty_output(input);
        out.reserve(len);
        let mut start = 0;
        loop {
            let rows = BLOCK_ROWS.min(len - start);
            scratch.block(self, start, rows, &mut out);
            start += rows;
            if start >= len {
                break;
            }
        }
        debug_assert_eq!(
            out.len(),
            len,
            "ScalarProgram::eval: one result row per input row"
        );
        out
    }

    /// The empty column the result is appended to: a column of the output instruction's type,
    /// found from the input's columns and the instructions' types without evaluating any block.
    fn empty_output(&self, input: &ColumnValue) -> ColumnValue {
        let mut empties: Vec<ColumnValue> = Vec::with_capacity(self.instrs.len());
        for instr in &self.instrs {
            let empty = match instr {
                Instr::Input { path } => field(input, path).empty_like(),
                Instr::Const(value) => ColumnValue::single(value.clone()).empty_like(),
                // `neg` and `not` keep their operand's type.
                Instr::Un(_, a) => empties[*a as usize].clone(),
                Instr::Bin(op, a, _) => {
                    let operand = empties[*a as usize]
                        .view()
                        .expect("an operand is a column of a base type");
                    binop_result_column(*op, &operand)
                }
            };
            empties.push(empty);
        }
        empties.pop().expect("a program has an output instruction")
    }
}

impl std::fmt::Display for Instr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instr::Input { path } if path.is_empty() => write!(f, "_"),
            Instr::Input { path } => write!(f, "_.{}", path.join(".")),
            Instr::Const(value) => write!(f, "{value}"),
            Instr::Un(op, a) => write!(f, "{op:?}(s{a})"),
            Instr::Bin(op, a, b) => {
                write!(f, "{}(s{a}, s{b})", crate::pretty_graph::fmt_binop(op))
            }
        }
    }
}

impl std::fmt::Display for ScalarProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (slot, instr) in self.instrs.iter().enumerate() {
            write!(f, "s{slot} = {instr}; ")?;
        }
        write!(f, "=> s{}", self.instrs.len() - 1)
    }
}

/// A fused chain: the program, the extents it is applied between, and how many of the
/// chain's elements it replaces.
pub struct Fused {
    pub program: ScalarProgram,
    pub domain: Extent,
    pub codomain: Extent,
    pub consumed: usize,
}

/// The value a chain element is applied to, while the chain is being read. A `zip` is tracked
/// structurally and is a slot only where an operation needs its column.
#[derive(Clone)]
enum Val {
    /// The chain's input, or a field path into it, not yet read into a slot, with the extent of
    /// its values. An empty path is the input itself.
    Read(Vec<SmolStr>, Extent),
    /// A computed column, with the extent of its values.
    Slot(Slot, Extent),
    /// A closed value, the same at every position, with its extent: held as a value until an
    /// operation reads a base value of it as a column, or a comparison takes a record apart.
    Const(Value, Extent),
    /// The arms of a `zip`, which a binary operation takes its operands from.
    Tuple(Vec<Val>),
}

struct Parser {
    /// The instructions emitted so far. Instructions are appended and never removed.
    instrs: Vec<Instr>,
    /// The `Input` instruction of each path read so far, so a path read twice is one slot.
    reads: HashMap<Vec<SmolStr>, Slot>,
    /// How many operations the chain read so far: every element that is neither the
    /// identity nor a composition of others. Fusing replaces that many operators with one.
    ops: usize,
}

impl Parser {
    fn emit(&mut self, instr: Instr) -> Slot {
        self.instrs.push(instr);
        (self.instrs.len() - 1) as Slot
    }

    /// The column a value stands for, read into a slot: a computed column, a path of the input, or
    /// a base value. A product and a record have none.
    fn column(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        match v {
            Val::Slot(slot, extent) => Some((*slot, extent.clone())),
            Val::Read(path, extent) if has_view(extent) => {
                let slot = match self.reads.get(path) {
                    Some(&slot) => slot,
                    None => {
                        let slot = self.emit(Instr::Input { path: path.clone() });
                        self.reads.insert(path.clone(), slot);
                        slot
                    }
                };
                Some((slot, extent.clone()))
            }
            Val::Const(value, extent) if has_view(extent) => {
                Some((self.emit(Instr::Const(value.clone())), extent.clone()))
            }
            Val::Read(..) | Val::Const(..) | Val::Tuple(_) => None,
        }
    }

    /// `value` at every position, when it has an extent a column of it can be read at: a base
    /// value or a record of them.
    fn constant(value: Value) -> Option<Val> {
        let extent = value_extent(&value)?;
        Some(Val::Const(value, extent))
    }

    /// The fields of a record `v` that is read from the input or is a constant, each as the value
    /// of that field. A value that is not a record has none.
    fn fields_of(v: &Val) -> Option<HashMap<SmolStr, Val>> {
        match v {
            Val::Read(path, extent) => Some(
                extent
                    .record_fields()?
                    .iter()
                    .map(|(name, field)| {
                        let mut path = path.clone();
                        path.push(name.clone());
                        (name.clone(), Val::Read(path, field.clone()))
                    })
                    .collect(),
            ),
            Val::Const(Value::Record(values), extent) => {
                let extents = extent.record_fields()?;
                values
                    .iter()
                    .map(|(name, value)| {
                        let field = Val::Const(value.clone(), extents.get(name)?.clone());
                        Some((name.clone(), field))
                    })
                    .collect()
            }
            _ => None,
        }
    }

    /// `a op b` for a binary operation. Two records compare field by field over the fields
    /// [`compared_fields`] names, as `compare_records` compares the columns of two: `==` is the
    /// conjunction of the fields' comparisons and `!=` their disjunction. A record against
    /// anything but a record, two records with no field in common, and any other operation on a
    /// record have no program.
    fn operation(&mut self, op: InterpreterBinOp, a: &Val, b: &Val) -> Option<(Slot, Extent)> {
        let InterpreterBinOp::Compare(kind @ (CompareKind::Equals | CompareKind::NotEquals)) = op
        else {
            let ((a, _), (b, _)) = (self.column(a)?, self.column(b)?);
            return Some((self.emit(Instr::Bin(op, a, b)), binop_output_extent(&op)));
        };
        match (Self::fields_of(a), Self::fields_of(b)) {
            (None, None) => {
                let ((a, _), (b, _)) = (self.column(a)?, self.column(b)?);
                Some((self.emit(Instr::Bin(op, a, b)), binop_output_extent(&op)))
            }
            (Some(left), Some(right)) => {
                let join = InterpreterBinOp::BoolLogic(if kind == CompareKind::Equals {
                    LogicKind::And
                } else {
                    LogicKind::Or
                });
                // In name order, so that equal chains give equal programs.
                let mut fields: Vec<_> = compared_fields(&left, &right).collect();
                fields.sort_by_key(|(name, ..)| *name);
                let mut joined: Option<Slot> = None;
                for (_, l, r) in fields {
                    let (slot, _) = self.operation(op, l, r)?;
                    joined = Some(match joined {
                        None => slot,
                        Some(prev) => self.emit(Instr::Bin(join, prev, slot)),
                    });
                }
                Some((joined?, binop_output_extent(&join)))
            }
            _ => None,
        }
    }

    /// A field of the chain's input. A projection of a product built in the chain,
    /// `⟨f, g⟩ ≫ .0`, is a product beta redex that `simplify` reduces before conversion, so it is
    /// not read.
    fn project(v: Val, key: &ProjKey) -> Option<Val> {
        let Val::Read(mut path, extent) = v else {
            return None;
        };
        let name = match key {
            ProjKey::Index(i) => tuple_field(*i),
            ProjKey::Field(name) => name.runtime_key(),
        };
        let field = extent.record_fields()?.get(&name)?.clone();
        path.push(name);
        Some(Val::Read(path, field))
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
                let (slot, extent) = self.operation((*op).into(), a, b)?;
                Some(Val::Slot(slot, extent))
            }
            TypedExprNode::Builtin(b @ (Builtin::Neg | Builtin::NotFn)) => {
                let (a, operand) = self.column(&cur)?;
                let op = if *b == Builtin::Neg {
                    UnaryOpKind::Neg
                } else {
                    UnaryOpKind::Not
                };
                let extent = op.output_extent(&operand);
                Some(Val::Slot(self.emit(Instr::Un(op, a)), extent))
            }
            TypedExprNode::Apply { argument, function } => match &function.node {
                // `𝑐 ▷ const` for a closed value: the same value at every position.
                TypedExprNode::Builtin(Builtin::Const) => {
                    Self::constant(expr_to_value(argument).ok()?)
                }
                // Every arm is a function of the value the zip is applied to.
                TypedExprNode::Builtin(Builtin::Zip) => match &argument.node {
                    TypedExprNode::Tuple(arms) => arms
                        .iter()
                        .map(|arm| self.step(arm, cur.clone()))
                        .collect::<Option<Vec<_>>>()
                        .map(Val::Tuple),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// The slot a chain ending at `v` yields. A projection of the input is nothing to compute,
    /// whatever its path: the projection's own conversion takes the field without copying it, and
    /// the prefix ends at an operation, so an `Input` is emitted only for an operation that reads
    /// it. A constant has no root for the same reason, since `simplify` has already reduced
    /// `f ≫ c ▷ const`. A product ends as a tile of its fields rather than as one column, which a
    /// column function cannot build, so a product has none.
    fn root_of(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        match v {
            Val::Slot(..) => self.column(v),
            Val::Read(..) | Val::Const(..) | Val::Tuple(_) => None,
        }
    }
}

/// The extent of a closed value that a column of it can be read at: a base value or a record of
/// them.
fn value_extent(value: &Value) -> Option<Extent> {
    Some(match value {
        Value::Int(_) => Extent::Base(BaseType::Int),
        Value::UInt(_) => Extent::Base(BaseType::UInt),
        Value::String(_) => Extent::Base(BaseType::String),
        Value::Bool(_) => Extent::Base(BaseType::Bool),
        Value::Record(fields) => Extent::Record(
            fields
                .iter()
                .map(|(name, v)| Some((name.clone(), value_extent(v)?)))
                .collect::<Option<_>>()?,
        ),
        _ => return None,
    })
}

/// Whether a column of `extent` has a [`ColumnView`]: a base type other than `Unit`, whose column
/// stores no values.
fn has_view(extent: &Extent) -> bool {
    matches!(extent, Extent::Base(base) if *base != BaseType::Unit)
}

/// Whether a column of `extent` is one `eval` can read from: a base type or a record of them.
fn is_plain(extent: &Extent) -> bool {
    match extent {
        Extent::Base(_) => true,
        Extent::Record(fields) => fields.values().all(is_plain),
        _ => false,
    }
}

/// The longest prefix of `chain` that is a pointwise function of its input, as one program.
/// `input` is the extent of the values the chain is applied to.
///
/// The recognizer reads the identity, projections, closed constants, binary and unary
/// operations, and `zip`s of such chains. The prefix ends before the first other element: an
/// aggregate, a lookup, a conditional, a store read, or a constant that is not closed has a
/// domain or a value outside the input column. A prefix of one operation keeps its own
/// conversion, since fusing it would replace one operator with one. A binary operation takes its
/// operands from a `zip`, so a prefix that holds one is at least two operations: `x + 1` fuses,
/// and the single-operation prefixes are a lone unary operation (`neg`, `not`), a projection and
/// a constant.
pub fn fuse_prefix(chain: &[Expr], input: &Extent) -> Option<Fused> {
    if !is_plain(input) {
        return None;
    }
    let mut parser = Parser {
        instrs: Vec::new(),
        reads: HashMap::new(),
        ops: 0,
    };
    let mut cur = Val::Read(Vec::new(), input.clone());
    // The chosen prefix: how many elements it consumes, how many instructions it keeps, and its
    // output extent.
    let mut best: Option<(usize, usize, Extent)> = None;
    for (k, e) in chain.iter().enumerate() {
        let Some(next) = parser.step(e, cur.clone()) else {
            break;
        };
        cur = next;
        if parser.ops >= 2
            && let Some((output, extent)) = parser.root_of(&cur)
        {
            debug_assert_eq!(
                output as usize + 1,
                parser.instrs.len(),
                "the output of a prefix is the instruction emitted last: no element projects an \
                 arm of a zip away, because `simplify` reduces `⟨f, g⟩ ≫ .0` before conversion"
            );
            best = Some((k + 1, parser.instrs.len(), extent));
        }
    }
    let (consumed, len, codomain) = best?;
    // Instructions past the prefix belong to an element the parse then abandoned.
    parser.instrs.truncate(len);
    Some(Fused {
        program: ScalarProgram {
            instrs: parser.instrs,
        },
        domain: input.clone(),
        codomain,
        consumed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Lit, LogicKind};
    use crate::interpreter::apply_binop_column;

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
            .program
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
            fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])),
            ColumnValue::Ints(vec![2, 6, 12])
        );
    }

    /// A computed subterm that two operations read is one slot, computed once: `(x + 1) * (x + 1)`
    /// holds one `add`.
    #[test]
    fn a_shared_computed_subterm_is_one_slot() {
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
        // The input, the constant, the sum and the product.
        assert_eq!(fused.program.instrs.len(), 4, "{}", fused.program);
        assert_eq!(
            fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])),
            ColumnValue::Ints(vec![4, 9, 16])
        );
    }

    /// Two reads of one field path are one `Input`.
    #[test]
    fn a_field_read_twice_is_one_input() {
        let record = Extent::Record(
            [(tuple_field(0), int()), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![Expr::proj_index(0), Expr::proj_index(0)]), add];
        let fused = fuse_prefix(&chain, &record).unwrap();
        let inputs = fused
            .program
            .instrs
            .iter()
            .filter(|instr| matches!(instr, Instr::Input { .. }))
            .count();
        assert_eq!(inputs, 1, "{}", fused.program);
    }

    /// A closed record is a constant, so a product compares against it in a fused chain.
    #[test]
    fn a_record_constant_fuses() {
        let record = Extent::Record(
            [(tuple_field(0), int()), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let pair = Expr::apply(
            Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
            Expr::builtin(Builtin::Const),
        );
        let eq = binop(BinOpKind::Compare(CompareKind::Equals));
        let chain = vec![zip(vec![id(), pair]), eq];
        let fused = fuse_prefix(&chain, &record).expect("a closed record is a constant");
        let n = 2 * BLOCK_ROWS + 5;
        let input = ColumnValue::Records(
            [
                (
                    tuple_field(0),
                    ColumnValue::Ints((0..n as i64).map(|i| i % 2).collect()),
                ),
                (tuple_field(1), ColumnValue::Ints(vec![2; n])),
            ]
            .into_iter()
            .collect(),
        );
        let want: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
        assert_eq!(bools(fused.program.eval(&input)), want);
    }

    /// The extent `{_0: Int, _1: Int, …}`, one field per name given.
    fn tuple_of_ints(n: usize) -> Extent {
        Extent::Record((0..n).map(|i| (tuple_field(i), int())).collect())
    }

    /// The closed tuple of the integers `ns`, as a constant.
    fn closed_tuple(ns: &[i64]) -> Expr {
        let lits = ns.iter().map(|&n| Expr::lit(Lit::Int(n))).collect();
        Expr::apply(Expr::tuple(lits), Expr::builtin(Builtin::Const))
    }

    /// The result of comparing `input` to the closed tuple `ns` with `op`, as a fused chain.
    fn compare_to_tuple(
        input_extent: &Extent,
        op: CompareKind,
        ns: &[i64],
        input: &ColumnValue,
    ) -> Option<Vec<bool>> {
        let chain = vec![
            zip(vec![id(), closed_tuple(ns)]),
            binop(BinOpKind::Compare(op)),
        ];
        Some(bools(
            fuse_prefix(&chain, input_extent)?.program.eval(input),
        ))
    }

    /// `n` rows of `(i % 2, 2, 7)` as a record column of `width` fields.
    fn tuples(width: usize, n: usize) -> ColumnValue {
        let field = |i: usize| match i {
            0 => ColumnValue::Ints((0..n as i64).map(|i| i % 2).collect()),
            1 => ColumnValue::Ints(vec![2; n]),
            _ => ColumnValue::Ints(vec![7; n]),
        };
        ColumnValue::Records((0..width).map(|i| (tuple_field(i), field(i))).collect())
    }

    /// `==` of two records is the conjunction of the fields' comparisons and `!=` their
    /// disjunction, decided while the chain is read: the program holds comparisons of base
    /// columns, and no record constant.
    #[test]
    fn a_record_comparison_is_taken_apart_into_its_fields() {
        let n = 2 * BLOCK_ROWS + 5;
        let input = tuples(2, n);
        let eq = [CompareKind::Equals, CompareKind::NotEquals]
            .map(|op| compare_to_tuple(&tuple_of_ints(2), op, &[1, 2], &input).unwrap());
        let is_one: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
        assert_eq!(eq[0], is_one);
        assert_eq!(eq[1], is_one.iter().map(|b| !b).collect::<Vec<_>>());
        let chain = vec![
            zip(vec![id(), closed_tuple(&[1, 2])]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        let fused = fuse_prefix(&chain, &tuple_of_ints(2)).unwrap();
        assert!(
            fused
                .program
                .instrs
                .iter()
                .all(|instr| !matches!(instr, Instr::Const(Value::Record(_)))),
            "{}",
            fused.program
        );
    }

    /// A field that is a record is compared the same way, down to its base fields.
    #[test]
    fn a_nested_record_comparison_is_taken_apart_to_base_fields() {
        let inner = tuple_of_ints(2);
        let extent = Extent::Record(
            [(tuple_field(0), inner), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let n = 5;
        let input = ColumnValue::Records(
            [
                (tuple_field(0), tuples(2, n)),
                (tuple_field(1), ColumnValue::Ints(vec![7; n])),
            ]
            .into_iter()
            .collect(),
        );
        let nested = Expr::apply(
            Expr::tuple(vec![
                Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
                Expr::lit(Lit::Int(7)),
            ]),
            Expr::builtin(Builtin::Const),
        );
        let chain = vec![
            zip(vec![id(), nested]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        let fused = fuse_prefix(&chain, &extent).expect("a nested record is compared by field");
        let is_one: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
        assert_eq!(bools(fused.program.eval(&input)), is_one);
    }

    /// Two records compare over the fields both carry, as the columns of two records do
    /// (`compare_records`): a wider value reaching a narrower position keeps its surplus field,
    /// which is not part of the value there.
    #[test]
    fn a_comparison_reads_the_fields_both_records_carry() {
        let n = 7;
        let wide = tuples(3, n);
        let got = compare_to_tuple(&tuple_of_ints(3), CompareKind::Equals, &[1, 2], &wide).unwrap();
        let columns = ColumnValue::Records(
            [
                (tuple_field(0), ColumnValue::Ints(vec![1; n])),
                (tuple_field(1), ColumnValue::Ints(vec![2; n])),
            ]
            .into_iter()
            .collect(),
        );
        let want = apply_binop_column(
            InterpreterBinOp::Compare(crate::scalar_ops::CompareKind::Equals),
            &wide,
            &columns,
        );
        assert_eq!(ColumnValue::Bools(got), want);
    }

    /// A record against a base value, two records with no field in common, and an ordering of two
    /// records are not compared, so the chain stays unfused.
    #[test]
    fn a_comparison_without_a_field_to_compare_is_not_fused() {
        let (record, other) = (tuple_of_ints(2), record_of("x", int()));
        let fuses = |input: &Extent, constant: Expr, op: CompareKind| {
            let chain = vec![zip(vec![id(), constant]), binop(BinOpKind::Compare(op))];
            fuse_prefix(&chain, input).is_some()
        };
        assert!(fuses(&record, closed_tuple(&[1, 2]), CompareKind::Equals));
        assert!(!fuses(&record, constant(1), CompareKind::Equals));
        assert!(!fuses(&other, closed_tuple(&[1, 2]), CompareKind::Equals));
        assert!(!fuses(&record, closed_tuple(&[1, 2]), CompareKind::Less));
    }

    /// A record compared to a record read from the input, or to another constant, is taken apart
    /// the same way, and `!=` joins the fields' comparisons by `or`.
    #[test]
    fn records_compare_with_records_read_or_constant() {
        let n = 6;
        let input = tuples(2, n);
        let record = tuple_of_ints(2);
        let compare = |op, arms: Vec<Expr>| {
            let chain = vec![zip(arms), binop(BinOpKind::Compare(op))];
            bools(fuse_prefix(&chain, &record).unwrap().program.eval(&input))
        };
        let (a, b) = (closed_tuple(&[1, 2]), closed_tuple(&[1, 3]));
        assert_eq!(
            compare(CompareKind::Equals, vec![id(), id()]),
            vec![true; n]
        );
        assert_eq!(
            compare(CompareKind::NotEquals, vec![id(), id()]),
            vec![false; n]
        );
        assert_eq!(
            compare(CompareKind::Equals, vec![a.clone(), b.clone()]),
            vec![false; n]
        );
        assert_eq!(compare(CompareKind::NotEquals, vec![a, b]), vec![true; n]);
    }

    /// A nested record is not equal when any base field differs: `!=` is joined by `or` at every
    /// level.
    #[test]
    fn a_nested_record_differs_when_any_base_field_differs() {
        let extent = Extent::Record(
            [(tuple_field(0), tuple_of_ints(2)), (tuple_field(1), int())]
                .into_iter()
                .collect(),
        );
        let n = 5;
        let input = ColumnValue::Records(
            [
                (tuple_field(0), tuples(2, n)),
                (tuple_field(1), ColumnValue::Ints(vec![7; n])),
            ]
            .into_iter()
            .collect(),
        );
        let nested = |last: i64| {
            let inner = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);
            let pair = Expr::tuple(vec![inner, Expr::lit(Lit::Int(last))]);
            Expr::apply(pair, Expr::builtin(Builtin::Const))
        };
        let ne = |last| {
            let chain = vec![
                zip(vec![id(), nested(last)]),
                binop(BinOpKind::Compare(CompareKind::NotEquals)),
            ];
            bools(fuse_prefix(&chain, &extent).unwrap().program.eval(&input))
        };
        assert_eq!(ne(7), (0..n).map(|i| i % 2 == 0).collect::<Vec<_>>());
        assert_eq!(ne(8), vec![true; n]);
    }

    /// The fields come from the extents, so a column wider than the extent that names it compares
    /// over the fields both sides name, and a field with no values to read is not compared.
    #[test]
    fn a_column_wider_than_its_extent_compares_over_the_extents_fields() {
        let n = 4;
        let wide = tuples(3, n);
        let got = compare_to_tuple(&tuple_of_ints(2), CompareKind::Equals, &[1, 2], &wide);
        assert_eq!(got.unwrap(), (0..n).map(|i| i % 2 == 1).collect::<Vec<_>>());
        let unit = Extent::Record(
            [
                (SmolStr::from("u"), Extent::Base(BaseType::Unit)),
                (SmolStr::from("x"), int()),
            ]
            .into_iter()
            .collect(),
        );
        let chain = vec![
            zip(vec![id(), id()]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        assert!(
            fuse_prefix(&chain, &unit).is_none(),
            "a `Units` column has no view to compare"
        );
    }

    /// Equal chains give equal programs, whatever order a hash map holds the record's fields in.
    #[test]
    fn a_record_comparison_gives_the_same_program_every_time() {
        let wide = tuple_of_ints(12);
        let chain = vec![
            zip(vec![id(), closed_tuple(&(0..12).collect::<Vec<_>>())]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        let first = fuse_prefix(&chain, &wide).unwrap().program;
        for _ in 0..8 {
            assert_eq!(fuse_prefix(&chain, &wide).unwrap().program, first);
        }
    }

    /// A constant is not a root: `simplify` reduces `f ≫ c ▷ const` to the constant, so a chain
    /// does not end at one, and the prefix ends before it.
    #[test]
    fn the_prefix_ends_before_a_trailing_constant() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![id(), constant(1)]), add, constant(5)];
        assert_eq!(fuse_prefix(&chain, &int()).unwrap().consumed, 2);
    }

    /// `7 - x` and `x - 7` keep their operand order through the zip.
    #[test]
    fn operand_order_survives_the_zip() {
        let sub = binop(BinOpKind::Arithmetic(ArithmeticKind::Sub));
        let left = vec![zip(vec![constant(7), id()]), sub.clone()];
        let right = vec![zip(vec![id(), constant(7)]), sub];
        let input = || ColumnValue::Ints(vec![1, 10]);
        let eval = |chain: &[Expr]| fuse_prefix(chain, &int()).unwrap().program.eval(&input());
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
        assert_eq!(fused.program.eval(&input), ColumnValue::Ints(vec![11, 22]));
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
            fused.program.eval(&ColumnValue::Ints(vec![1, 2])),
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
            fused.program.eval(&ColumnValue::Ints(vec![1, -2, 3])),
            ColumnValue::Ints(vec![1, -2, 3])
        );
        let bools = Extent::Base(BaseType::Bool);
        let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
        let fused = fuse_prefix(&chain, &bools).expect("two operations");
        let input = vec![true, false, true];
        assert_eq!(
            fused.program.eval(&ColumnValue::Bools(input.clone())),
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

    /// An element the parse abandons part-way leaves the instructions it emitted past the chosen
    /// prefix, and the program holds none of them, so equal chains give equal programs.
    #[test]
    fn an_abandoned_attempt_leaves_the_same_program() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let plain = vec![zip(vec![id(), constant(1)]), add.clone()];
        let plain = fuse_prefix(&plain, &int()).unwrap().program;
        // A good prefix, then a `zip` whose second arm is not element-wise.
        let abandoned = vec![
            zip(vec![id(), constant(1)]),
            add.clone(),
            zip(vec![
                Expr::compose(vec![zip(vec![id(), constant(9)]), add]),
                Expr::builtin(Builtin::Sum),
            ]),
        ];
        let abandoned = fuse_prefix(&abandoned, &int()).unwrap().program;
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
                bools(fused.program.eval(&ColumnValue::Ints(xs))),
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
        assert_eq!(fused.program.eval(&input), column(|i| 11 * i));
    }

    /// A column of `Bool`s is cut into blocks like any other.
    #[test]
    fn a_bool_column_is_evaluated_block_by_block() {
        let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
        let fused = fuse_prefix(&chain, &Extent::Base(BaseType::Bool)).unwrap();
        let input: Vec<bool> = (0..2 * BLOCK_ROWS + 5).map(|i| i % 3 == 0).collect();
        assert_eq!(
            fused.program.eval(&ColumnValue::Bools(input.clone())),
            ColumnValue::Bools(input)
        );
    }

    /// A slot's buffer is the one its first block allocated: later blocks write into it, so
    /// the evaluation allocates per instruction, not per instruction and block. The output has
    /// no slot: it appends to the result, whose buffer the first block reserved in full.
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
        let mut scratch = Scratch::new(&input, &fused.program);
        let mut out = fused.program.empty_output(&input);
        out.reserve(total);
        scratch.block(&fused.program, 0, BLOCK_ROWS, &mut out);
        let result = pointer(&out);
        let (output, body) = scratch.slots.split_last().unwrap();
        assert!(
            matches!(output, ColumnValue::Units(0)),
            "the output writes to the result, not a slot"
        );
        // An input and a scalar constant are read in place and own no buffer; only an
        // operation's slot holds a column.
        let written = |slot: &ColumnValue| !matches!(slot, ColumnValue::Units(_));
        let buffers: Vec<Option<*const u8>> = body
            .iter()
            .map(|slot| written(slot).then(|| pointer(slot)))
            .collect();
        for (slot, instr) in buffers.iter().zip(&fused.program.instrs) {
            assert_eq!(
                slot.is_some(),
                matches!(instr, Instr::Bin(..) | Instr::Un(..)),
                "{instr}"
            );
        }
        for start in [BLOCK_ROWS, 2 * BLOCK_ROWS] {
            scratch.block(&fused.program, start, BLOCK_ROWS, &mut out);
            let body = &scratch.slots[..buffers.len()];
            for (slot, before) in body.iter().zip(&buffers) {
                assert_eq!(
                    written(slot).then(|| pointer(slot)),
                    *before,
                    "block at {start}"
                );
            }
            assert_eq!(pointer(&out), result, "block at {start}");
        }
        assert_eq!(out.len(), total);
    }

    /// `{name: inner}`.
    fn record_of(name: &str, inner: Extent) -> Extent {
        Extent::Record([(SmolStr::from(name), inner)].into_iter().collect())
    }

    /// A chain of projections alone computes nothing, whatever its length or how it is grouped,
    /// so the prefix ends at an operation and no `Input` is read for nothing.
    #[test]
    fn a_chain_of_projections_alone_is_not_fused() {
        let ab = record_of("a", record_of("b", int()));
        let abc = record_of("a", record_of("b", record_of("c", int())));
        let field = Expr::proj_field;
        assert!(fuse_prefix(&[field("a"), field("b")], &ab).is_none());
        assert!(fuse_prefix(&[field("a"), field("b"), field("c")], &abc).is_none());
        let composed = Expr::compose(vec![field("a"), field("b"), field("c")]);
        assert!(fuse_prefix(&[composed], &abc).is_none());
    }

    /// Equal chains give equal programs: projections read as separate elements and as one
    /// composition, followed by an operation, are one `Input` and the operation, with no
    /// instruction for the intermediate path.
    #[test]
    fn equal_chains_of_projections_give_equal_programs() {
        let abc = record_of("a", record_of("b", record_of("c", int())));
        let field = Expr::proj_field;
        let times_two = || {
            vec![
                zip(vec![id(), constant(2)]),
                binop(BinOpKind::Arithmetic(ArithmeticKind::Mul)),
            ]
        };
        let separate = [vec![field("a"), field("b"), field("c")], times_two()].concat();
        let composed = [
            vec![Expr::compose(vec![field("a"), field("b"), field("c")])],
            times_two(),
        ]
        .concat();
        let separate = fuse_prefix(&separate, &abc).expect("an operation follows the projections");
        let composed = fuse_prefix(&composed, &abc).expect("an operation follows the projections");
        assert_eq!(separate.program, composed.program);
        let inputs = |fused: &Fused| {
            fused
                .program
                .instrs
                .iter()
                .filter(|i| matches!(i, Instr::Input { .. }))
                .count()
        };
        assert_eq!(inputs(&separate), 1, "only the full path is read");
        assert_eq!(
            separate.program.instrs.len(),
            3,
            "the read, the constant, the product"
        );
    }
}
