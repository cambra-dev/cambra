//! Recognize element-wise chains and evaluate them as [`FunctionDef::Scalar`](super::FunctionDef).
//!
//! [`fuse_prefix`] builds the program; [`ScalarProgram::eval`] applies it to a column. The program
//! format and evaluation rules are in `src/interpreter/design-operators.md`, "Scalar programs".
//! Conversion eligibility is in `src/ccl/design/optimization.md`, "Element-wise chains".

use std::collections::HashMap;
use std::mem::replace;
use std::ops::Range;

use smol_str::SmolStr;

use crate::ccl::{Builtin, Expr, FieldKey, ProjKey, TagMap, Type, TypedExprNode};

use crate::view::View;

use super::{
    BaseType, BinOpKind as InterpreterBinOp, ColumnValue, ColumnView, CompareKind, Extent,
    LogicKind, UnaryOpKind, UnionArm, Value, apply_binop_views, apply_unaryop_views,
    binop::compared_fields, binop_output_extent, binop_result_column,
    operator_conversion::expr_to_value, tuple_field, unaryop_result_column,
};

/// The index of an instruction, which is also the slot it writes.
type Slot = u32;

/// The rows an instruction runs on: [`ROOT`], every row of the block, or the rows of the `Arm`
/// whose slot it is ([`Op::Arm`]).
type Scope = Slot;

/// The scope holding every row of the block.
const ROOT: Scope = Slot::MAX;

/// One instruction of a [`ScalarProgram`]: an operation and the scope it runs in. An `Input` and a
/// `Const` are in [`ROOT`]; a constant reads as one value repeated to any scope's length.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Instr {
    scope: Scope,
    op: Op,
}

/// The empty column of a payload's type, which a block whose union column lacks the arm reads.
///
/// `ColumnValue` has no `Hash`, so a shape hashes as nothing; `Eq` still compares it, which keeps
/// equal instructions hashing equally.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Shape(ColumnValue);

impl std::hash::Hash for Shape {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

/// What a [`Op::Arm`] selects the rows of its enclosing scope by.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Gate {
    /// The rows where the `Bool` slot holds.
    Holds(Slot),
    /// The rows whose value in the union slot carries the tag.
    Tag(Slot, FieldKey),
}

/// What an instruction computes. Every slot an operation reads is in the instruction's scope or
/// is a constant ([`ScalarProgram::scopes_are_consistent`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    /// The column at `path` inside the map's input value; an empty path is the value itself. The
    /// column is of a base type or a union. A `Unit` or union column has no view, so no operation
    /// reads one ([`ScalarProgram::operands_have_views`]), and a constructor copies its rows.
    Input {
        path: Vec<SmolStr>,
    },
    /// One value of a base type at every row. A `Unit` constant has no view, so no operation
    /// reads one ([`ScalarProgram::operands_have_views`]).
    Const(Value),
    Bin(InterpreterBinOp, Slot, Slot),
    Un(UnaryOpKind, Slot),
    /// A column of records, one field per slot named, sorted by field name. A tuple's fields are
    /// `_0`, `_1`, …, which sort as strings: `_10` before `_2`.
    ///
    /// A constructor: no operation reads it, and it is the last instruction or a field or payload
    /// of a later constructor ([`ScalarProgram::constructors_build_only_the_result`]).
    Record(Vec<(SmolStr, Slot)>),
    /// A union column whose every row carries `tag`, with the payload in `payload`. The column
    /// holds only that arm, since an absent arm reads as an empty one ([`ColumnValue::Union`]).
    ///
    /// A constructor, as [`Op::Record`] is.
    Wrap {
        tag: FieldKey,
        payload: Slot,
    },
    /// Opens the scope this slot names: the rows of the instruction's scope that `gate` selects.
    /// It is no column, so nothing but a scope's instructions and a `Case` reads it.
    Arm {
        gate: Gate,
    },
    /// In an arm's scope, the rows of `from`, a slot of the enclosing scope, that the arm holds.
    Narrow {
        from: Slot,
    },
    /// In the scope of an arm with a `Tag` gate, the payloads of the rows it holds, at `path`
    /// inside them.
    Payload {
        path: Vec<SmolStr>,
        shape: Shape,
    },
    /// Each row's value from the one arm holding it: `arms` lists each `Arm` slot with the slot of
    /// its result. The arms split the rows of the instruction's scope. A `Case` that `constructs`
    /// is a constructor, as [`Op::Record`] is; one that does not yields a column with a view and
    /// writes a scratch column.
    Case {
        arms: Vec<(Slot, Slot)>,
        constructs: bool,
    },
}

impl Op {
    /// Whether this operation builds part of the result: a [`Op::Record`], a [`Op::Wrap`], or a
    /// [`Op::Case`] that constructs.
    fn is_constructor(&self) -> bool {
        matches!(
            self,
            Op::Record(_)
                | Op::Wrap { .. }
                | Op::Case {
                    constructs: true,
                    ..
                }
        )
    }
}

/// A straight-line program whose operands refer to earlier instruction slots.
///
/// The last instruction produces the result. Structural equality compares instruction sequences;
/// it does not establish equivalence between different expressions for the same function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScalarProgram {
    instrs: Vec<Instr>,
}

/// Rows per block, chosen to keep a kernel's operands and result in L1. Each full 64-bit column
/// occupies 8 KiB, so two operands and a result occupy 24 KiB.
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

/// An arm's rows in the current block.
#[derive(Default)]
struct ArmRows {
    /// The ascending positions, within the enclosing scope's rows, that the arm holds.
    selection: Vec<u32>,
    /// For a `Tag` gate, the slots of the gate's `UnionArm` that hold those rows; empty for a
    /// `Holds` gate or a tag the union column lacks.
    run: Range<usize>,
}

/// Per-evaluation buffers reused across blocks. Inputs and constants are borrowed views.
struct Scratch<'a> {
    input: &'a ColumnValue,
    /// The empty column of each slot's type; `None` for an `Arm`, which is no column.
    empties: Vec<Option<ColumnValue>>,
    /// `Units(0)` marks unwritten slots. An operation, a `Narrow`, a `Case` that does not
    /// construct, and a `Payload` with no view write their block here; the last instruction does
    /// not.
    slots: Vec<ColumnValue>,
    /// The rows of each `Arm` slot in the current block.
    arms: Vec<ArmRows>,
    /// The current block: the rows `start..start + len` of the input.
    start: usize,
    len: usize,
}

impl<'a> Scratch<'a> {
    fn new(input: &'a ColumnValue, program: &ScalarProgram) -> Self {
        let n = program.instrs.len();
        Self {
            input,
            empties: program.empties(input),
            slots: vec![ColumnValue::Units(0); n],
            arms: (0..n).map(|_| ArmRows::default()).collect(),
            start: 0,
            len: 0,
        }
    }

    /// How many rows `scope` holds in the current block.
    fn len_of(&self, scope: Scope) -> usize {
        if scope == ROOT {
            self.len
        } else {
            self.arms[scope as usize].selection.len()
        }
    }

    /// The current block of the union column in `slot`, with the row its block starts at: the
    /// input's column numbers its rows across the whole input, a scratch column from 0.
    fn union_block<'s>(&'s self, program: &ScalarProgram, slot: Slot) -> (&'s ColumnValue, usize) {
        match &program.instrs[slot as usize].op {
            Op::Input { path } => (field(self.input, path), self.start),
            Op::Narrow { .. } | Op::Payload { .. } => (&self.slots[slot as usize], 0),
            op => unreachable!("a union is read from the input or a scratch column, got {op:?}"),
        }
    }

    /// The payload column of the `Tag` arm `scope`, at `path`, for the rows the arm holds in the
    /// current block.
    fn payload<'s>(
        &'s self,
        program: &'s ScalarProgram,
        scope: Scope,
        path: &[SmolStr],
        shape: &'s Shape,
    ) -> (&'s ColumnValue, Range<usize>) {
        let Op::Arm {
            gate: Gate::Tag(union, tag),
        } = &program.instrs[scope as usize].op
        else {
            unreachable!("a payload is read in the scope of a `Tag` arm")
        };
        let (column, _) = self.union_block(program, *union);
        let ColumnValue::Union(arms) = column else {
            unreachable!("a `Tag` gate reads a union column, got {column:?}")
        };
        match arms.get(tag) {
            Some(arm) => (
                field(arm.values(), path),
                self.arms[scope as usize].run.clone(),
            ),
            None => (&shape.0, 0..0),
        }
    }

    /// The block of instruction `slot` as a view, at `len` rows: the length of the scope reading
    /// it, which a constant repeats to.
    fn view<'s>(&'s self, program: &'s ScalarProgram, slot: usize, len: usize) -> ColumnView<'s> {
        let instr = &program.instrs[slot];
        let view = match &instr.op {
            Op::Input { path } => field(self.input, path)
                .view()
                .unwrap_or_else(|| panic!("the input at {path:?} is a column of a base type"))
                .range(self.start..self.start + self.len),
            Op::Const(value) => return const_view(value, len),
            Op::Payload { path, shape } => {
                let (column, run) = self.payload(program, instr.scope, path, shape);
                column
                    .view()
                    .unwrap_or_else(|| panic!("the payload s{slot} is a column of a base type"))
                    .range(run)
            }
            Op::Bin(..) | Op::Un(..) | Op::Narrow { .. } | Op::Case { .. } => self.slots[slot]
                .view()
                .unwrap_or_else(|| panic!("the result s{slot} is a column of a base type")),
            Op::Record(_) | Op::Wrap { .. } | Op::Arm { .. } => {
                unreachable!("no instruction views s{slot}, which is no column with a view")
            }
        };
        debug_assert_eq!(view.len(), len, "s{slot} is read at its own scope's length");
        view
    }

    /// Append the current block of `slot` to `out`, which must have its type, for a reader in
    /// `scope`. A constructor builds its block in place. A `Unit` or union input has no view, so
    /// its block is copied, and so is a column with no view in a scratch slot. A `Unit` constant
    /// adds the scope's rows to a `Units` column.
    fn append(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue, scope: Scope) {
        let instr = &program.instrs[slot];
        let len = self.len_of(scope);
        match &instr.op {
            op if op.is_constructor() => self.run(program, slot, out),
            Op::Input { path } if field(self.input, path).view().is_none() => {
                out.append(field(self.input, path).slice(self.start..self.start + self.len))
            }
            Op::Const(Value::Unit) => out.append(ColumnValue::Units(len)),
            Op::Narrow { .. } | Op::Payload { .. } if !self.has_view(program, slot) => {
                out.append(self.slots[slot].clone())
            }
            _ => out.extend_from_view(self.view(program, slot, len)),
        }
    }

    /// Append the result for `start..start + len` to `out`, prepared by
    /// [`ScalarProgram::empties`]. No instruction reads the last slot, so its result can be
    /// appended directly without a scratch buffer.
    fn block(&mut self, program: &ScalarProgram, start: usize, len: usize, out: &mut ColumnValue) {
        self.start = start;
        self.len = len;
        let last = program.instrs.len() - 1;
        for slot in 0..last {
            self.run_into_slot(program, slot);
        }
        self.run(program, last, out);
    }

    /// Evaluate one instruction for the current block into its scratch slot, or, for an `Arm`, its
    /// rows. Inputs, constants and constructors write nothing.
    fn run_into_slot(&mut self, program: &ScalarProgram, slot: usize) {
        let instr = &program.instrs[slot];
        match &instr.op {
            Op::Arm { gate } => self.arms[slot] = self.select(program, instr.scope, gate),
            Op::Narrow { from } => {
                let column = self.narrow(program, instr.scope, *from);
                self.slots[slot] = column;
            }
            Op::Payload { path, shape } => {
                let (column, run) = self.payload(program, instr.scope, path, shape);
                if column.view().is_none() {
                    let copy = if run.is_empty() {
                        column.empty_like()
                    } else {
                        column.slice(run)
                    };
                    self.slots[slot] = copy;
                }
            }
            Op::Bin(..)
            | Op::Un(..)
            | Op::Case {
                constructs: false, ..
            } => {
                let mut column = self.slot_column(slot);
                self.run(program, slot, &mut column);
                self.slots[slot] = column;
            }
            Op::Input { .. } | Op::Const(_) | Op::Record(_) | Op::Wrap { .. } | Op::Case { .. } => {
            }
        }
    }

    /// The rows of the enclosing scope `scope` that `gate` selects in the current block.
    fn select(&self, program: &ScalarProgram, scope: Scope, gate: &Gate) -> ArmRows {
        let len = self.len_of(scope);
        match gate {
            Gate::Holds(slot) => {
                let ColumnView::Bools(holds) = self.view(program, *slot as usize, len) else {
                    unreachable!("a `Holds` gate reads a `Bool` column")
                };
                let selection = (0..len)
                    .filter(|&p| *holds.get(p))
                    .map(|p| p as u32)
                    .collect();
                ArmRows {
                    selection,
                    run: 0..0,
                }
            }
            // The arm's rows are ascending, so those in the block are one run of them.
            Gate::Tag(union, tag) => {
                let (column, offset) = self.union_block(program, *union);
                let ColumnValue::Union(arms) = column else {
                    unreachable!("a `Tag` gate reads a union column, got {column:?}")
                };
                let Some(arm) = arms.get(tag) else {
                    return ArmRows::default();
                };
                let rows = arm.rows();
                let run = rows.partition_point(|&r| r < offset)
                    ..rows.partition_point(|&r| r < offset + len);
                let selection = rows[run.clone()]
                    .iter()
                    .map(|&r| (r - offset) as u32)
                    .collect();
                ArmRows { selection, run }
            }
        }
    }

    /// Whether `slot` reads as a view in the current block: an operation, a `Case` that does not
    /// construct, or an input, `Narrow` or `Payload` of a base type other than `Unit`.
    fn has_view(&self, program: &ScalarProgram, slot: usize) -> bool {
        let instr = &program.instrs[slot];
        match &instr.op {
            Op::Input { path } => field(self.input, path).view().is_some(),
            Op::Const(value) => !matches!(value, Value::Unit),
            Op::Bin(..)
            | Op::Un(..)
            | Op::Case {
                constructs: false, ..
            } => true,
            Op::Narrow { .. } => self.slots[slot].view().is_some(),
            Op::Payload { path, shape } => self
                .payload(program, instr.scope, path, shape)
                .0
                .view()
                .is_some(),
            Op::Record(_) | Op::Wrap { .. } | Op::Arm { .. } | Op::Case { .. } => false,
        }
    }

    /// The rows of `from`, a slot of the scope enclosing the arm `scope`, that the arm holds.
    fn narrow(&self, program: &ScalarProgram, scope: Scope, from: Slot) -> ColumnValue {
        let selection = &self.arms[scope as usize].selection;
        let enclosing = program.instrs[scope as usize].scope;
        if self.has_view(program, from as usize) {
            let len = self.len_of(enclosing);
            return self.view(program, from as usize, len).gather(selection);
        }
        let (column, offset) = match &program.instrs[from as usize].op {
            Op::Input { path } => (field(self.input, path), self.start),
            _ => (&self.slots[from as usize], 0),
        };
        column.select_indices(
            selection.iter().map(|&p| offset + p as usize),
            selection.len(),
        )
    }

    /// The column an operation writes its block into: its slot's buffer, cleared, or on the first
    /// block a new empty column of the operation's result type.
    fn slot_column(&mut self, slot: usize) -> ColumnValue {
        let mut column = take(&mut self.slots[slot]);
        if !matches!(column, ColumnValue::Units(_)) {
            column.clear();
            return column;
        }
        self.empties[slot]
            .clone()
            .expect("an operation's result is a column")
    }

    /// Append an operation or constructor's current block to `out`, which must have its result
    /// type. Nested constructors are built recursively because they have no scratch columns.
    fn run(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        let instr = &program.instrs[slot];
        let len = self.len_of(instr.scope);
        match &instr.op {
            Op::Un(op, a) => apply_unaryop_views(*op, &self.view(program, *a as usize, len), out),
            Op::Bin(op, a, b) => {
                let (a, b) = (
                    self.view(program, *a as usize, len),
                    self.view(program, *b as usize, len),
                );
                apply_binop_views(*op, &a, &b, out);
            }
            Op::Record(fields) => {
                let ColumnValue::Records(columns) = out else {
                    panic!("a record is appended to a record column, got {out:?}")
                };
                for (name, field) in fields {
                    let column = columns
                        .get_mut(name)
                        .unwrap_or_else(|| panic!("the result has a column for the field {name}"));
                    self.append(program, *field as usize, column, instr.scope);
                }
            }
            Op::Wrap { tag, payload } => {
                let rows = out.len()..out.len() + len;
                let ColumnValue::Union(arms) = out else {
                    panic!("a wrap is appended to a union column, got {out:?}")
                };
                let arm = arms
                    .get_mut(tag)
                    .unwrap_or_else(|| panic!("the result has an arm for the tag {tag}"));
                // Every row the wrap builds carries this one arm, so its rows follow the rows the
                // column already holds.
                arm.extend_rows(rows, |values| {
                    self.append(program, *payload as usize, values, instr.scope)
                });
            }
            Op::Case {
                arms,
                constructs: false,
            } => {
                let parts: Vec<_> = arms
                    .iter()
                    .map(|&(arm, result)| {
                        let selection = &self.arms[arm as usize].selection;
                        let view = self.view(program, result as usize, selection.len());
                        (view, selection.as_slice())
                    })
                    .collect();
                ColumnView::scatter_into(&parts, len, out);
            }
            Op::Case {
                arms,
                constructs: true,
            } => {
                let parts = arms
                    .iter()
                    .map(|&(arm, result)| {
                        let mut part = self.empties[result as usize]
                            .clone()
                            .expect("an arm's result is a column");
                        self.append(program, result as usize, &mut part, arm);
                        (part, self.arms[arm as usize].selection.as_slice())
                    })
                    .collect();
                out.append(merge_parts(parts, len));
            }
            Op::Input { .. }
            | Op::Const(_)
            | Op::Arm { .. }
            | Op::Narrow { .. }
            | Op::Payload { .. } => {
                unreachable!(
                    "s{slot} runs only as an operation, the last instruction or a field or \
                     payload that is a constructor, and the last instruction is an operation or a \
                     constructor"
                )
            }
        }
    }
}

/// One arm of a merged union column: its tag, the parts' payloads for it concatenated, and each
/// row's position in the merged column with its index in those payloads.
type MergedArm = (FieldKey, ColumnValue, Vec<(u32, usize)>);

/// One column of `len` rows from `parts`: the row at position `p` is the next row of the one part
/// whose positions hold `p`. The parts' positions are ascending and together hold each of `0..len`
/// once. A record merges field by field, and a union arm by arm, each row keeping its tag.
fn merge_parts(parts: Vec<(ColumnValue, &[u32])>, len: usize) -> ColumnValue {
    let first = &parts.first().expect("a `Case` has an arm").0;
    if first.view().is_some() {
        let mut out = first.empty_like();
        let views: Vec<_> = parts
            .iter()
            .map(|(column, positions)| (column.view().expect("parts of one type"), *positions))
            .collect();
        ColumnView::scatter_into(&views, len, &mut out);
        return out;
    }
    match first {
        ColumnValue::Units(_) => ColumnValue::Units(len),
        ColumnValue::Records(fields) => {
            let names: Vec<SmolStr> = fields.keys().cloned().collect();
            let mut parts = parts;
            ColumnValue::Records(
                names
                    .into_iter()
                    .map(|name| {
                        let field_parts = parts
                            .iter_mut()
                            .map(|(column, positions)| {
                                let ColumnValue::Records(fields) = column else {
                                    panic!("parts of one type")
                                };
                                let field = fields.remove(&name).expect("parts of one type");
                                (field, *positions)
                            })
                            .collect();
                        (name, merge_parts(field_parts, len))
                    })
                    .collect(),
            )
        }
        ColumnValue::Union(_) => {
            // Each part's union rows are numbered within the part; a row's position in the
            // merged column is the part's position for it. An arm's payloads are the parts'
            // payloads for that tag, concatenated and then taken in position order.
            let mut by_tag: Vec<MergedArm> = Vec::new();
            for (column, positions) in parts {
                let ColumnValue::Union(arms) = column else {
                    panic!("parts of one type")
                };
                for (tag, arm) in arms {
                    let i = match by_tag.iter().position(|(t, ..)| *t == tag) {
                        Some(i) => i,
                        None => {
                            by_tag.push((tag, arm.values().empty_like(), Vec::new()));
                            by_tag.len() - 1
                        }
                    };
                    let (_, values, rows) = &mut by_tag[i];
                    let base = values.len();
                    rows.extend(
                        arm.rows()
                            .iter()
                            .enumerate()
                            .map(|(slot, &row)| (positions[row], base + slot)),
                    );
                    values.append(arm.values().clone());
                }
            }
            ColumnValue::Union(TagMap::from_arms(
                by_tag
                    .into_iter()
                    .map(|(tag, values, mut rows)| {
                        rows.sort_unstable_by_key(|(position, _)| *position);
                        let values =
                            values.select_indices(rows.iter().map(|(_, i)| *i), rows.len());
                        let rows = rows.iter().map(|(p, _)| *p as usize).collect();
                        (tag, UnionArm::new(rows, values))
                    })
                    .collect(),
            ))
        }
        other => panic!("a `Case` merges columns of base types, records and unions, got {other:?}"),
    }
}

/// The column in `slot`, leaving the unwritten marker behind.
fn take(slot: &mut ColumnValue) -> ColumnValue {
    replace(slot, ColumnValue::Units(0))
}

impl ScalarProgram {
    /// Return one result row per input row, evaluating in blocks of [`BLOCK_ROWS`].
    ///
    /// Reserve the output for all input rows before evaluation. Intermediate operations retain
    /// only one block each; inputs and constants are read through borrowed views.
    pub fn eval(&self, input: &ColumnValue) -> ColumnValue {
        let len = input.len();
        let mut scratch = Scratch::new(input, self);
        let mut out = scratch
            .empties
            .last()
            .cloned()
            .flatten()
            .expect("a program's result is a column");
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
        out.debug_assert_union_invariants();
        out
    }

    /// The empty column of each slot's type, found from the input's columns and the instructions'
    /// types without evaluating any block; `None` for an `Arm`, which is no column.
    fn empties(&self, input: &ColumnValue) -> Vec<Option<ColumnValue>> {
        let mut empties: Vec<Option<ColumnValue>> = Vec::with_capacity(self.instrs.len());
        for instr in &self.instrs {
            let of = |slot: &Slot| -> ColumnValue {
                empties[*slot as usize]
                    .clone()
                    .expect("an operand is a column")
            };
            let empty = match &instr.op {
                Op::Input { path } => field(input, path).empty_like(),
                Op::Const(value) => ColumnValue::single(value.clone()).empty_like(),
                Op::Un(op, a) => {
                    let operand = of(a);
                    let operand = operand
                        .view()
                        .expect("an operand is a column of a base type");
                    unaryop_result_column(*op, &operand)
                }
                Op::Bin(op, a, _) => {
                    let operand = of(a);
                    let operand = operand
                        .view()
                        .expect("an operand is a column of a base type");
                    binop_result_column(*op, &operand)
                }
                Op::Record(fields) => ColumnValue::Records(
                    fields
                        .iter()
                        .map(|(name, field)| (name.clone(), of(field)))
                        .collect(),
                ),
                Op::Wrap { tag, payload } => ColumnValue::Union(TagMap::from_arms(vec![(
                    tag.clone(),
                    UnionArm::new(Vec::new(), of(payload)),
                )])),
                Op::Arm { .. } => {
                    empties.push(None);
                    continue;
                }
                Op::Narrow { from } => of(from),
                Op::Payload { shape, .. } => shape.0.clone(),
                // A union `Case` holds each arm's tags, so the arms' empty columns are appended.
                Op::Case { arms, .. } => {
                    let mut arms = arms.iter().map(|(_, result)| of(result));
                    let mut empty = arms.next().expect("a `Case` has an arm");
                    arms.for_each(|arm| empty.append(arm));
                    empty
                }
            };
            empties.push(Some(empty));
        }
        empties
    }

    /// Check that constructors are used only to build the result, never as operation operands:
    /// each is the last instruction or a field, payload or arm result of a later constructor. The
    /// last instruction must be an operation or a constructor, not a borrowed input, constant,
    /// arm, narrowed column or payload.
    fn constructors_build_only_the_result(&self) -> bool {
        let is_constructor = |slot: &Slot| self.instrs[*slot as usize].op.is_constructor();
        let last = self.instrs.len() - 1;
        let result_is_built = matches!(
            self.instrs[last].op,
            Op::Bin(..) | Op::Un(..) | Op::Record(_) | Op::Wrap { .. } | Op::Case { .. }
        );
        let builds = |later: &Op, slot: usize| match later {
            Op::Record(fields) => fields.iter().any(|(_, field)| *field as usize == slot),
            Op::Wrap { payload, .. } => *payload as usize == slot,
            Op::Case {
                arms,
                constructs: true,
            } => arms.iter().any(|(_, result)| *result as usize == slot),
            _ => false,
        };
        result_is_built
            && self
                .instrs
                .iter()
                .enumerate()
                .all(|(slot, instr)| match &instr.op {
                    Op::Bin(_, a, b) => !is_constructor(a) && !is_constructor(b),
                    Op::Un(_, a) => !is_constructor(a),
                    Op::Case {
                        arms,
                        constructs: false,
                    } => arms.iter().all(|(_, result)| !is_constructor(result)),
                    Op::Narrow { from } => !is_constructor(from),
                    Op::Arm {
                        gate: Gate::Holds(b) | Gate::Tag(b, _),
                    } => !is_constructor(b),
                    op if op.is_constructor() => {
                        slot == last
                            || self.instrs[slot + 1..]
                                .iter()
                                .any(|later| builds(&later.op, slot))
                    }
                    _ => true,
                })
    }

    /// Check that every operand of an operation has a view, for a program applied to values of
    /// `input`. An operand has a view when it is an operation, a `Case` that does not construct,
    /// or an input, constant, `Narrow` or `Payload` whose column has one ([`has_view`]). A
    /// constructor, an `Arm`, a `Unit` constant, and a `Unit` or union column have none. A `Holds`
    /// gate and the arm results of a `Case` that does not construct are operands too.
    fn operands_have_views(&self, input: &Extent) -> bool {
        fn has_a_view(program: &ScalarProgram, input: &Extent, slot: Slot) -> bool {
            match &program.instrs[slot as usize].op {
                Op::Input { path } => path
                    .iter()
                    .try_fold(input, |extent, name| extent.record_fields()?.get(name))
                    .is_some_and(has_view),
                Op::Const(value) => value_extent(value).as_ref().is_some_and(has_view),
                Op::Bin(..)
                | Op::Un(..)
                | Op::Case {
                    constructs: false, ..
                } => true,
                Op::Narrow { from } => has_a_view(program, input, *from),
                Op::Payload { shape, .. } => shape.0.view().is_some(),
                Op::Record(_) | Op::Wrap { .. } | Op::Arm { .. } | Op::Case { .. } => false,
            }
        }
        let has = |slot: &Slot| has_a_view(self, input, *slot);
        self.instrs.iter().all(|instr| match &instr.op {
            Op::Bin(_, a, b) => has(a) && has(b),
            Op::Un(_, a) => has(a),
            Op::Arm {
                gate: Gate::Holds(b),
            } => has(b),
            Op::Case {
                arms,
                constructs: false,
            } => arms.iter().all(|(_, result)| has(result)),
            _ => true,
        })
    }

    /// Check that every instruction reads slots of its own scope or constants, and that scopes
    /// nest: an `Arm`'s gate is in the arm's enclosing scope, a `Narrow` reads its arm's
    /// enclosing scope, a `Payload` is in a `Tag` arm, a `Case`'s arms open inside its scope and
    /// each result is in its arm, and the result is in [`ROOT`].
    fn scopes_are_consistent(&self) -> bool {
        let scope_of = |slot: &Slot| self.instrs[*slot as usize].scope;
        let is_const = |slot: &Slot| matches!(self.instrs[*slot as usize].op, Op::Const(_));
        let reads_in = |slot: &Slot, scope: Scope| is_const(slot) || scope_of(slot) == scope;
        let is_arm = |slot: Slot| matches!(self.instrs[slot as usize].op, Op::Arm { .. });
        self.instrs.last().is_some_and(|last| last.scope == ROOT)
            && self.instrs.iter().enumerate().all(|(slot, instr)| {
                let scope = instr.scope;
                let opens = |arm: Slot| arm == ROOT || (arm as usize) < slot && is_arm(arm);
                opens(scope)
                    && match &instr.op {
                        Op::Input { .. } | Op::Const(_) => scope == ROOT,
                        Op::Bin(_, a, b) => reads_in(a, scope) && reads_in(b, scope),
                        Op::Un(_, a) => reads_in(a, scope),
                        Op::Record(fields) => fields.iter().all(|(_, f)| reads_in(f, scope)),
                        Op::Wrap { payload, .. } => reads_in(payload, scope),
                        Op::Arm {
                            gate: Gate::Holds(b),
                        } => reads_in(b, scope),
                        // A union is read from the input or from a scratch column of this scope.
                        Op::Arm {
                            gate: Gate::Tag(u, _),
                        } => {
                            scope_of(u) == scope
                                && matches!(
                                    self.instrs[*u as usize].op,
                                    Op::Input { .. } | Op::Narrow { .. } | Op::Payload { .. }
                                )
                        }
                        Op::Narrow { from } => {
                            scope != ROOT
                                && !is_const(from)
                                && scope_of(from) == self.instrs[scope as usize].scope
                        }
                        Op::Payload { .. } => {
                            scope != ROOT
                                && matches!(
                                    self.instrs[scope as usize].op,
                                    Op::Arm {
                                        gate: Gate::Tag(..)
                                    }
                                )
                        }
                        Op::Case { arms, .. } => arms.iter().all(|&(arm, result)| {
                            is_arm(arm)
                                && self.instrs[arm as usize].scope == scope
                                && reads_in(&result, arm)
                        }),
                    }
            })
    }
}

impl std::fmt::Display for Instr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.op {
            Op::Input { path } if path.is_empty() => write!(f, "_"),
            Op::Input { path } => write!(f, "_.{}", path.join(".")),
            Op::Const(value) => write!(f, "{value}"),
            Op::Un(op, a) => write!(f, "{op:?}(s{a})"),
            Op::Bin(op, a, b) => {
                write!(f, "{}(s{a}, s{b})", crate::pretty_graph::fmt_binop(op))
            }
            Op::Record(fields) => {
                write!(f, "(")?;
                for (i, (name, field)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: s{field}")?;
                }
                write!(f, ")")
            }
            Op::Wrap { tag, payload } => write!(f, "`{tag}(s{payload})"),
            Op::Arm {
                gate: Gate::Holds(b),
            } => write!(f, "arm s{b}"),
            Op::Arm {
                gate: Gate::Tag(u, tag),
            } => write!(f, "arm s{u} is `{tag}"),
            Op::Narrow { from } => write!(f, "narrow s{from}"),
            Op::Payload { path, .. } if path.is_empty() => write!(f, "payload"),
            Op::Payload { path, .. } => write!(f, "payload.{}", path.join(".")),
            Op::Case { arms, .. } => {
                write!(f, "case(")?;
                for (i, (arm, result)) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "s{arm}: s{result}")?;
                }
                write!(f, ")")
            }
        }?;
        if self.scope != ROOT {
            write!(f, " in s{}", self.scope)?;
        }
        Ok(())
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

/// A value during recognition. Products retain their fields without emitting record instructions;
/// operations read individual fields, and [`Parser::output`] materializes result records.
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
    /// The arms of a `zip` of a tuple, which a binary operation takes its operands from.
    Tuple(Vec<Val>),
    /// The arms of a `zip` of a record, by name.
    Record(Vec<(SmolStr, Val)>),
    /// The payload of a variant at `tag`, with the extent of the whole union: what a
    /// `variant_wrap` builds, or a variant constant. Only [`Parser::output`] reads it.
    Wrap(FieldKey, Box<Val>, Extent),
    /// In the scope of a `Tag` arm, the payloads of the rows it holds, or a field path into them,
    /// not yet read into a slot, with the extent of their values.
    Payload(Slot, Vec<SmolStr>, Extent),
    /// A `Case` that constructs, with its extent. Only [`Parser::output`] reads it.
    Built(Slot, Extent),
}

/// The union slot a `Tag` gate reads, with the tags of its extent.
type Scrutinee = (Slot, Vec<FieldKey>);

/// What a `DisjointJoin` operand's gate opens ([`Parser::gate`]).
enum Opened {
    /// An `Arm` slot, and the value its operand's chain continues from.
    Arm(Slot, Val),
    /// A `variant_project` of a variant built in the chain, whose tag is known: the payload when
    /// the tag is the one projected, and `None` when the operand holds no row.
    Known(Option<Val>),
}

/// The most search nodes [`gates_split_the_rows`] visits before it gives up on a conditional, a
/// compile-time budget: a conditional whose proof needs more is not fused.
const SPLIT_BUDGET: usize = 4096;

/// One node of [`Formulas`]. A node's operands come before it.
enum Node {
    /// A `Bool` slot no `and`, `or` or `not` produces; the node stands for one slot.
    Atom,
    Known(bool),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
}

/// Gates as formulas over atoms, held as one graph: a formula two gates share, or that one gate
/// reads twice, is one node.
#[derive(Default)]
struct Formulas {
    nodes: Vec<Node>,
}

impl Formulas {
    fn push(&mut self, node: Node) -> usize {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    /// Every node's value under `assignment`, which assigns atom nodes, in three-valued logic:
    /// `None` while a node depends on an atom `assignment` does not assign.
    fn values(&self, assignment: &[Option<bool>]) -> Vec<Option<bool>> {
        let mut values: Vec<Option<bool>> = Vec::with_capacity(self.nodes.len());
        for (i, node) in self.nodes.iter().enumerate() {
            let value = match *node {
                Node::Atom => assignment[i],
                Node::Known(value) => Some(value),
                Node::Not(a) => values[a].map(|value| !value),
                Node::And(a, b) => match (values[a], values[b]) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
                Node::Or(a, b) => match (values[a], values[b]) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
            };
            values.push(value);
        }
        values
    }

    /// An atom node that `gate` reads and `values` leaves undecided.
    fn undecided_atom(&self, gate: usize, values: &[Option<bool>]) -> Option<usize> {
        if values[gate].is_some() {
            return None;
        }
        match self.nodes[gate] {
            Node::Atom => Some(gate),
            Node::Known(_) => None,
            Node::Not(a) => self.undecided_atom(a, values),
            Node::And(a, b) | Node::Or(a, b) => self
                .undecided_atom(a, values)
                .or_else(|| self.undecided_atom(b, values)),
        }
    }
}

/// Whether every row is held by exactly one of `gates`, nodes of `formulas`: every assignment of
/// truth values to their atoms makes exactly one gate true. Atoms are assigned one at a time, and
/// a branch ends once every gate is decided. It fails once two gates are true or every gate is
/// false, and gives up after visiting [`SPLIT_BUDGET`] search nodes.
fn gates_split_the_rows(formulas: &Formulas, gates: &[usize]) -> bool {
    fn search(
        formulas: &Formulas,
        gates: &[usize],
        assignment: &mut Vec<Option<bool>>,
        budget: &mut usize,
    ) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        let values = formulas.values(assignment);
        let holding = gates.iter().filter(|&&g| values[g] == Some(true)).count();
        if holding > 1 || gates.iter().all(|&g| values[g] == Some(false)) {
            return false;
        }
        let Some(atom) = gates
            .iter()
            .find_map(|&g| formulas.undecided_atom(g, &values))
        else {
            return true;
        };
        [true, false].into_iter().all(|value| {
            assignment[atom] = Some(value);
            let split = search(formulas, gates, assignment, budget);
            assignment[atom] = None;
            split
        })
    }
    let mut budget = SPLIT_BUDGET;
    let mut assignment = vec![None; formulas.nodes.len()];
    search(formulas, gates, &mut assignment, &mut budget)
}

/// The value of an `==` or `!=` comparison as [`Parser::comparison`] reads it.
enum Comparison {
    /// A column of `Bool`s in this slot.
    Computed(Slot),
    /// The same answer at every row, known while parsing.
    Decided(bool),
}

struct Parser<'t> {
    /// The scope the next instruction runs in: [`ROOT`], or the `Arm` whose operand is parsed.
    scope: Scope,
    /// The extent of a type, as operator conversion reads it. The parser reads a union's arms
    /// from it, since the payload of a `variant_wrap` or of a variant constant names only its own
    /// arm.
    extent_of: &'t dyn Fn(&Type) -> Option<Extent>,
    /// The instructions emitted so far. Instructions are appended, and removed only by
    /// [`Parser::truncate`].
    instrs: Vec<Instr>,
    /// The slot of each instruction emitted so far other than a constructor, so an equal
    /// instruction is one slot: a path read twice, a constant written twice, or an operation on
    /// the same slots computed twice ([`Parser::emit`]).
    slots: HashMap<Instr, Slot>,
    /// How many operations the chain read so far. The identity and a composition of others count
    /// as none, a `zip` as two whatever its arity, and every other element as one. A prefix is
    /// taken only when it reads two or more ([`fuse_prefix`]), so a `zip` alone is taken.
    ops: usize,
}

impl Parser<'_> {
    /// The slot of `op` in the current scope, or in [`ROOT`] for an `Input` or a `Const`.
    fn emit(&mut self, op: Op) -> Slot {
        let scope = match op {
            Op::Input { .. } | Op::Const(_) => ROOT,
            _ => self.scope,
        };
        self.emit_in(scope, op)
    }

    /// The slot of `op` in `scope`: an equal instruction's slot when one was emitted, or a new one.
    /// An instruction's value is a function of its scope, its fields and the slots it reads, so
    /// equal instructions compute equal columns. Constructors are always new, since each is read by
    /// the one constructor it is a field or payload of
    /// ([`ScalarProgram::constructors_build_only_the_result`]).
    fn emit_in(&mut self, scope: Scope, op: Op) -> Slot {
        let instr = Instr { scope, op };
        if let Some(&slot) = self.slots.get(&instr) {
            return slot;
        }
        let slot = self.instrs.len() as Slot;
        if !instr.op.is_constructor() {
            self.slots.insert(instr.clone(), slot);
        }
        self.instrs.push(instr);
        slot
    }

    /// `slot` read in the current scope: narrowed through each arm between its own scope and the
    /// current one, which must lie inside it. A constant reads in any scope.
    fn narrowed(&mut self, slot: Slot) -> Option<Slot> {
        let home = self.instrs[slot as usize].scope;
        if matches!(self.instrs[slot as usize].op, Op::Const(_)) || home == self.scope {
            return Some(slot);
        }
        let mut arms = Vec::new();
        let mut scope = self.scope;
        while scope != home {
            if scope == ROOT {
                return None;
            }
            arms.push(scope);
            scope = self.instrs[scope as usize].scope;
        }
        Some(
            arms.into_iter()
                .rev()
                .fold(slot, |from, arm| self.emit_in(arm, Op::Narrow { from })),
        )
    }

    /// The `Payload` instruction reading `path` in the `Tag` arm `arm`, whose values have `extent`.
    fn payload(&mut self, arm: Slot, path: &[SmolStr], extent: &Extent) -> Slot {
        let shape = Shape(ColumnValue::from_values(Vec::new(), extent));
        let path = path.to_vec();
        self.emit_in(arm, Op::Payload { path, shape })
    }

    /// Discard instructions from `len` onward, with their entries in [`Parser::slots`]. Keep the
    /// operation count: probing an output must not undo the count accumulated by
    /// [`Parser::step`].
    fn truncate(&mut self, len: usize) {
        self.instrs.truncate(len);
        self.slots.retain(|_, slot| (*slot as usize) < len);
    }

    /// Return a scalar slot, emitting an input or constant instruction when needed. Records and
    /// tuples have no scalar slot. Repeated reads of one input path share an instruction.
    fn column(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        let slot = match v {
            Val::Slot(slot, _) => *slot,
            Val::Read(path, extent) if has_view(extent) => self.input(path),
            Val::Const(value, extent) if has_view(extent) => self.emit(Op::Const(value.clone())),
            Val::Payload(arm, path, extent) if has_view(extent) => self.payload(*arm, path, extent),
            _ => return None,
        };
        let extent = match v {
            Val::Slot(_, e) | Val::Read(_, e) | Val::Const(_, e) | Val::Payload(_, _, e) => e,
            _ => unreachable!("matched above"),
        };
        Some((self.narrowed(slot)?, extent.clone()))
    }

    /// The `Input` instruction reading `path`.
    fn input(&mut self, path: &[SmolStr]) -> Slot {
        self.emit(Op::Input {
            path: path.to_vec(),
        })
    }

    /// An input or constant with no view as a slot: a `Unit` one, or a union read from the input.
    /// Only a constructor reads the slot, copying its rows.
    fn copied(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        let (slot, extent) = match v {
            Val::Read(path, extent @ (Extent::Base(BaseType::Unit) | Extent::Union(_))) => {
                (self.input(path), extent)
            }
            Val::Payload(arm, path, extent @ (Extent::Base(BaseType::Unit) | Extent::Union(_))) => {
                (self.payload(*arm, path, extent), extent)
            }
            Val::Const(value @ Value::Unit, extent) => {
                (self.emit(Op::Const(value.clone())), extent)
            }
            _ => return None,
        };
        Some((self.narrowed(slot)?, extent.clone()))
    }

    /// `value` at every position, with `extent` the extent of its values. A variant constant is
    /// the [`Val::Wrap`] of its payload, so it builds a column as a `variant_wrap` does. A variant
    /// has no value here when its extent is not a [plain](is_plain) union holding its tag.
    fn constant(value: Value, extent: Extent) -> Option<Val> {
        match value {
            Value::Union { tag, inner } => {
                let Extent::Union(arms) = &extent else {
                    return None;
                };
                if !is_plain(&extent) {
                    return None;
                }
                let payload = Self::constant(*inner, arms.get(&tag)?.clone())?;
                Some(Val::Wrap(tag, Box::new(payload), extent))
            }
            value => Some(Val::Const(value, extent)),
        }
    }

    /// The fields of a record `v`, each as the value of that field: the arms of a product built in
    /// the chain, a tuple's by [`tuple_field`] name, and the fields of a record read from the input
    /// or held as a constant. A value that is not a record has none.
    fn fields_of(v: &Val) -> Option<HashMap<SmolStr, Val>> {
        match v {
            Val::Tuple(items) => Some(
                items
                    .iter()
                    .enumerate()
                    .map(|(i, item)| (tuple_field(i), item.clone()))
                    .collect(),
            ),
            Val::Record(arms) => Some(arms.iter().cloned().collect()),
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
            Val::Payload(arm, path, extent) => Some(
                extent
                    .record_fields()?
                    .iter()
                    .map(|(name, field)| {
                        let mut path = path.clone();
                        path.push(name.clone());
                        (name.clone(), Val::Payload(*arm, path, field.clone()))
                    })
                    .collect(),
            ),
            Val::Const(Value::Record(values), extent) => {
                let extents = extent.record_fields()?;
                values
                    .iter()
                    .map(|(name, value)| {
                        let field = Self::constant(value.clone(), extents.get(name)?.clone())?;
                        Some((name.clone(), field))
                    })
                    .collect()
            }
            _ => None,
        }
    }

    /// `a op b` for a binary operation. `==` and `!=` read as [`Parser::comparison`] reads them. A
    /// comparison decided while parsing computes no column, so it has no program here.
    fn operation(&mut self, op: InterpreterBinOp, a: &Val, b: &Val) -> Option<(Slot, Extent)> {
        let InterpreterBinOp::Compare(kind @ (CompareKind::Equals | CompareKind::NotEquals)) = op
        else {
            let ((a, _), (b, _)) = (self.column(a)?, self.column(b)?);
            return Some((self.emit(Op::Bin(op, a, b)), binop_output_extent(&op)));
        };
        match self.comparison(kind, a, b)? {
            Comparison::Computed(slot) => Some((slot, binop_output_extent(&op))),
            Comparison::Decided(_) => None,
        }
    }

    /// `a == b` or `a != b`, as `kind` names, by the rules `apply_binop_into` evaluates it by:
    ///
    /// - Two `unit` values are equal at every row.
    /// - Two variants of one tag compare their payloads, and two of different tags differ at every
    ///   row.
    /// - Two records compare field by field over the fields [`compared_fields`] names: `==` is the
    ///   conjunction of the fields' comparisons and `!=` their disjunction. A field decided while
    ///   parsing drops out of the join when its answer is the join's identity, `true` under `and`
    ///   and `false` under `or`. Any other decided field decides the whole comparison.
    ///
    /// A record's fields are the ones its extent names, inside a variant's payload as at the top
    /// level. A record against anything but a record, a variant against anything but a variant, a
    /// union read from the input, and two records sharing no field have no program.
    fn comparison(&mut self, kind: CompareKind, a: &Val, b: &Val) -> Option<Comparison> {
        let equals = kind == CompareKind::Equals;
        let is_unit = |v: &Val| {
            matches!(
                v,
                Val::Read(_, Extent::Base(BaseType::Unit))
                    | Val::Payload(_, _, Extent::Base(BaseType::Unit))
                    | Val::Const(Value::Unit, _)
            )
        };
        if is_unit(a) && is_unit(b) {
            return Some(Comparison::Decided(equals));
        }
        if let (Val::Wrap(a_tag, a, _), Val::Wrap(b_tag, b, _)) = (a, b) {
            if a_tag != b_tag {
                return Some(Comparison::Decided(!equals));
            }
            return self.comparison(kind, a, b);
        }
        let (left, right) = match (Self::fields_of(a), Self::fields_of(b)) {
            (None, None) => {
                let ((a, _), (b, _)) = (self.column(a)?, self.column(b)?);
                let op = InterpreterBinOp::Compare(kind);
                return Some(Comparison::Computed(self.emit(Op::Bin(op, a, b))));
            }
            (Some(left), Some(right)) => (left, right),
            _ => return None,
        };
        let join = InterpreterBinOp::BoolLogic(if equals {
            LogicKind::And
        } else {
            LogicKind::Or
        });
        // In name order, so that equal chains give equal programs.
        let mut fields: Vec<_> = compared_fields(&left, &right).collect();
        if fields.is_empty() {
            return None;
        }
        fields.sort_by_key(|(name, ..)| *name);
        let start = self.instrs.len();
        let mut joined: Option<Slot> = None;
        for (_, l, r) in fields {
            match self.comparison(kind, l, r)? {
                Comparison::Decided(answer) if answer == equals => {}
                Comparison::Decided(answer) => {
                    // The answer reads no column the earlier fields computed, and no value outside
                    // this comparison holds a slot emitted after `start`.
                    self.truncate(start);
                    return Some(Comparison::Decided(answer));
                }
                Comparison::Computed(slot) => {
                    joined = Some(match joined {
                        None => slot,
                        Some(prev) => self.emit(Op::Bin(join, prev, slot)),
                    });
                }
            }
        }
        Some(joined.map_or(Comparison::Decided(equals), Comparison::Computed))
    }

    /// Extend an input field path. Projections of computed products are not recognized here;
    /// any such projection left after simplification ends the prefix.
    fn project(v: Val, key: &ProjKey) -> Option<Val> {
        let name = match key {
            ProjKey::Index(i) => tuple_field(*i),
            ProjKey::Field(name) => name.runtime_key(),
        };
        match v {
            Val::Read(mut path, extent) => {
                let field = extent.record_fields()?.get(&name)?.clone();
                path.push(name);
                Some(Val::Read(path, field))
            }
            Val::Payload(arm, mut path, extent) => {
                let field = extent.record_fields()?.get(&name)?.clone();
                path.push(name);
                Some(Val::Payload(arm, path, field))
            }
            _ => None,
        }
    }

    /// Read `e` as a function applied to `cur`.
    fn step(&mut self, e: &Expr, cur: Val) -> Option<Val> {
        self.ops += match &e.node {
            TypedExprNode::Compose(_) | TypedExprNode::Builtin(Builtin::Id) => 0,
            TypedExprNode::Apply { function, .. }
                if matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)) =>
            {
                2
            }
            _ => 1,
        };
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
            TypedExprNode::Builtin(b @ (Builtin::Neg | Builtin::NotFn | Builtin::IntToUint)) => {
                let (a, operand) = self.column(&cur)?;
                let op = match b {
                    Builtin::Neg => UnaryOpKind::Neg,
                    Builtin::NotFn => UnaryOpKind::Not,
                    _ => UnaryOpKind::IntToUint,
                };
                let extent = op.output_extent(&operand);
                Some(Val::Slot(self.emit(Op::Un(op, a)), extent))
            }
            // The union's arms come from the node's codomain, since the payload names only `tag`.
            // A union with an arm that holds a collection is a union of tiles
            // (`Tiling::from_extent`), not a column, so its wrap keeps the `VariantWrap` operator.
            TypedExprNode::Builtin(Builtin::VariantWrap(tag)) => {
                let extent = (self.extent_of)(&e.ty.codomain()?)?;
                let Extent::Union(arms) = &extent else {
                    return None;
                };
                if !is_plain(&extent) {
                    return None;
                }
                arms.get(tag)?;
                Some(Val::Wrap(tag.clone(), Box::new(cur), extent))
            }
            TypedExprNode::DisjointJoin(operands) => self.join(e, operands, cur),
            TypedExprNode::Apply { argument, function } => match &function.node {
                // `𝑐 ▷ const` for a closed value: the same value at every position. A variant
                // value names only its own arm, so a value holding one takes its extent from the
                // node's codomain.
                TypedExprNode::Builtin(Builtin::Const) => {
                    let value = expr_to_value(argument).ok()?;
                    let extent = match value_extent(&value) {
                        Some(extent) => extent,
                        None => (self.extent_of)(&e.ty.codomain()?)?,
                    };
                    Self::constant(value, extent)
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
                        .map(|entry| {
                            Some((
                                entry.label.runtime_key(),
                                self.step(&entry.value, cur.clone())?,
                            ))
                        })
                        .collect::<Option<Vec<_>>>()
                        .map(Val::Record),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// `e`, a `DisjointJoin` of `operands`, applied to `cur`: one `Case` whose arms are the
    /// operands' gates and whose results are the rest of their chains. The operands' gates must
    /// split the rows, by [`gates_split_the_rows`] for `Holds` gates and by naming every tag of one
    /// union for `Tag` gates. A gate on a variant built in the chain has a known tag, so the join
    /// reads as the one operand naming it. See `src/ccl/design/optimization.md`, "A conditional
    /// in an element-wise chain".
    fn join(&mut self, e: &Expr, operands: &[Expr], cur: Val) -> Option<Val> {
        let enclosing = self.scope;
        let start = self.instrs.len();
        let joined = self.join_arms(e, operands, cur);
        self.scope = enclosing;
        if joined.is_none() {
            self.truncate(start);
        }
        joined
    }

    fn join_arms(&mut self, e: &Expr, operands: &[Expr], cur: Val) -> Option<Val> {
        let enclosing = self.scope;
        let mut arms: Vec<(Slot, Val)> = Vec::new();
        let mut known: Option<(Vec<&Expr>, Val)> = None;
        let mut tags: Option<Scrutinee> = None;
        for operand in operands {
            let elements = flattened(operand);
            let (opened, rest, scrutinee) = self.gate(&elements, cur.clone())?;
            match opened {
                Opened::Known(None) => {}
                Opened::Known(Some(payload)) => {
                    if known.replace((rest.to_vec(), payload)).is_some() {
                        return None;
                    }
                }
                Opened::Arm(arm, arm_cur) => {
                    if let Some((union, union_tags)) = scrutinee {
                        match &tags {
                            Some((u, _)) if *u != union => return None,
                            _ => tags = Some((union, union_tags)),
                        }
                    }
                    self.scope = arm;
                    let result = rest.iter().try_fold(arm_cur, |cur, e| self.step(e, cur))?;
                    self.scope = enclosing;
                    arms.push((arm, result));
                }
            }
        }
        if let Some((rest, payload)) = known {
            return if arms.is_empty() {
                rest.iter().try_fold(payload, |cur, e| self.step(e, cur))
            } else {
                None
            };
        }
        let gates: Vec<&Gate> = arms
            .iter()
            .map(|(arm, _)| match &self.instrs[*arm as usize].op {
                Op::Arm { gate } => gate,
                op => unreachable!("an operand opens an arm, got {op:?}"),
            })
            .collect();
        let split = if gates.iter().all(|g| matches!(g, Gate::Holds(_))) {
            let mut formulas = Formulas::default();
            let mut nodes = HashMap::new();
            let roots: Vec<usize> = gates
                .iter()
                .map(|g| match g {
                    Gate::Holds(b) => self.formula(*b, &mut formulas, &mut nodes),
                    Gate::Tag(..) => unreachable!("all gates hold"),
                })
                .collect();
            gates_split_the_rows(&formulas, &roots)
        } else if gates.iter().all(|g| matches!(g, Gate::Tag(..))) {
            let named: Vec<&FieldKey> = gates
                .iter()
                .map(|g| match g {
                    Gate::Tag(_, tag) => tag,
                    Gate::Holds(_) => unreachable!("all gates are tags"),
                })
                .collect();
            let distinct = named
                .iter()
                .enumerate()
                .all(|(i, tag)| !named[..i].contains(tag));
            let (_, union_tags) = tags.as_ref()?;
            distinct && union_tags.iter().all(|tag| named.contains(&tag))
        } else {
            false
        };
        if !split {
            return None;
        }
        let codomain = (self.extent_of)(&e.ty.codomain()?)?;
        let constructs = matches!(
            codomain,
            Extent::Record(_) | Extent::Union(_) | Extent::Base(BaseType::Unit)
        );
        let mut results = Vec::with_capacity(arms.len());
        for (arm, result) in &arms {
            self.scope = *arm;
            let (slot, extent) = if constructs {
                self.output(result)?
            } else {
                self.column(result)?
            };
            // Each arm's column must have the join's layout, which `merge_parts` combines: a
            // record arm wider than the join's type would carry a field the others lack.
            if !fits(&extent, &codomain) {
                return None;
            }
            results.push((*arm, slot));
        }
        self.scope = enclosing;
        let case = self.emit(Op::Case {
            arms: results,
            constructs,
        });
        Some(if constructs {
            Val::Built(case, codomain)
        } else {
            Val::Slot(case, codomain)
        })
    }

    /// The gate a `DisjointJoin` operand of `elements` opens on `cur`, with the elements after it,
    /// and for a `Tag` gate the union slot and its extent's tags. The gate is parsed in the scope
    /// enclosing the join:
    ///
    /// - ``(𝑔 ▷ filter_values) ≫ …`` holds where `𝑔` does.
    /// - ``𝑠 ≫ variant_project(`𝑐) ≫ …`` holds where `𝑠` carries `𝑐`, and the chain continues
    ///   from the payload.
    /// - ``(id, 𝑠 ≫ variant_project(`𝑐)) ▷ zip ≫ …`` holds there too, and the chain continues from
    ///   the pair of the element and the payload.
    fn gate<'e>(
        &mut self,
        elements: &[&'e Expr],
        cur: Val,
    ) -> Option<(Opened, Vec<&'e Expr>, Option<Scrutinee>)> {
        let (first, rest) = elements.split_first()?;
        if let TypedExprNode::Apply { argument, function } = &first.node {
            match &function.node {
                TypedExprNode::Builtin(Builtin::FilterValues) => {
                    self.ops += 1;
                    let holds = self.step(argument, cur.clone())?;
                    let (b, extent) = self.column(&holds)?;
                    if !matches!(extent, Extent::Base(BaseType::Bool)) {
                        return None;
                    }
                    let arm = self.emit(Op::Arm {
                        gate: Gate::Holds(b),
                    });
                    return Some((Opened::Arm(arm, cur), rest.to_vec(), None));
                }
                TypedExprNode::Builtin(Builtin::Zip) => {
                    let TypedExprNode::Tuple(items) = &argument.node else {
                        return None;
                    };
                    let projects = |item: &Expr| flattened(item).iter().any(|e| is_project(e));
                    let k = items.iter().position(projects)?;
                    if items.iter().filter(|item| projects(item)).count() != 1 {
                        return None;
                    }
                    self.ops += 2;
                    let mut vals = Vec::with_capacity(items.len());
                    let mut opened = None;
                    for (i, item) in items.iter().enumerate() {
                        if i == k {
                            let item_elements = flattened(item);
                            let (o, item_rest, scrutinee) =
                                self.gate(&item_elements, cur.clone())?;
                            let Opened::Arm(arm, payload) = o else {
                                return None;
                            };
                            // The rest of the item's chain reads the payload in the arm.
                            let enclosing = self.scope;
                            self.scope = arm;
                            let value = item_rest
                                .iter()
                                .try_fold(payload, |cur, e| self.step(e, cur));
                            self.scope = enclosing;
                            vals.push(value?);
                            opened = Some((arm, scrutinee));
                        } else {
                            vals.push(self.step(item, cur.clone())?);
                        }
                    }
                    let (arm, scrutinee) = opened?;
                    return Some((Opened::Arm(arm, Val::Tuple(vals)), rest.to_vec(), scrutinee));
                }
                _ => {}
            }
        }
        let k = elements.iter().position(|e| is_project(e))?;
        let TypedExprNode::Builtin(Builtin::VariantProject(tag)) = &elements[k].node else {
            unreachable!("found by `is_project`")
        };
        let scrutinee = elements[..k]
            .iter()
            .try_fold(cur, |cur, e| self.step(e, cur))?;
        self.ops += 1;
        let rest = elements[k + 1..].to_vec();
        let opened = match scrutinee {
            Val::Wrap(t, payload, _) => {
                return Some((Opened::Known((t == *tag).then_some(*payload)), rest, None));
            }
            ref union @ (Val::Read(_, Extent::Union(ref union_arms))
            | Val::Payload(_, _, Extent::Union(ref union_arms))) => {
                let union_tags: Vec<FieldKey> = union_arms.keys().cloned().collect();
                let payload = (self.extent_of)(&elements[k].ty.codomain()?)?;
                if !is_plain(&payload) {
                    return None;
                }
                let (u, _) = self.copied(union)?;
                let arm = self.emit(Op::Arm {
                    gate: Gate::Tag(u, tag.clone()),
                });
                (
                    Opened::Arm(arm, Val::Payload(arm, Vec::new(), payload)),
                    Some((u, union_tags)),
                )
            }
            _ => return None,
        };
        Some((opened.0, rest, opened.1))
    }

    /// The node of `formulas` for the gate in the `Bool` slot `slot`, adding the nodes it reads.
    /// `nodes` holds the node of each slot added so far, so a slot read twice is one node.
    fn formula(
        &self,
        slot: Slot,
        formulas: &mut Formulas,
        nodes: &mut HashMap<Slot, usize>,
    ) -> usize {
        if let Some(&node) = nodes.get(&slot) {
            return node;
        }
        let node = match &self.instrs[slot as usize].op {
            Op::Const(Value::Bool(value)) => Node::Known(*value),
            Op::Un(UnaryOpKind::Not, a) => Node::Not(self.formula(*a, formulas, nodes)),
            Op::Bin(InterpreterBinOp::BoolLogic(LogicKind::And), a, b) => Node::And(
                self.formula(*a, formulas, nodes),
                self.formula(*b, formulas, nodes),
            ),
            Op::Bin(InterpreterBinOp::BoolLogic(LogicKind::Or), a, b) => Node::Or(
                self.formula(*a, formulas, nodes),
                self.formula(*b, formulas, nodes),
            ),
            _ => Node::Atom,
        };
        let node = formulas.push(node);
        nodes.insert(slot, node);
        node
    }

    /// Return the final instruction and result extent, emitting result records if needed.
    /// Input paths and constants are not eligible results on their own: their ordinary conversion
    /// does not require a scalar program.
    fn root_of(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        match v {
            // The program's result is its last instruction. A computed value equal to an earlier
            // one is that earlier slot (`Parser::emit`), so a prefix ending at it has no result.
            Val::Slot(slot, extent) if *slot as usize + 1 == self.instrs.len() => {
                Some((*slot, extent.clone()))
            }
            Val::Built(slot, extent) if *slot as usize + 1 == self.instrs.len() => {
                Some((*slot, extent.clone()))
            }
            Val::Slot(..) | Val::Built(..) => None,
            Val::Tuple(_) | Val::Record(_) | Val::Wrap(..) => self.output(v),
            Val::Read(..) | Val::Const(..) | Val::Payload(..) => None,
        }
    }

    /// `v` as a column of the result, with its extent. A variant is a `Wrap` of its payload's
    /// column, and a record ([`Parser::fields_of`]) is a `Record` of its fields' columns. Anything
    /// else is its own column: a computed one, a base value or `Unit` read from the input or held
    /// as a constant, or a union read from the input. A product with no field has no column, since
    /// nothing in it counts its rows.
    fn output(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        // A `Case` that constructs has no column to narrow, so it is read only in its own scope.
        if let Val::Built(slot, extent) = v {
            let in_scope = self.instrs[*slot as usize].scope == self.scope;
            return in_scope.then(|| (*slot, extent.clone()));
        }
        if let Val::Wrap(tag, payload, extent) = v {
            let (payload, _) = self.output(payload)?;
            let tag = tag.clone();
            return Some((self.emit(Op::Wrap { tag, payload }), extent.clone()));
        }
        let mut fields: Vec<(SmolStr, Val)> = match Self::fields_of(v) {
            Some(fields) => fields.into_iter().collect(),
            None => return self.column(v).or_else(|| self.copied(v)),
        };
        if fields.is_empty() {
            return None;
        }
        // In name order, so that equal chains give equal programs.
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        let mut named = Vec::with_capacity(fields.len());
        let mut extents = HashMap::with_capacity(fields.len());
        for (name, field) in fields {
            let (slot, extent) = self.output(&field)?;
            named.push((name.clone(), slot));
            extents.insert(name, extent);
        }
        Some((self.emit(Op::Record(named)), Extent::Record(extents)))
    }
}

/// Whether a column of `extent` has the layout of a column of `target`: the same record fields, at
/// every depth, and union arms that `target` names. A variant's column holds only the arms it
/// carries, so a union fits a wider one; a record does not, since a column holds every field it
/// has.
fn fits(extent: &Extent, target: &Extent) -> bool {
    match (extent, target) {
        (Extent::Record(fields), Extent::Record(target)) => {
            fields.len() == target.len()
                && fields
                    .iter()
                    .all(|(name, field)| target.get(name).is_some_and(|t| fits(field, t)))
        }
        (Extent::Union(arms), Extent::Union(target)) => arms
            .iter()
            .all(|(tag, arm)| target.get(tag).is_some_and(|t| fits(arm, t))),
        (Extent::Record(_) | Extent::Union(_), _) | (_, Extent::Record(_) | Extent::Union(_)) => {
            false
        }
        _ => true,
    }
}

/// The elements of `e` read as a chain: a composition's elements, flattened, or `e` alone.
fn flattened(e: &Expr) -> Vec<&Expr> {
    match &e.node {
        TypedExprNode::Compose(elements) => elements.iter().flat_map(flattened).collect(),
        _ => vec![e],
    }
}

/// Whether `e` is a `variant_project`.
fn is_project(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Builtin(Builtin::VariantProject(_)))
}

/// The extent of a closed value, read from the value: a base value or a record of them. A variant
/// names only its own arm, so it has no extent here.
fn value_extent(value: &Value) -> Option<Extent> {
    Some(match value {
        Value::Unit => Extent::Base(BaseType::Unit),
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

/// Whether a column of `extent` is one `eval` can read from: a base type, or a record or union of
/// them. An operation reads only a base column other than `Unit`, and a constructor copies a
/// `Unit` or union one.
fn is_plain(extent: &Extent) -> bool {
    match extent {
        Extent::Base(_) => true,
        Extent::Record(fields) => fields.values().all(is_plain),
        Extent::Union(arms) => arms.values().all(is_plain),
        _ => false,
    }
}

/// Return the longest prefix accepted by the scalar recognizer, or `None` if none is eligible.
/// `input` is the extent of each input value, and `extent_of` gives the extent of a type.
///
/// An eligible prefix ends at an operation, a product or a variant and meets [`Parser::ops`]'s minimum count
/// of two. See `src/ccl/design/optimization.md`, "Element-wise chains", for supported forms and
/// conversion boundaries.
pub fn fuse_prefix(
    chain: &[Expr],
    input: &Extent,
    extent_of: &dyn Fn(&Type) -> Option<Extent>,
) -> Option<Fused> {
    if !is_plain(input) {
        return None;
    }
    let mut parser = Parser {
        scope: ROOT,
        extent_of,
        instrs: Vec::new(),
        slots: HashMap::new(),
        ops: 0,
    };
    let mut cur = Val::Read(Vec::new(), input.clone());
    // The chosen prefix: how many elements it consumes, how many instructions it holds before
    // its output reads the fields of a product, and the value it ends at.
    let mut best: Option<(usize, usize, Val)> = None;
    for (k, e) in chain.iter().enumerate() {
        let Some(next) = parser.step(e, cur.clone()) else {
            break;
        };
        cur = next;
        if parser.ops >= 2 {
            // Probing a product output emits instructions that later elements must not read.
            // Discard them now and rebuild the output only for the chosen prefix.
            let len = parser.instrs.len();
            if parser.root_of(&cur).is_some() {
                best = Some((k + 1, len, cur.clone()));
            }
            parser.truncate(len);
        }
    }
    let (consumed, len, root) = best?;
    // Instructions past the prefix belong to an element the parse then abandoned.
    parser.truncate(len);
    let (_, codomain) = parser
        .root_of(&root)
        .expect("the root is read from the state it was chosen in");
    let program = ScalarProgram {
        instrs: parser.instrs,
    };
    debug_assert!(
        program.constructors_build_only_the_result(),
        "a constructor is the last instruction or a field or payload of a later one, and no \
         operation reads one; got {program}"
    );
    debug_assert!(
        program.operands_have_views(input),
        "an operation reads only a column with a view, over {input}; got {program}"
    );
    debug_assert!(
        program.scopes_are_consistent(),
        "every instruction reads its own scope, and scopes nest; got {program}"
    );
    Some(Fused {
        program,
        domain: input.clone(),
        codomain,
        consumed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Occurrence;
    use crate::ccl::RecordEntry;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Lit, LogicKind};
    use crate::interpreter::apply_binop_column;

    impl ScalarProgram {
        /// A program of `ops`, each in the root scope.
        fn rooted(ops: Vec<Op>) -> Self {
            let instrs = ops
                .into_iter()
                .map(|op| Instr { scope: ROOT, op })
                .collect();
            ScalarProgram { instrs }
        }
    }

    /// [`fuse_prefix`] for a chain that holds no variant, which reads no type's extent.
    fn fuse(chain: &[Expr], input: &Extent) -> Option<Fused> {
        fuse_prefix(chain, input, &|ty| {
            panic!("a chain without a variant reads no type's extent, read {ty}")
        })
    }

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
        let fused = fuse(&conjunction(), &int()).expect("every arm is element-wise");
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
        let fused = fuse(&chain, &int()).unwrap();
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
        let fused = fuse(&chain, &int()).unwrap();
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
        let fused = fuse(&chain, &record).unwrap();
        let inputs = fused
            .program
            .instrs
            .iter()
            .filter(|instr| matches!(instr.op, Op::Input { .. }))
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
        let fused = fuse(&chain, &record).expect("a closed record is a constant");
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
        Some(bools(fuse(&chain, input_extent)?.program.eval(input)))
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
        let fused = fuse(&chain, &tuple_of_ints(2)).unwrap();
        assert!(
            fused
                .program
                .instrs
                .iter()
                .all(|instr| !matches!(instr.op, Op::Const(Value::Record(_)))),
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
        let fused = fuse(&chain, &extent).expect("a nested record is compared by field");
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
    /// records are not compared, so the prefix ends before the comparison, at the `zip`.
    #[test]
    fn a_comparison_without_a_field_to_compare_ends_the_prefix() {
        let (record, other) = (tuple_of_ints(2), record_of("x", int()));
        let consumed = |input: &Extent, constant: Expr, op: CompareKind| {
            let chain = vec![zip(vec![id(), constant]), binop(BinOpKind::Compare(op))];
            fuse(&chain, input).map(|fused| fused.consumed)
        };
        assert_eq!(
            consumed(&record, closed_tuple(&[1, 2]), CompareKind::Equals),
            Some(2)
        );
        assert_eq!(consumed(&record, constant(1), CompareKind::Equals), Some(1));
        assert_eq!(
            consumed(&other, closed_tuple(&[1, 2]), CompareKind::Equals),
            Some(1)
        );
        assert_eq!(
            consumed(&record, closed_tuple(&[1, 2]), CompareKind::Less),
            Some(1)
        );
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
            bools(fuse(&chain, &record).unwrap().program.eval(&input))
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

    /// A product built in the chain is taken apart like a record read or held as a constant, so
    /// `(a: (z: x * 2) == (z: x + 1))` is one program whose only `Record` is the result.
    #[test]
    fn a_product_built_in_the_chain_is_compared_field_by_field() {
        let eq = Expr::compose(vec![
            zip(vec![
                zip_record(vec![("z", arith(ArithmeticKind::Mul, 2))]),
                zip_record(vec![("z", arith(ArithmeticKind::Add, 1))]),
            ]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ]);
        let chain = vec![zip_record(vec![("a", eq)])];
        let fused = fuse(&chain, &int()).expect("both records are built in the chain");
        let records = fused
            .program
            .instrs
            .iter()
            .filter(|instr| matches!(instr.op, Op::Record(_)))
            .count();
        assert_eq!(records, 1, "{}", fused.program);
        let out = fused.program.eval(&ColumnValue::Ints(vec![0, 1, 2]));
        assert_eq!(
            field_of(&out, "a"),
            &ColumnValue::Bools(vec![false, true, false])
        );
    }

    /// A tuple built in the chain compares with one read from the input, position by position:
    /// `(x.1 - 1, x.1) == x` over the rows `(i % 2, 2)`.
    #[test]
    fn a_tuple_built_in_the_chain_compares_with_one_read() {
        let second_minus_one = Expr::compose(vec![
            zip(vec![Expr::proj_index(1), constant(1)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Sub)),
        ]);
        let built = zip(vec![second_minus_one, Expr::proj_index(1)]);
        let compare = |op| {
            let chain = vec![
                zip(vec![built.clone(), id()]),
                binop(BinOpKind::Compare(op)),
            ];
            let fused = fuse(&chain, &tuple_of_ints(2)).expect("the tuple is taken apart");
            bools(fused.program.eval(&tuples(2, 5)))
        };
        let is_one: Vec<bool> = (0..5).map(|i| i % 2 == 1).collect();
        assert_eq!(compare(CompareKind::Equals), is_one);
        assert_eq!(
            compare(CompareKind::NotEquals),
            is_one.iter().map(|b| !b).collect::<Vec<_>>()
        );
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
            bools(fuse(&chain, &extent).unwrap().program.eval(&input))
        };
        assert_eq!(ne(7), (0..n).map(|i| i % 2 == 0).collect::<Vec<_>>());
        assert_eq!(ne(8), vec![true; n]);
    }

    /// The fields come from the extents, so a column wider than the extent that names it compares
    /// over the fields both sides name.
    #[test]
    fn a_column_wider_than_its_extent_compares_over_the_extents_fields() {
        let n = 4;
        let wide = tuples(3, n);
        let got = compare_to_tuple(&tuple_of_ints(2), CompareKind::Equals, &[1, 2], &wide);
        assert_eq!(got.unwrap(), (0..n).map(|i| i % 2 == 1).collect::<Vec<_>>());
    }

    /// A field whose compared values hold only `unit` is equal at every row, so a comparison of
    /// records leaves it out and agrees with the unfused comparison: `p.l == p.r` and `p.l != p.r`,
    /// where `l` and `r` differ in `x` at some rows and share `u: Unit` and a nested `n`. The `n` of
    /// `r` is wider than the `n` of `l`, and the field it adds is not compared.
    #[test]
    fn a_comparison_leaves_out_the_fields_that_hold_only_unit() {
        let unit = || Extent::Base(BaseType::Unit);
        let narrow = record_of_extents(vec![("u", unit())]);
        let wide = record_of_extents(vec![("u", unit()), ("w", int())]);
        let side = |n| record_of_extents(vec![("n", n), ("u", unit()), ("x", int())]);
        let input = record_of_extents(vec![("l", side(narrow)), ("r", side(wide))]);
        let rows = 4;
        let units = || ColumnValue::Units(rows);
        let records = |fields: Vec<(&str, ColumnValue)>| {
            ColumnValue::Records(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
        };
        let l = records(vec![
            ("n", records(vec![("u", units())])),
            ("u", units()),
            ("x", ColumnValue::Ints(vec![1, 2, 3, 4])),
        ]);
        let r = records(vec![
            (
                "n",
                records(vec![
                    ("u", units()),
                    ("w", ColumnValue::Ints(vec![9; rows])),
                ]),
            ),
            ("u", units()),
            ("x", ColumnValue::Ints(vec![1, 0, 3, 0])),
        ]);
        let column = records(vec![("l", l.clone()), ("r", r.clone())]);
        for kind in [CompareKind::Equals, CompareKind::NotEquals] {
            let op = BinOpKind::Compare(kind);
            let chain = vec![
                zip(vec![Expr::proj_field("l"), Expr::proj_field("r")]),
                binop(op),
            ];
            let fused = fuse(&chain, &input).expect("`x` is compared");
            assert_eq!(fused.consumed, 2, "{kind:?}");
            let want = apply_binop_column(op.into(), &l, &r);
            assert_eq!(fused.program.eval(&column), want, "{kind:?}");
        }
    }

    /// Two records whose shared fields all hold only `unit` have no field to compare, so the prefix
    /// ends before the comparison: `p == p` over `{u: Unit}`.
    #[test]
    fn a_comparison_of_units_alone_has_no_program() {
        let units = record_of_extents(vec![("u", Extent::Base(BaseType::Unit))]);
        let chain = vec![
            zip(vec![id(), id()]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        assert_eq!(fuse(&chain, &units).map(|fused| fused.consumed), Some(1));
    }

    /// Equal chains give equal programs, whatever order a hash map holds the record's fields in.
    #[test]
    fn a_record_comparison_gives_the_same_program_every_time() {
        let wide = tuple_of_ints(12);
        let chain = vec![
            zip(vec![id(), closed_tuple(&(0..12).collect::<Vec<_>>())]),
            binop(BinOpKind::Compare(CompareKind::Equals)),
        ];
        let first = fuse(&chain, &wide).unwrap().program;
        for _ in 0..8 {
            assert_eq!(fuse(&chain, &wide).unwrap().program, first);
        }
    }

    /// A constant is not a root: `simplify` reduces `f ≫ c ▷ const` to the constant, so a chain
    /// does not end at one, and the prefix ends before it.
    #[test]
    fn the_prefix_ends_before_a_trailing_constant() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![id(), constant(1)]), add, constant(5)];
        assert_eq!(fuse(&chain, &int()).unwrap().consumed, 2);
    }

    /// `7 - x` and `x - 7` keep their operand order through the zip.
    #[test]
    fn operand_order_survives_the_zip() {
        let sub = binop(BinOpKind::Arithmetic(ArithmeticKind::Sub));
        let left = vec![zip(vec![constant(7), id()]), sub.clone()];
        let right = vec![zip(vec![id(), constant(7)]), sub];
        let input = || ColumnValue::Ints(vec![1, 10]);
        let eval = |chain: &[Expr]| fuse(chain, &int()).unwrap().program.eval(&input());
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
        let fused = fuse(&chain, &record).unwrap();
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
    /// `x + 1` holds a `zip`, which counts as two operations, so it fuses, where `neg x` and
    /// `not x` are one.
    #[test]
    fn adding_a_constant_fuses_and_a_lone_unary_operation_does_not() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let fused = fuse(&[zip(vec![id(), constant(1)]), add], &int()).unwrap();
        assert_eq!(fused.consumed, 2);
        assert_eq!(
            fused.program.eval(&ColumnValue::Ints(vec![1, 2])),
            ColumnValue::Ints(vec![2, 3])
        );
        assert!(fuse(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
        let bools = Extent::Base(BaseType::Bool);
        assert!(fuse(&[Expr::builtin(Builtin::NotFn)], &bools).is_none());
    }

    #[test]
    fn a_lone_operation_is_left_to_its_own_conversion() {
        assert!(fuse(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
        assert!(fuse(&[binop(BinOpKind::Arithmetic(ArithmeticKind::Add))], &int()).is_none());
    }

    /// Two operations fuse whether or not a `zip` joins them.
    #[test]
    fn a_chain_of_unary_operations_fuses_without_a_zip() {
        let chain = vec![Expr::builtin(Builtin::Neg), Expr::builtin(Builtin::Neg)];
        let fused = fuse(&chain, &int()).expect("two operations");
        assert_eq!(fused.consumed, 2);
        assert_eq!(
            fused.program.eval(&ColumnValue::Ints(vec![1, -2, 3])),
            ColumnValue::Ints(vec![1, -2, 3])
        );
        let bools = Extent::Base(BaseType::Bool);
        let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
        let fused = fuse(&chain, &bools).expect("two operations");
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
        assert_eq!(fuse(&chain, &int()).unwrap().consumed, 2);
    }

    /// `zip` of a record with the arms `arms`, by name.
    fn zip_record(arms: Vec<(&str, Expr)>) -> Expr {
        let arms = arms
            .into_iter()
            .map(|(name, arm)| RecordEntry::new(name, Occurrence::mint(), arm))
            .collect();
        Expr::apply(
            Expr::new(TypedExprNode::Record(arms)),
            Expr::builtin(Builtin::Zip),
        )
    }

    /// `x op n` as a chain element.
    fn arith(op: ArithmeticKind, n: i64) -> Expr {
        Expr::compose(vec![
            zip(vec![id(), constant(n)]),
            binop(BinOpKind::Arithmetic(op)),
        ])
    }

    fn record_of_extents(fields: Vec<(&str, Extent)>) -> Extent {
        Extent::Record(
            fields
                .into_iter()
                .map(|(name, extent)| (SmolStr::from(name), extent))
                .collect(),
        )
    }

    /// The column of field `name` of a column of records.
    fn field_of<'c>(column: &'c ColumnValue, name: &str) -> &'c ColumnValue {
        let ColumnValue::Records(fields) = column else {
            panic!("expected a column of records, got {column:?}")
        };
        &fields[name]
    }

    /// A chain that ends in a `zip` yields one column of records, a field per arm, and an arm
    /// that reads the input or a constant is a field like any other.
    #[test]
    fn a_tuple_result_is_one_column_of_records() {
        let chain = vec![zip(vec![arith(ArithmeticKind::Add, 1), id(), constant(7)])];
        let fused = fuse(&chain, &int()).expect("every arm is element-wise");
        assert_eq!(fused.consumed, 1);
        assert_eq!(fused.codomain, tuple_of_ints(3));
        let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 2]));
        assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![7, 7]));
    }

    /// A record `zip` names its fields, and an arm that is itself a `zip` is a column of records
    /// inside the result: `(a: x + 1, b: (c: x - 1, d: 1))`.
    #[test]
    fn a_nested_record_result_is_a_record_column_inside_one() {
        let chain = vec![zip_record(vec![
            ("a", arith(ArithmeticKind::Add, 1)),
            (
                "b",
                zip_record(vec![
                    ("c", arith(ArithmeticKind::Sub, 1)),
                    ("d", constant(1)),
                ]),
            ),
        ])];
        let fused = fuse(&chain, &int()).expect("every arm is element-wise");
        let inner = record_of_extents(vec![("c", int()), ("d", int())]);
        assert_eq!(
            fused.codomain,
            record_of_extents(vec![("a", int()), ("b", inner)])
        );
        let out = fused.program.eval(&ColumnValue::Ints(vec![5, 10]));
        assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(vec![6, 11]));
        let b = field_of(&out, "b");
        assert_eq!(field_of(b, "c"), &ColumnValue::Ints(vec![4, 9]));
        assert_eq!(field_of(b, "d"), &ColumnValue::Ints(vec![1, 1]));
    }

    /// A field that holds a record read from the input is a record column of its base fields,
    /// each read from the input.
    #[test]
    fn a_record_field_read_from_the_input_is_copied_field_by_field() {
        let pair = tuple_of_ints(2);
        let first_plus_one = Expr::compose(vec![
            zip(vec![Expr::proj_index(0), constant(1)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ]);
        let chain = vec![zip(vec![id(), first_plus_one, constant(100)])];
        let fused = fuse(&chain, &pair).expect("one field is computed");
        assert_eq!(
            fused.codomain,
            record_of_extents(vec![("_0", pair), ("_1", int()), ("_2", int())])
        );
        let out = fused.program.eval(&tuples(2, 3));
        assert_eq!(field_of(&out, "_0"), &tuples(2, 3));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 2, 1]));
        assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![100; 3]));
    }

    /// A field that holds a closed record is a record column of its base values, each repeated.
    #[test]
    fn a_record_constant_field_is_repeated_field_by_field() {
        let record = Expr::apply(
            Expr::tuple(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::String("s".into())),
            ]),
            Expr::builtin(Builtin::Const),
        );
        let chain = vec![zip(vec![arith(ArithmeticKind::Add, 1), record])];
        let fused = fuse(&chain, &int()).expect("one field is computed");
        let n = BLOCK_ROWS + 3;
        let out = fused.program.eval(&ramp(n));
        let constant = field_of(&out, "_1");
        assert_eq!(field_of(constant, "_0"), &ColumnValue::Ints(vec![1; n]));
        assert_eq!(
            field_of(constant, "_1"),
            &ColumnValue::Strings(vec!["s".into(); n])
        );
    }

    /// A nested record of computed fields is built block by block:
    /// `(a: x + 1, b: (c: x * 2, d: x))` over more than two blocks holds every row's fields.
    #[test]
    fn a_nested_computed_record_spans_blocks() {
        let chain = vec![zip_record(vec![
            ("a", arith(ArithmeticKind::Add, 1)),
            (
                "b",
                zip_record(vec![("c", arith(ArithmeticKind::Mul, 2)), ("d", id())]),
            ),
        ])];
        let fused = fuse(&chain, &int()).expect("every arm is element-wise");
        let n = 2 * BLOCK_ROWS + 3;
        let input = ramp(n);
        let xs: Vec<i64> = (0..n as i64).map(|i| i * 7 % 3000).collect();
        let out = fused.program.eval(&input);
        let plus_one = xs.iter().map(|x| x + 1).collect();
        assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(plus_one));
        let b = field_of(&out, "b");
        let doubled = xs.iter().map(|x| x * 2).collect();
        assert_eq!(field_of(b, "c"), &ColumnValue::Ints(doubled));
        assert_eq!(field_of(b, "d"), &input);
    }

    /// A product of reads and constants is one column of records, its fields copied and repeated:
    /// `(x, 1)` replaces the `MapResultToConst` that pairs the constant with `x`, `(x, x)` the
    /// `Memo`, `FanOut`s and `Zip` of its two reads, and `(a=x)` the `RecordWrap` of its one.
    #[test]
    fn a_product_of_reads_and_constants_fuses() {
        let chain = vec![zip(vec![id(), constant(1)])];
        let fused = fuse(&chain, &int()).expect("a zip is two operations");
        let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![4, 5]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 1]));
        let pair = tuple_of_ints(2);
        let swapped = vec![zip(vec![
            Expr::proj_index(1),
            Expr::proj_index(0),
            closed_tuple(&[1, 2]),
        ])];
        let fused = fuse(&swapped, &pair).expect("two projections and a constant");
        let out = fused.program.eval(&tuples(2, 3));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2; 3]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![0, 1, 0]));
        let fused = fuse(&[zip(vec![id(), id()])], &int()).expect("a zip of identities");
        let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![4, 5]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![4, 5]));
        let one_field = [zip_record(vec![("a", id())])];
        let fused = fuse(&one_field, &int()).expect("a zip of one arm");
        let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
        assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(vec![4, 5]));
    }

    /// A `Unit` field read from the input is copied into the result: `(p, p.x + 1)` over
    /// `{u: Unit, x: Int}`.
    #[test]
    fn a_unit_field_of_the_input_is_copied() {
        let unit = record_of_extents(vec![("u", Extent::Base(BaseType::Unit)), ("x", int())]);
        let x_plus_one = Expr::compose(vec![
            zip(vec![Expr::proj_field("x"), constant(1)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ]);
        let fused = fuse(&[zip(vec![id(), x_plus_one])], &unit).expect("a `Unit` field is copied");
        let input = ColumnValue::Records(HashMap::from([
            ("u".into(), ColumnValue::Units(3)),
            ("x".into(), ColumnValue::Ints(vec![1, 2, 3])),
        ]));
        let out = fused.program.eval(&input);
        assert_eq!(field_of(&out, "_0"), &input);
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3, 4]));
    }

    fn tag(name: &str) -> FieldKey {
        FieldKey::Name(name.into())
    }

    /// ``{`none | `some{Int}}``.
    fn option_type() -> Type {
        Type::variant(vec![
            (tag("none"), Type::Base(BaseType::Unit)),
            (tag("some"), Type::Base(BaseType::Int)),
        ])
    }

    /// The extent of [`option_type`].
    fn option_extent() -> Extent {
        Extent::Union(TagMap::from_arms(vec![
            (tag("none"), Extent::Base(BaseType::Unit)),
            (tag("some"), int()),
        ]))
    }

    /// [`fuse_prefix`] where every type read is [`option_type`].
    fn fuse_options(chain: &[Expr], input: &Extent) -> Option<Fused> {
        fuse_prefix(chain, input, &|ty| {
            assert_eq!(*ty, option_type(), "only an option's extent is read");
            Some(option_extent())
        })
    }

    /// ``variant_wrap(`tag) : Int ⇒ {`none | `some{Int}}``.
    fn wrap(name: &str) -> Expr {
        Expr::builtin(Builtin::VariantWrap(tag(name)))
            .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
    }

    /// ``(`none(unit) ▷ const) : Int ⇒ {`none | `some{Int}}``.
    fn none() -> Expr {
        let ctor = Expr::variant_ctor("none", Occurrence::mint(), Expr::lit(Lit::Unit));
        Expr::apply(ctor, Expr::builtin(Builtin::Const))
            .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
    }

    /// ``(`some(n) ▷ const) : Int ⇒ {`none | `some{Int}}``.
    fn some(n: i64) -> Expr {
        let ctor = Expr::variant_ctor("some", Occurrence::mint(), Expr::lit(Lit::Int(n)));
        Expr::apply(ctor, Expr::builtin(Builtin::Const))
            .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
    }

    /// A wrap at the end of a chain yields a union column of one arm, numbered by input row
    /// across blocks: ``x + 1 ≫ variant_wrap(`some)`` over 2,500 rows.
    #[test]
    fn a_wrap_yields_a_union_column_of_one_arm() {
        let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
        let fused = fuse_options(&chain, &int()).expect("an operation and a wrap");
        assert_eq!(fused.consumed, 2);
        assert_eq!(fused.codomain, option_extent());
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        let some = UnionArm::new(
            (0..n as usize).collect(),
            ColumnValue::Ints((1..=n).collect()),
        );
        assert_eq!(
            out,
            ColumnValue::Union(TagMap::from_arms(vec![(tag("some"), some)]))
        );
    }

    /// A variant constant is the wrap of its payload, and a `Unit` payload is a `Units` column
    /// that grows block by block: ``(a: x * 2, b: `none(unit))`` over 2,500 rows.
    #[test]
    fn a_variant_constant_is_a_field() {
        let chain = vec![zip_record(vec![
            ("a", arith(ArithmeticKind::Mul, 2)),
            ("b", none()),
        ])];
        let fused = fuse_options(&chain, &int()).expect("an operation and a constant");
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        assert_eq!(
            field_of(&out, "a"),
            &ColumnValue::Ints((0..n).map(|x| x * 2).collect())
        );
        let none = UnionArm::new((0..n as usize).collect(), ColumnValue::Units(n as usize));
        assert_eq!(
            field_of(&out, "b"),
            &ColumnValue::Union(TagMap::from_arms(vec![(tag("none"), none)]))
        );
    }

    /// A union field of the input is copied into the result row for row, with no type read:
    /// `(c: p.b, d: p.a + 1)` over 2,500 rows whose `b` alternates between the arms.
    #[test]
    fn a_union_field_of_the_input_is_copied_across_blocks() {
        let input = record_of_extents(vec![("a", int()), ("b", option_extent())]);
        let a_plus_one = Expr::compose(vec![
            zip(vec![Expr::proj_field("a"), constant(1)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ]);
        let chain = vec![zip_record(vec![
            ("c", Expr::proj_field("b")),
            ("d", a_plus_one),
        ])];
        let fused = fuse(&chain, &input).expect("a copied field and an operation");
        let n = 2_500;
        let options: Vec<Value> = (0..n)
            .map(|i| Value::Union {
                tag: tag(if i % 2 == 0 { "some" } else { "none" }),
                inner: Box::new(if i % 2 == 0 {
                    Value::Int(i)
                } else {
                    Value::Unit
                }),
            })
            .collect();
        let b = ColumnValue::from_values(options.clone(), &option_extent());
        let column = ColumnValue::Records(HashMap::from([
            ("a".into(), ColumnValue::Ints((0..n).collect())),
            ("b".into(), b),
        ]));
        let out = fused.program.eval(&column);
        let c = field_of(&out, "c");
        assert_eq!(
            (0..n as usize).map(|i| c.index_at(i)).collect::<Vec<_>>(),
            options
        );
        assert_eq!(field_of(&out, "d"), &ColumnValue::Ints((1..=n).collect()));
    }

    /// [`fuse_prefix`] where each type read is one of `types`, with its extent.
    fn fuse_typed(chain: &[Expr], input: &Extent, types: &[(Type, Extent)]) -> Option<Fused> {
        fuse_prefix(chain, input, &|ty| {
            let found = types.iter().find(|(t, _)| t == ty);
            Some(
                found
                    .unwrap_or_else(|| panic!("no extent for {ty}"))
                    .1
                    .clone(),
            )
        })
    }

    /// ``variant_wrap(`name) : payload ⇒ union``.
    fn wrap_into(name: &str, payload: Type, union: Type) -> Expr {
        Expr::builtin(Builtin::VariantWrap(tag(name))).with_ty(Type::fun(payload, union))
    }

    /// A wrap of a wrap is a union column whose payload is a union column, each numbered by input
    /// row across blocks: ``x + 1 ≫ variant_wrap(`inner) ≫ variant_wrap(`outer)``.
    #[test]
    fn a_wrap_of_a_wrap_nests_union_columns() {
        let inner_ty = Type::variant(vec![(tag("inner"), Type::Base(BaseType::Int))]);
        let outer_ty = Type::variant(vec![(tag("outer"), inner_ty.clone())]);
        let inner = Extent::Union(TagMap::from_arms(vec![(tag("inner"), int())]));
        let outer = Extent::Union(TagMap::from_arms(vec![(tag("outer"), inner.clone())]));
        let chain = vec![
            arith(ArithmeticKind::Add, 1),
            wrap_into("inner", Type::Base(BaseType::Int), inner_ty.clone()),
            wrap_into("outer", inner_ty.clone(), outer_ty.clone()),
        ];
        let types = [(inner_ty, inner), (outer_ty, outer.clone())];
        let fused = fuse_typed(&chain, &int(), &types).expect("an operation and two wraps");
        assert_eq!(fused.consumed, 3);
        assert_eq!(fused.codomain, outer);
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        let rows = || (0..n as usize).collect::<Vec<_>>();
        let inner = UnionArm::new(rows(), ColumnValue::Ints((1..=n).collect()));
        let inner = ColumnValue::Union(TagMap::from_arms(vec![(tag("inner"), inner)]));
        let outer = UnionArm::new(rows(), inner);
        assert_eq!(
            out,
            ColumnValue::Union(TagMap::from_arms(vec![(tag("outer"), outer)]))
        );
    }

    /// A wrap of a product holds a column of records: ``(a: x + 1, b: x) ▷ zip ≫ variant_wrap(`r)``.
    #[test]
    fn a_wrap_of_a_product_holds_a_column_of_records() {
        let int_ty = || Type::Base(BaseType::Int);
        let pair_ty = Type::Record(vec![("a".into(), int_ty()), ("b".into(), int_ty())]);
        let r_ty = Type::variant(vec![(tag("r"), pair_ty.clone())]);
        let pair = record_of_extents(vec![("a", int()), ("b", int())]);
        let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), pair)]));
        let chain = vec![
            zip_record(vec![("a", arith(ArithmeticKind::Add, 1)), ("b", id())]),
            wrap_into("r", pair_ty, r_ty.clone()),
        ];
        let fused = fuse_typed(&chain, &int(), &[(r_ty, r)]).expect("a product and a wrap");
        let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
        let ColumnValue::Union(arms) = &out else {
            panic!("expected a union column, got {out:?}")
        };
        let arm = arms.get(&tag("r")).expect("the `r` arm");
        assert_eq!(arm.rows(), [0, 1]);
        assert_eq!(field_of(arm.values(), "a"), &ColumnValue::Ints(vec![2, 3]));
        assert_eq!(field_of(arm.values(), "b"), &ColumnValue::Ints(vec![1, 2]));
    }

    /// A record constant holding a variant is a record column whose variant field is a wrap of
    /// its payload: ``(c: (a: 1, b: `none(unit)) ▷ const, d: x + 1)``.
    #[test]
    fn a_record_constant_holding_a_variant_is_a_field() {
        let entry = |name: &str, value: Expr| RecordEntry::new(name, Occurrence::mint(), value);
        let literal = Expr::new(TypedExprNode::Record(vec![
            entry("a", Expr::lit(Lit::Int(1))),
            entry(
                "b",
                Expr::variant_ctor("none", Occurrence::mint(), Expr::lit(Lit::Unit)),
            ),
        ]));
        let record_ty = Type::Record(vec![
            ("a".into(), Type::Base(BaseType::Int)),
            ("b".into(), option_type()),
        ]);
        let record = record_of_extents(vec![("a", int()), ("b", option_extent())]);
        let constant = Expr::apply(literal, Expr::builtin(Builtin::Const))
            .with_ty(Type::fun(Type::Base(BaseType::Int), record_ty.clone()));
        let chain = vec![zip_record(vec![
            ("c", constant),
            ("d", arith(ArithmeticKind::Add, 1)),
        ])];
        let fused = fuse_typed(&chain, &int(), &[(record_ty, record)]).expect("a record constant");
        let out = fused.program.eval(&ColumnValue::Ints(vec![5, 6]));
        let c = field_of(&out, "c");
        assert_eq!(field_of(c, "a"), &ColumnValue::Ints(vec![1, 1]));
        let none = UnionArm::new(vec![0, 1], ColumnValue::Units(2));
        assert_eq!(
            field_of(c, "b"),
            &ColumnValue::Union(TagMap::from_arms(vec![(tag("none"), none)]))
        );
        assert_eq!(field_of(&out, "d"), &ColumnValue::Ints(vec![6, 7]));
    }

    /// An empty input yields an empty union column with the wrapped arm.
    #[test]
    fn a_wrap_over_no_rows_is_an_empty_union_column() {
        let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
        let fused = fuse_options(&chain, &int()).expect("an operation and a wrap");
        let some = UnionArm::new(Vec::new(), ColumnValue::Ints(Vec::new()));
        assert_eq!(
            fused.program.eval(&ColumnValue::Ints(Vec::new())),
            ColumnValue::Union(TagMap::from_arms(vec![(tag("some"), some)]))
        );
    }

    /// The prefix ends before a wrap whose union is unknown, lacks the tag, or has an arm that
    /// holds a collection, which is a union of tiles rather than a column.
    #[test]
    fn the_prefix_ends_before_a_wrap_with_no_column() {
        let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
        assert_eq!(
            fuse_prefix(&chain, &int(), &|_| None).map(|f| f.consumed),
            Some(1)
        );
        let other = vec![arith(ArithmeticKind::Add, 1), wrap("other")];
        assert_eq!(fuse_options(&other, &int()).map(|f| f.consumed), Some(1));
        let with_a_collection = Extent::Union(TagMap::from_arms(vec![
            (tag("none"), Extent::Base(BaseType::Unit)),
            (
                tag("some"),
                Extent::Function {
                    domain: Box::new(Extent::Base(BaseType::UInt)),
                    codomain: Box::new(int()),
                },
            ),
        ]));
        let consumed =
            fuse_prefix(&chain, &int(), &|_| Some(with_a_collection.clone())).map(|f| f.consumed);
        assert_eq!(consumed, Some(1));
    }

    /// A wrap of a union field copied from the input holds the copied column as its payload:
    /// ``p.b ≫ variant_wrap(`w)`` over 2,500 rows.
    #[test]
    fn a_wrap_of_a_copied_union_holds_the_copy() {
        let input = record_of_extents(vec![("a", int()), ("b", option_extent())]);
        let w_ty = Type::variant(vec![(tag("w"), option_type())]);
        let w = Extent::Union(TagMap::from_arms(vec![(tag("w"), option_extent())]));
        let chain = vec![
            Expr::proj_field("b"),
            wrap_into("w", option_type(), w_ty.clone()),
        ];
        let fused = fuse_typed(&chain, &input, &[(w_ty, w)]).expect("a projection and a wrap");
        let n = 2_500;
        let options: Vec<Value> = (0..n)
            .map(|i| Value::Union {
                tag: tag(if i % 3 == 0 { "none" } else { "some" }),
                inner: Box::new(if i % 3 == 0 {
                    Value::Unit
                } else {
                    Value::Int(i)
                }),
            })
            .collect();
        let column = ColumnValue::Records(HashMap::from([
            ("a".into(), ColumnValue::Ints((0..n).collect())),
            (
                "b".into(),
                ColumnValue::from_values(options.clone(), &option_extent()),
            ),
        ]));
        let out = fused.program.eval(&column);
        let ColumnValue::Union(arms) = &out else {
            panic!("expected a union column, got {out:?}")
        };
        let arm = arms.get(&tag("w")).expect("the `w` arm");
        assert_eq!(arm.rows(), (0..n as usize).collect::<Vec<_>>());
        let payload = arm.values();
        assert_eq!(
            (0..n as usize)
                .map(|i| payload.index_at(i))
                .collect::<Vec<_>>(),
            options
        );
    }

    /// Two variants of one tag compare their payloads, so the program builds no union:
    /// ``(x + 1 ≫ variant_wrap(`some), `some(3) ▷ const) ▷ zip ≫ eq`` is `x + 1 == 3`.
    #[test]
    fn variants_of_one_tag_compare_their_payloads() {
        let some_plus_one = Expr::compose(vec![arith(ArithmeticKind::Add, 1), wrap("some")]);
        for (kind, want) in [
            (CompareKind::Equals, vec![false, true, false]),
            (CompareKind::NotEquals, vec![true, false, true]),
        ] {
            let chain = vec![
                zip(vec![some_plus_one.clone(), some(3)]),
                binop(BinOpKind::Compare(kind)),
            ];
            let fused = fuse_options(&chain, &int()).expect("the payloads are compared");
            assert_eq!(fused.consumed, 2);
            assert!(
                !fused
                    .program
                    .instrs
                    .iter()
                    .any(|instr| instr.op.is_constructor()),
                "no union is built: {}",
                fused.program
            );
            assert_eq!(
                bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3]))),
                want
            );
        }
    }

    /// Two variants of different tags differ at every row, so the comparison is decided while
    /// parsing and has no program: the prefix ends at the `zip` before it, under `==` and `!=`,
    /// alone or as a field that decides a record comparison. In the record, the deciding field `z`
    /// is compared after the computed field `b`.
    #[test]
    fn variants_of_different_tags_decide_the_comparison() {
        let bare = zip(vec![wrap("some"), none()]);
        let in_records = zip(vec![
            zip_record(vec![("b", id()), ("z", wrap("some"))]),
            zip_record(vec![("b", constant(2)), ("z", none())]),
        ]);
        for product in [bare, in_records] {
            for kind in [CompareKind::Equals, CompareKind::NotEquals] {
                let chain = vec![product.clone(), binop(BinOpKind::Compare(kind))];
                let fused = fuse_options(&chain, &int()).expect("the zip builds the product");
                assert_eq!(fused.consumed, 1, "{kind:?}");
            }
        }
    }

    /// A field decided as the join's identity drops out, `true` under `==` and `false` under `!=`:
    /// ``(a: `none(unit), b: x + 1) == (a: `none(unit), b: 3)`` compares `b` alone, since two
    /// `unit` payloads are equal at every row.
    #[test]
    fn a_field_decided_as_the_identity_drops_out() {
        for (kind, want) in [
            (CompareKind::Equals, vec![false, true, false]),
            (CompareKind::NotEquals, vec![true, false, true]),
        ] {
            let chain = vec![
                zip(vec![
                    zip_record(vec![("a", none()), ("b", arith(ArithmeticKind::Add, 1))]),
                    zip_record(vec![("a", none()), ("b", constant(3))]),
                ]),
                binop(BinOpKind::Compare(kind)),
            ];
            let fused = fuse_options(&chain, &int()).expect("`b` is compared");
            assert_eq!(fused.consumed, 2, "{kind:?}");
            let got = bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])));
            assert_eq!(got, want, "{kind:?}");
        }
    }

    /// A comparison recurses through nested variants and into a record payload: ``x ≫
    /// variant_wrap(`inner) ≫ variant_wrap(`outer)`` against `` `outer(`inner(3)) `` is `x == 3`,
    /// against `` `outer(`other(unit)) `` it is decided, and ``(a: x + 1, b: x) ≫
    /// variant_wrap(`r)`` against `` `r((a: 3, b: 2)) `` compares both fields.
    #[test]
    fn a_comparison_recurses_through_variant_payloads() {
        let int_ty = || Type::Base(BaseType::Int);
        let inner_ty = Type::variant(vec![
            (tag("inner"), int_ty()),
            (tag("other"), Type::Base(BaseType::Unit)),
        ]);
        let outer_ty = Type::variant(vec![(tag("outer"), inner_ty.clone())]);
        let inner = Extent::Union(TagMap::from_arms(vec![
            (tag("inner"), int()),
            (tag("other"), Extent::Base(BaseType::Unit)),
        ]));
        let outer = Extent::Union(TagMap::from_arms(vec![(tag("outer"), inner.clone())]));
        let types = [(inner_ty.clone(), inner), (outer_ty.clone(), outer)];
        let nested = Expr::compose(vec![
            wrap_into("inner", int_ty(), inner_ty.clone()),
            wrap_into("outer", inner_ty, outer_ty.clone()),
        ]);
        let outer_of = |name: &str, payload: Expr| {
            let inner = Expr::variant_ctor(name, Occurrence::mint(), payload);
            let outer = Expr::variant_ctor("outer", Occurrence::mint(), inner);
            Expr::apply(outer, Expr::builtin(Builtin::Const))
                .with_ty(Type::fun(int_ty(), outer_ty.clone()))
        };
        let eq = || binop(BinOpKind::Compare(CompareKind::Equals));
        let three = outer_of("inner", Expr::lit(Lit::Int(3)));
        let computed = vec![zip(vec![nested.clone(), three]), eq()];
        let fused = fuse_typed(&computed, &int(), &types).expect("the payloads are compared");
        assert_eq!(fused.consumed, 2);
        assert_eq!(
            bools(fused.program.eval(&ColumnValue::Ints(vec![2, 3, 4]))),
            vec![false, true, false]
        );
        let other = outer_of("other", Expr::lit(Lit::Unit));
        let decided = vec![zip(vec![nested, other]), eq()];
        let consumed = fuse_typed(&decided, &int(), &types).map(|fused| fused.consumed);
        assert_eq!(consumed, Some(1), "the inner tags differ");

        let pair_ty = Type::Record(vec![("a".into(), int_ty()), ("b".into(), int_ty())]);
        let r_ty = Type::variant(vec![(tag("r"), pair_ty.clone())]);
        let pair = record_of_extents(vec![("a", int()), ("b", int())]);
        let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), pair)]));
        let product = Expr::compose(vec![
            zip_record(vec![("a", arith(ArithmeticKind::Add, 1)), ("b", id())]),
            wrap_into("r", pair_ty, r_ty.clone()),
        ]);
        let entry =
            |name: &str, n: i64| RecordEntry::new(name, Occurrence::mint(), Expr::lit(Lit::Int(n)));
        let literal = Expr::new(TypedExprNode::Record(vec![entry("a", 3), entry("b", 2)]));
        let constant = Expr::apply(
            Expr::variant_ctor("r", Occurrence::mint(), literal),
            Expr::builtin(Builtin::Const),
        )
        .with_ty(Type::fun(int_ty(), r_ty.clone()));
        let chain = vec![zip(vec![product, constant]), eq()];
        let fused = fuse_typed(&chain, &int(), &[(r_ty, r)]).expect("both fields are compared");
        assert!(
            !fused
                .program
                .instrs
                .iter()
                .any(|instr| instr.op.is_constructor()),
            "no record or union is built: {}",
            fused.program
        );
        assert_eq!(
            bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3]))),
            vec![false, true, false]
        );
    }

    /// The fused and unfused comparisons agree on a record payload whose column carries a field its
    /// type does not name. The input is typed `{a: Int}`, but its column carries a surplus field
    /// `w`, as width subtyping can leave one. ``p ≫ variant_wrap(`r)`` against `` `r((a: 3)) ``
    /// compares `a` alone: fused over the fields the extent names, unfused over the fields both
    /// values carry. The same union nested in a record field compares the same way unfused.
    #[test]
    fn a_surplus_payload_field_is_compared_by_neither_path() {
        let a_ty = Type::Record(vec![("a".into(), Type::Base(BaseType::Int))]);
        let r_ty = Type::variant(vec![(tag("r"), a_ty.clone())]);
        let a = record_of_extents(vec![("a", int())]);
        let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), a.clone())]));
        let literal = Expr::new(TypedExprNode::Record(vec![RecordEntry::new(
            "a",
            Occurrence::mint(),
            Expr::lit(Lit::Int(3)),
        )]));
        let three = Expr::apply(
            Expr::variant_ctor("r", Occurrence::mint(), literal),
            Expr::builtin(Builtin::Const),
        )
        .with_ty(Type::fun(a_ty.clone(), r_ty.clone()));
        let rows = 4;
        let records = |a: Vec<i64>, w: Option<Vec<i64>>| {
            let mut fields = HashMap::from([(SmolStr::from("a"), ColumnValue::Ints(a))]);
            if let Some(w) = w {
                fields.insert("w".into(), ColumnValue::Ints(w));
            }
            ColumnValue::Records(fields)
        };
        let wide = records(vec![1, 3, 5, 3], Some(vec![7; rows]));
        let union = |payloads| {
            let arm = UnionArm::new((0..rows).collect(), payloads);
            ColumnValue::Union(TagMap::from_arms(vec![(tag("r"), arm)]))
        };
        for (kind, want) in [
            (CompareKind::Equals, vec![false, true, false, true]),
            (CompareKind::NotEquals, vec![true, false, true, false]),
        ] {
            let op = BinOpKind::Compare(kind);
            let chain = vec![
                zip(vec![
                    wrap_into("r", a_ty.clone(), r_ty.clone()),
                    three.clone(),
                ]),
                binop(op),
            ];
            let fused = fuse_typed(&chain, &a, &[(r_ty.clone(), r.clone())])
                .expect("the payloads are compared");
            assert_eq!(bools(fused.program.eval(&wide)), want, "fused {kind:?}");
            let threes = union(records(vec![3; rows], None));
            let unfused = apply_binop_column(op.into(), &union(wide.clone()), &threes);
            assert_eq!(bools(unfused), want, "unfused {kind:?}");
            let field = |column| ColumnValue::Records(HashMap::from([("u".into(), column)]));
            let nested = apply_binop_column(op.into(), &field(union(wide.clone())), &field(threes));
            assert_eq!(bools(nested), want, "unfused in a record field {kind:?}");
        }
    }

    /// `lambda_elim`'s first-match gates over `n` conditions and a final guard of `true`
    /// (`synthesize_arm_predicate`): arm `i` holds `𝑔ᵢ ∧ ¬𝑔₀ ∧ … ∧ ¬𝑔ᵢ₋₁`.
    fn first_match(formulas: &mut Formulas, n: usize) -> Vec<usize> {
        let mut guards: Vec<usize> = (0..n).map(|_| formulas.push(Node::Atom)).collect();
        guards.push(formulas.push(Node::Known(true)));
        let negated: Vec<usize> = guards
            .iter()
            .map(|&g| formulas.push(Node::Not(g)))
            .collect();
        guards
            .iter()
            .enumerate()
            .map(|(i, &guard)| {
                negated[..i]
                    .iter()
                    .fold(guard, |gate, &not| formulas.push(Node::And(gate, not)))
            })
            .collect()
    }

    /// The first-match gates of a 20-way `elif` split the rows within the budget: each branch is
    /// decided once one condition holds, so the search reaches one leaf per arm, not 2²⁰.
    #[test]
    fn first_match_gates_split_the_rows() {
        for n in [0, 1, 20] {
            let mut formulas = Formulas::default();
            let gates = first_match(&mut formulas, n);
            assert!(gates_split_the_rows(&formulas, &gates), "{n} conditions");
        }
    }

    /// Gates that overlap, or that leave a row in no arm, do not split the rows.
    #[test]
    fn overlapping_or_uncovering_gates_do_not_split_the_rows() {
        let mut formulas = Formulas::default();
        let a = formulas.push(Node::Atom);
        let b = formulas.push(Node::Atom);
        let a_or_b = formulas.push(Node::Or(a, b));
        let a_and_b = formulas.push(Node::And(a, b));
        let not_a = formulas.push(Node::Not(a));
        let never = formulas.push(Node::Known(false));
        assert!(
            !gates_split_the_rows(&formulas, &[a, a_or_b]),
            "a row where `a` holds is in both"
        );
        assert!(
            !gates_split_the_rows(&formulas, &[a_and_b, not_a]),
            "a row where only `a` holds is in neither"
        );
        assert!(
            !gates_split_the_rows(&formulas, &[never]),
            "no row is in an arm"
        );
        assert!(gates_split_the_rows(&formulas, &[a, not_a]));
    }

    /// A split that needs more branches than the budget is not proved, so its conditional is not
    /// fused: the parity of thirteen atoms and its negation decide only once every atom is
    /// assigned, which takes 2¹³ leaves.
    #[test]
    fn a_split_beyond_the_budget_is_not_proved() {
        let parity = |n: Slot| {
            let mut formulas = Formulas::default();
            let mut acc = formulas.push(Node::Atom);
            for _ in 1..n {
                let b = formulas.push(Node::Atom);
                let not_acc = formulas.push(Node::Not(acc));
                let not_b = formulas.push(Node::Not(b));
                let left = formulas.push(Node::And(acc, not_b));
                let right = formulas.push(Node::And(not_acc, b));
                acc = formulas.push(Node::Or(left, right));
            }
            let odd = formulas.push(Node::Not(acc));
            (formulas, [acc, odd])
        };
        let (small, gates) = parity(6);
        assert!(gates_split_the_rows(&small, &gates));
        let (large, gates) = parity(13);
        assert!(!gates_split_the_rows(&large, &gates));
    }

    /// ``(𝑔 ▷ filter_values) ≫ 𝑒`` over `x`, typed `Int ⇒ 𝑇`.
    fn filtered(gate: Expr, then: Expr, codomain: Type) -> Expr {
        let filter = Expr::apply(gate, Expr::builtin(Builtin::FilterValues));
        Expr::compose(vec![filter, then]).with_ty(Type::fun(Type::Base(BaseType::Int), codomain))
    }

    /// `𝑎₁ ⊔ … ⊔ 𝑎ₙ`, typed `Int ⇒ 𝑇`.
    fn joined(arms: Vec<Expr>, codomain: Type) -> Expr {
        Expr::disjoint_join(arms).with_ty(Type::fun(Type::Base(BaseType::Int), codomain))
    }

    /// A conditional over 2,500 rows answers each row from its arm, merged in row order across
    /// blocks, and runs `//` only on its arm's rows: ``(x > 1000 ▷ filter_values ≫ 1000 // (x -
    /// 1000)) ⊔ (x > 1000 ≫ not_fn ▷ filter_values ≫ 0 - x)``, where `1000 // 0` would panic.
    #[test]
    fn a_conditional_runs_each_arm_on_its_rows() {
        let int_ty = || Type::Base(BaseType::Int);
        let over = compare(CompareKind::Greater, 1000);
        let divide = Expr::compose(vec![
            zip(vec![constant(1000), arith(ArithmeticKind::Sub, 1000)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::FloorDiv)),
        ]);
        let negate = Expr::compose(vec![
            zip(vec![constant(0), id()]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Sub)),
        ]);
        let not_over = Expr::compose(vec![over.clone(), Expr::builtin(Builtin::NotFn)]);
        let chain = vec![joined(
            vec![
                filtered(over, divide, int_ty()),
                filtered(not_over, negate, int_ty()),
            ],
            int_ty(),
        )];
        let fused =
            fuse_typed(&chain, &int(), &[(int_ty(), int())]).expect("the gates split the rows");
        assert_eq!(fused.consumed, 1);
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        let want = (0..n)
            .map(|x| {
                if x > 1000 {
                    1000_i64.div_euclid(x - 1000)
                } else {
                    -x
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(out, ColumnValue::Ints(want), "{}", fused.program);
    }

    /// A conditional whose arms build variants is a constructor yielding one union column with
    /// each arm's tag: ``(x > 1 ▷ filter_values ≫ variant_wrap(`some)) ⊔ (x > 1 ≫ not_fn ▷
    /// filter_values ≫ `none(unit) ▷ const)`` over 2,500 rows.
    #[test]
    fn a_conditional_building_variants_merges_their_tags() {
        let over = compare(CompareKind::Greater, 1);
        let not_over = Expr::compose(vec![over.clone(), Expr::builtin(Builtin::NotFn)]);
        let chain = vec![joined(
            vec![
                filtered(over, wrap("some"), option_type()),
                filtered(not_over, none(), option_type()),
            ],
            option_type(),
        )];
        let fused = fuse_options(&chain, &int()).expect("the gates split the rows");
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        let want: Vec<Value> = (0..n)
            .map(|x| match x > 1 {
                true => Value::Union {
                    tag: tag("some"),
                    inner: Box::new(Value::Int(x)),
                },
                false => Value::Union {
                    tag: tag("none"),
                    inner: Box::new(Value::Unit),
                },
            })
            .collect();
        let got: Vec<Value> = (0..n as usize).map(|i| out.index_at(i)).collect();
        assert_eq!(got, want, "{}", fused.program);
    }

    /// A `match` over a union read from the input selects each arm's rows by tag, reading the
    /// payloads of a block as one run: ``(variant_project(`some) ≫ id * 2) ⊔
    /// (variant_project(`none) ≫ 0 ▷ const)`` over 2,500 rows that alternate between the tags.
    #[test]
    fn a_match_selects_each_arm_by_tag() {
        let int_ty = || Type::Base(BaseType::Int);
        let project = |name: &str, payload: Type| {
            Expr::builtin(Builtin::VariantProject(tag(name)))
                .with_ty(Type::fun(option_type(), payload))
        };
        let chain = vec![joined(
            vec![
                Expr::compose(vec![
                    project("some", int_ty()),
                    arith(ArithmeticKind::Mul, 2),
                ]),
                Expr::compose(vec![
                    project("none", Type::Base(BaseType::Unit)),
                    constant(0),
                ]),
            ],
            int_ty(),
        )];
        let n = 2_500;
        let options: Vec<Value> = (0..n)
            .map(|i| Value::Union {
                tag: tag(if i % 3 == 0 { "none" } else { "some" }),
                inner: Box::new(if i % 3 == 0 {
                    Value::Unit
                } else {
                    Value::Int(i)
                }),
            })
            .collect();
        let input = ColumnValue::from_values(options, &option_extent());
        let fused = fuse_typed(
            &chain,
            &option_extent(),
            &[
                (int_ty(), int()),
                (Type::Base(BaseType::Unit), Extent::Base(BaseType::Unit)),
            ],
        )
        .expect("the arms name every tag");
        let want = (0..n)
            .map(|i| if i % 3 == 0 { 0 } else { i * 2 })
            .collect::<Vec<_>>();
        assert_eq!(
            fused.program.eval(&input),
            ColumnValue::Ints(want),
            "{}",
            fused.program
        );
        let one_arm = vec![joined(
            vec![Expr::compose(vec![
                project("some", int_ty()),
                arith(ArithmeticKind::Mul, 2),
            ])],
            int_ty(),
        )];
        let types = [(int_ty(), int())];
        assert!(
            fuse_typed(&one_arm, &option_extent(), &types).is_none(),
            "a `match` naming one of two tags leaves rows in no arm"
        );
    }

    /// ``variant_project(`name) : {`none | `some{Int}} ⇒ payload``.
    fn project_option(name: &str, payload: Type) -> Expr {
        Expr::builtin(Builtin::VariantProject(tag(name))).with_ty(Type::fun(option_type(), payload))
    }

    /// The types a conditional over options reads, with their extents.
    fn option_types() -> Vec<(Type, Extent)> {
        vec![
            (Type::Base(BaseType::Int), int()),
            (Type::Base(BaseType::Unit), Extent::Base(BaseType::Unit)),
            (option_type(), option_extent()),
        ]
    }

    /// `𝑥 ≫ not_fn`.
    fn negated(gate: Expr) -> Expr {
        Expr::compose(vec![gate, Expr::builtin(Builtin::NotFn)])
    }

    /// An `if` inside an arm opens an arm inside that arm, which reads `x` narrowed twice:
    /// ``(x > 1000 ▷ filter_values ≫ ((x > 2000 ▷ filter_values ≫ x * 2) ⊔ (x > 2000 ≫ not_fn ▷
    /// filter_values ≫ x * 3))) ⊔ (x > 1000 ≫ not_fn ▷ filter_values ≫ 0 - x)`` over 2,500 rows.
    #[test]
    fn an_if_inside_an_arm_opens_a_nested_arm() {
        let int_ty = || Type::Base(BaseType::Int);
        let (over_1000, over_2000) = (
            compare(CompareKind::Greater, 1000),
            compare(CompareKind::Greater, 2000),
        );
        let inner = joined(
            vec![
                filtered(over_2000.clone(), arith(ArithmeticKind::Mul, 2), int_ty()),
                filtered(negated(over_2000), arith(ArithmeticKind::Mul, 3), int_ty()),
            ],
            int_ty(),
        );
        let negate = Expr::compose(vec![
            zip(vec![constant(0), id()]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Sub)),
        ]);
        let chain = vec![joined(
            vec![
                filtered(over_1000.clone(), inner, int_ty()),
                filtered(negated(over_1000), negate, int_ty()),
            ],
            int_ty(),
        )];
        let fused = fuse_typed(&chain, &int(), &[(int_ty(), int())]).expect("both joins split");
        let n = 2_500;
        let want = (0..n)
            .map(|x| match x {
                x if x > 2000 => x * 2,
                x if x > 1000 => x * 3,
                x => -x,
            })
            .collect::<Vec<_>>();
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        assert_eq!(out, ColumnValue::Ints(want), "{}", fused.program);
        let empty = fused.program.eval(&ColumnValue::Ints(Vec::new()));
        assert_eq!(empty, ColumnValue::Ints(Vec::new()), "an empty input");
    }

    /// A `match` inside an `if` arm reads the union narrowed to the arm: over `{k: Int, o: {`none |
    /// `some{Int}}}`, ``(k > 0 ▷ filter_values ≫ .o ≫ ((variant_project(`some) ≫ id * 2) ⊔
    /// (variant_project(`none) ≫ 7 ▷ const))) ⊔ (k > 0 ≫ not_fn ▷ filter_values ≫ .k)``.
    #[test]
    fn a_match_inside_an_if_arm_reads_the_narrowed_union() {
        let int_ty = || Type::Base(BaseType::Int);
        let input = record_of_extents(vec![("k", int()), ("o", option_extent())]);
        let k_over_0 = Expr::compose(vec![
            zip(vec![Expr::proj_field("k"), constant(0)]),
            binop(BinOpKind::Compare(CompareKind::Greater)),
        ]);
        let matched = joined(
            vec![
                Expr::compose(vec![
                    project_option("some", int_ty()),
                    arith(ArithmeticKind::Mul, 2),
                ]),
                Expr::compose(vec![
                    project_option("none", Type::Base(BaseType::Unit)),
                    constant(7),
                ]),
            ],
            int_ty(),
        );
        let chain = vec![joined(
            vec![
                filtered(
                    k_over_0.clone(),
                    Expr::compose(vec![Expr::proj_field("o"), matched]),
                    int_ty(),
                ),
                filtered(negated(k_over_0), Expr::proj_field("k"), int_ty()),
            ],
            int_ty(),
        )];
        let fused =
            fuse_typed(&chain, &input, &option_types()).expect("both conditionals split the rows");
        let n = 2_500;
        let k: Vec<i64> = (0..n).map(|i| if i % 4 == 0 { -i } else { i }).collect();
        let o: Vec<Value> = (0..n)
            .map(|i| Value::Union {
                tag: tag(if i % 3 == 0 { "none" } else { "some" }),
                inner: Box::new(if i % 3 == 0 {
                    Value::Unit
                } else {
                    Value::Int(i)
                }),
            })
            .collect();
        let column = ColumnValue::Records(HashMap::from([
            ("k".into(), ColumnValue::Ints(k.clone())),
            ("o".into(), ColumnValue::from_values(o, &option_extent())),
        ]));
        let want = (0..n)
            .map(|i| match (k[i as usize] > 0, i % 3 == 0) {
                (false, _) => k[i as usize],
                (true, true) => 7,
                (true, false) => i * 2,
            })
            .collect::<Vec<_>>();
        let out = fused.program.eval(&column);
        assert_eq!(out, ColumnValue::Ints(want), "{}", fused.program);
    }

    /// A conditional of records merges field by field, and one of `Unit` merges to a `Units`
    /// column. An arm whose record is wider than the join's type has no program: over
    /// `{a: Int, b: Int}`, ``(a > 0 ▷ filter_values ≫ id) ⊔ (a > 0 ≫ not_fn ▷ filter_values ≫ (a:
    /// 0) ▷ const)`` typed `{a: Int}`.
    #[test]
    fn a_conditional_of_records_merges_field_by_field() {
        let pair_ty = Type::Record(vec![
            ("a".into(), Type::Base(BaseType::Int)),
            ("b".into(), Type::Base(BaseType::Int)),
        ]);
        let pair = record_of_extents(vec![("a", int()), ("b", int())]);
        let over = compare(CompareKind::Greater, 1);
        let chain = vec![joined(
            vec![
                filtered(
                    over.clone(),
                    zip_record(vec![("a", id()), ("b", arith(ArithmeticKind::Mul, 2))]),
                    pair_ty.clone(),
                ),
                filtered(
                    negated(over.clone()),
                    zip_record(vec![("a", constant(0)), ("b", id())]),
                    pair_ty.clone(),
                ),
            ],
            pair_ty.clone(),
        )];
        let fused = fuse_typed(&chain, &int(), &[(pair_ty, pair)]).expect("the gates split");
        let out = fused.program.eval(&ColumnValue::Ints(vec![0, 5, 1, 9]));
        assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(vec![0, 5, 0, 9]));
        assert_eq!(field_of(&out, "b"), &ColumnValue::Ints(vec![0, 10, 1, 18]));

        let unit = || Type::Base(BaseType::Unit);
        let unit_const = || {
            Expr::apply(Expr::lit(Lit::Unit), Expr::builtin(Builtin::Const))
                .with_ty(Type::fun(Type::Base(BaseType::Int), unit()))
        };
        let units = vec![joined(
            vec![
                filtered(over.clone(), unit_const(), unit()),
                filtered(negated(over.clone()), unit_const(), unit()),
            ],
            unit(),
        )];
        let types = [(unit(), Extent::Base(BaseType::Unit))];
        let fused = fuse_typed(&units, &int(), &types).expect("the gates split");
        let out = fused.program.eval(&ColumnValue::Ints(vec![0, 5, 1]));
        assert_eq!(out, ColumnValue::Units(3));

        let a_ty = Type::Record(vec![("a".into(), Type::Base(BaseType::Int))]);
        let a = record_of_extents(vec![("a", int())]);
        let a_over = Expr::compose(vec![
            zip(vec![Expr::proj_field("a"), constant(0)]),
            binop(BinOpKind::Compare(CompareKind::Greater)),
        ]);
        let literal = Expr::new(TypedExprNode::Record(vec![RecordEntry::new(
            "a",
            Occurrence::mint(),
            Expr::lit(Lit::Int(0)),
        )]));
        let zero = Expr::apply(literal, Expr::builtin(Builtin::Const))
            .with_ty(Type::fun(a_ty.clone(), a_ty.clone()));
        let wider = vec![joined(
            vec![
                filtered(a_over.clone(), id(), a_ty.clone()),
                filtered(negated(a_over), zero, a_ty.clone()),
            ],
            a_ty.clone(),
        )];
        let input = record_of_extents(vec![("a", int()), ("b", int())]);
        let consumed = fuse_typed(&wider, &input, &[(a_ty, a)]).map(|fused| fused.consumed);
        assert_eq!(
            consumed, None,
            "the first arm carries `b`, which the join's type lacks"
        );
    }

    /// A tag the union column does not carry selects no row: a column holding only `` `some ``
    /// rows, matched by ``(variant_project(`some) ≫ id * 2) ⊔ (variant_project(`none) ≫ 7 ▷
    /// const)``, reads its `` `none `` payload from the instruction's empty column.
    #[test]
    fn a_tag_the_column_lacks_selects_no_row() {
        let int_ty = || Type::Base(BaseType::Int);
        let chain = vec![joined(
            vec![
                Expr::compose(vec![
                    project_option("some", int_ty()),
                    arith(ArithmeticKind::Mul, 2),
                ]),
                Expr::compose(vec![
                    project_option("none", Type::Base(BaseType::Unit)),
                    constant(7),
                ]),
            ],
            int_ty(),
        )];
        let fused =
            fuse_typed(&chain, &option_extent(), &option_types()).expect("the arms name every tag");
        let n = 2_500;
        let some = UnionArm::new((0..n).collect(), ColumnValue::Ints((0..n as i64).collect()));
        let column = ColumnValue::Union(TagMap::from_arms(vec![(tag("some"), some)]));
        let want = (0..n as i64).map(|i| i * 2).collect::<Vec<_>>();
        assert_eq!(fused.program.eval(&column), ColumnValue::Ints(want));
    }

    /// An operand that pairs the element with the payload, ``(.t, .w ≫ variant_project(`some)) ▷
    /// zip ≫ add``, holds the rows of its tag and reads both: over `{t: Int, w: {`none |
    /// `some{Int}}}`, matched together with ``.w ≫ variant_project(`none) ≫ 0 ▷ const``.
    #[test]
    fn an_operand_pairs_the_element_with_the_payload() {
        let int_ty = || Type::Base(BaseType::Int);
        let input = record_of_extents(vec![("t", int()), ("w", option_extent())]);
        let some_plus_t = Expr::compose(vec![
            zip(vec![
                Expr::proj_field("t"),
                Expr::compose(vec![
                    Expr::proj_field("w"),
                    project_option("some", int_ty()),
                ]),
            ]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ]);
        let none = Expr::compose(vec![
            Expr::proj_field("w"),
            project_option("none", Type::Base(BaseType::Unit)),
            constant(0),
        ]);
        let chain = vec![joined(vec![some_plus_t, none], int_ty())];
        let fused =
            fuse_typed(&chain, &input, &option_types()).expect("the arms name every tag of `w`");
        let w: Vec<Value> = (0..4)
            .map(|i| Value::Union {
                tag: tag(if i % 2 == 0 { "some" } else { "none" }),
                inner: Box::new(if i % 2 == 0 {
                    Value::Int(i * 10)
                } else {
                    Value::Unit
                }),
            })
            .collect();
        let column = ColumnValue::Records(HashMap::from([
            ("t".into(), ColumnValue::Ints(vec![1, 2, 3, 4])),
            ("w".into(), ColumnValue::from_values(w, &option_extent())),
        ]));
        assert_eq!(
            fused.program.eval(&column),
            ColumnValue::Ints(vec![1, 0, 23, 0]),
            "{}",
            fused.program
        );
    }

    /// A `match` on a variant built in the chain reads as the arm naming its tag, with no arm or
    /// `Case`: ``x ≫ variant_wrap(`some) ≫ ((variant_project(`some) ≫ id * 2) ⊔
    /// (variant_project(`none) ≫ 7 ▷ const))``.
    #[test]
    fn a_match_on_a_known_tag_reads_as_its_arm() {
        let int_ty = || Type::Base(BaseType::Int);
        let chain = vec![
            wrap("some"),
            joined(
                vec![
                    Expr::compose(vec![
                        project_option("some", int_ty()),
                        arith(ArithmeticKind::Mul, 2),
                    ]),
                    Expr::compose(vec![
                        project_option("none", Type::Base(BaseType::Unit)),
                        constant(7),
                    ]),
                ],
                int_ty(),
            ),
        ];
        let fused = fuse_typed(&chain, &int(), &option_types()).expect("the tag is known");
        assert!(
            !fused
                .program
                .instrs
                .iter()
                .any(|instr| matches!(instr.op, Op::Arm { .. } | Op::Case { .. })),
            "{}",
            fused.program
        );
        assert_eq!(
            fused.program.eval(&ColumnValue::Ints(vec![1, 2])),
            ColumnValue::Ints(vec![2, 4])
        );
    }

    /// A join is not fused when its gates mix `Holds` and `Tag`, name one tag twice, or read two
    /// unions.
    #[test]
    fn a_join_whose_gates_do_not_split_by_one_rule_has_no_program() {
        let int_ty = || Type::Base(BaseType::Int);
        let input = record_of_extents(vec![
            ("k", int()),
            ("v", option_extent()),
            ("w", option_extent()),
        ]);
        let arm = |field: &str, name: &str, then: Expr| {
            let payload = if name == "some" {
                int_ty()
            } else {
                Type::Base(BaseType::Unit)
            };
            Expr::compose(vec![
                Expr::proj_field(field),
                project_option(name, payload),
                then,
            ])
        };
        let k_over_0 = Expr::compose(vec![
            zip(vec![Expr::proj_field("k"), constant(0)]),
            binop(BinOpKind::Compare(CompareKind::Greater)),
        ]);
        let cases = [
            (
                "mixed gates",
                vec![
                    filtered(k_over_0, constant(1), int_ty()),
                    arm("v", "none", constant(0)),
                ],
            ),
            (
                "one tag twice",
                vec![
                    arm("v", "some", constant(1)),
                    arm("v", "some", constant(2)),
                    arm("v", "none", constant(0)),
                ],
            ),
            (
                "two unions",
                vec![arm("v", "some", constant(1)), arm("w", "none", constant(0))],
            ),
        ];
        for (name, operands) in cases {
            let chain = vec![joined(operands, int_ty())];
            assert!(
                fuse_typed(&chain, &input, &option_types()).is_none(),
                "{name}"
            );
        }
    }

    /// The scope check rejects an instruction that reads another scope, and a `Narrow` outside an
    /// arm.
    #[test]
    fn the_scope_check_rejects_a_read_across_scopes() {
        let gt = BinOpKind::Compare(CompareKind::Greater).into();
        let mut program = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Const(Value::Int(0)),
            Op::Bin(gt, 0, 1),
            Op::Arm {
                gate: Gate::Holds(2),
            },
            Op::Narrow { from: 0 },
            Op::Un(UnaryOpKind::Neg, 4),
            Op::Case {
                arms: vec![(3, 5)],
                constructs: false,
            },
        ]);
        program.instrs[4].scope = 3;
        program.instrs[5].scope = 3;
        assert!(program.scopes_are_consistent(), "{program}");
        program.instrs[5].op = Op::Un(UnaryOpKind::Neg, 0);
        assert!(
            !program.scopes_are_consistent(),
            "a root slot read in an arm"
        );
        program.instrs[5].op = Op::Un(UnaryOpKind::Neg, 4);
        program.instrs[4].scope = ROOT;
        assert!(
            !program.scopes_are_consistent(),
            "a `Narrow` in the root scope"
        );
    }

    /// An operation written twice is computed once: `(x + 1, x + 1)`, written as two arms, computes
    /// `x + 1` once and holds the constant `1` once.
    #[test]
    fn equal_computations_share_a_slot() {
        let chain = vec![zip(vec![
            arith(ArithmeticKind::Add, 1),
            arith(ArithmeticKind::Add, 1),
        ])];
        let fused = fuse(&chain, &int()).expect("a product of two operations");
        assert_eq!(
            fused.program.to_string(),
            "s0 = _; s1 = 1; s2 = +(s0, s1); s3 = (_0: s2, _1: s2); => s3"
        );
        let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3]));
    }

    /// A program's result is its last instruction, so a computed value that shares an earlier
    /// slot is no result.
    #[test]
    fn a_computed_value_in_an_earlier_slot_is_no_result() {
        let no_types = |ty: &Type| panic!("no type is read, read {ty}");
        let mut parser = Parser {
            scope: ROOT,
            extent_of: &no_types,
            instrs: Vec::new(),
            slots: HashMap::new(),
            ops: 0,
        };
        let x = parser.emit(Op::Input { path: Vec::new() });
        let one = parser.emit(Op::Const(Value::Int(1)));
        let add = InterpreterBinOp::from(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let sum = parser.emit(Op::Bin(add, x, one));
        assert!(parser.root_of(&Val::Slot(sum, int())).is_some());
        assert_eq!(
            parser.emit(Op::Bin(add, x, one)),
            sum,
            "an equal operation shares"
        );
        let negated = parser.emit(Op::Un(UnaryOpKind::Neg, sum));
        assert!(parser.root_of(&Val::Slot(sum, int())).is_none());
        assert!(parser.root_of(&Val::Slot(negated, int())).is_some());
    }

    /// A computed value that two fields and an operation read is one slot, computed once and copied
    /// into each field: `(x + 1) ≫ (id, id, id * 2)`, as `simplify` leaves
    /// `[(y, y, y * 2) for y in [x + 1 for x in xs]]`.
    #[test]
    fn a_value_two_fields_name_is_computed_once() {
        let chain = vec![
            arith(ArithmeticKind::Add, 1),
            zip(vec![id(), id(), arith(ArithmeticKind::Mul, 2)]),
        ];
        let fused = fuse(&chain, &int()).unwrap();
        let adds = fused
            .program
            .instrs
            .iter()
            .filter(|instr| matches!(instr.op, Op::Bin(InterpreterBinOp::Arithmetic(_), ..)))
            .count();
        assert_eq!(adds, 2, "one `add` and one `mul`: {}", fused.program);
        let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
        assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
        assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3]));
        assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![4, 6]));
    }

    /// A product the chain goes on to read is not an output, so the reads its fields would make
    /// are not in the program: `(x, 1) ▷ zip ≫ add` is the input, the constant and the sum.
    #[test]
    fn a_product_the_chain_reads_on_leaves_no_instruction_behind() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let chain = vec![zip(vec![id(), constant(1)]), add];
        let fused = fuse(&chain, &int()).unwrap();
        assert_eq!(fused.consumed, 2);
        assert_eq!(fused.program.instrs.len(), 3, "{}", fused.program);
        assert!(
            matches!(fused.program.instrs[2].op, Op::Bin(..)),
            "{}",
            fused.program
        );
    }

    /// A prefix that ends at a product, followed by an element the parse abandons after emitting
    /// an operation, gives the program of the product alone.
    #[test]
    fn a_prefix_can_end_at_a_product() {
        let product = zip(vec![arith(ArithmeticKind::Add, 1), id()]);
        let alone = fuse(std::slice::from_ref(&product), &int()).unwrap();
        let abandoned = zip(vec![
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
            Expr::builtin(Builtin::Sum),
        ]);
        let fused = fuse(&[product, abandoned], &int()).unwrap();
        assert_eq!(fused.consumed, 1);
        assert_eq!(fused.program, alone.program);
    }

    /// Every field is evaluated over each block, so the columns agree with a single pass for
    /// lengths on and around a block.
    #[test]
    fn a_record_result_is_evaluated_block_by_block() {
        let chain = vec![zip_record(vec![
            ("plus", arith(ArithmeticKind::Add, 1)),
            ("same", id()),
            ("big", compare(CompareKind::Greater, 1000)),
            ("seven", constant(7)),
        ])];
        let fused = fuse(&chain, &int()).unwrap();
        for n in [
            0,
            1,
            BLOCK_ROWS - 1,
            BLOCK_ROWS,
            BLOCK_ROWS + 1,
            3 * BLOCK_ROWS + 37,
        ] {
            let ColumnValue::Ints(xs) = ramp(n) else {
                unreachable!()
            };
            let out = fused.program.eval(&ColumnValue::Ints(xs.clone()));
            let plus: Vec<i64> = xs.iter().map(|x| x + 1).collect();
            let big: Vec<bool> = xs.iter().map(|&x| x > 1000).collect();
            assert_eq!(field_of(&out, "plus"), &ColumnValue::Ints(plus), "n = {n}");
            assert_eq!(field_of(&out, "same"), &ColumnValue::Ints(xs), "n = {n}");
            assert_eq!(field_of(&out, "big"), &ColumnValue::Bools(big), "n = {n}");
            assert_eq!(
                field_of(&out, "seven"),
                &ColumnValue::Ints(vec![7; n]),
                "n = {n}"
            );
        }
    }

    /// A nested product is a `Record` that a later `Record` names, and the outer one is the last
    /// instruction. A `Record` that an operation reads, or that nothing names before the end,
    /// breaks the invariant `fuse_prefix` asserts, and so does a program whose last instruction is
    /// an `Input` or a `Const`.
    #[test]
    fn a_record_is_only_the_result_or_a_field_of_one() {
        let chain = vec![zip_record(vec![
            ("a", arith(ArithmeticKind::Add, 1)),
            ("b", zip_record(vec![("c", id()), ("d", constant(1))])),
        ])];
        let program = fuse(&chain, &int()).unwrap().program;
        assert!(program.constructors_build_only_the_result(), "{program}");
        let records: Vec<usize> = program
            .instrs
            .iter()
            .enumerate()
            .filter_map(|(slot, instr)| matches!(instr.op, Op::Record(_)).then_some(slot))
            .collect();
        assert_eq!(records.len(), 2, "{program}");
        assert_eq!(records[1], program.instrs.len() - 1, "{program}");
        let read = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Record(vec![("a".into(), 0)]),
            Op::Un(UnaryOpKind::Neg, 1),
        ]);
        assert!(!read.constructors_build_only_the_result());
        let unnamed = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Record(vec![("a".into(), 0)]),
            Op::Un(UnaryOpKind::Neg, 0),
        ]);
        assert!(!unnamed.constructors_build_only_the_result());
        let bare_read = ScalarProgram::rooted(vec![Op::Input { path: Vec::new() }]);
        assert!(!bare_read.constructors_build_only_the_result());
        let wrap_read = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Wrap {
                tag: tag("some"),
                payload: 0,
            },
            Op::Un(UnaryOpKind::Neg, 1),
        ]);
        assert!(!wrap_read.constructors_build_only_the_result());
    }

    /// An operation reads only a column with a view: not a `Unit` constant, and not a `Unit` or
    /// union input, which the program tells apart only by the extent it is applied to.
    #[test]
    fn an_operation_reads_only_a_column_with_a_view() {
        let compare = |a, b| Op::Bin(BinOpKind::Compare(CompareKind::Equals).into(), a, b);
        let ints = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Const(Value::Int(1)),
            compare(0, 1),
        ]);
        assert!(ints.operands_have_views(&int()));
        let unit_constant = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Const(Value::Unit),
            compare(0, 1),
        ]);
        assert!(!unit_constant.operands_have_views(&int()));
        let negated = ScalarProgram::rooted(vec![
            Op::Input {
                path: vec!["b".into()],
            },
            Op::Un(UnaryOpKind::Neg, 0),
        ]);
        let with = |b| record_of_extents(vec![("a", int()), ("b", b)]);
        assert!(negated.operands_have_views(&with(int())));
        assert!(!negated.operands_have_views(&with(option_extent())));
        assert!(!negated.operands_have_views(&with(Extent::Base(BaseType::Unit))));
        assert!(
            !negated.operands_have_views(&int()),
            "`b` names no field of an `Int`"
        );
        let chained = ScalarProgram::rooted(vec![
            Op::Input { path: Vec::new() },
            Op::Const(Value::Int(1)),
            compare(0, 1),
            Op::Un(UnaryOpKind::Not, 2),
        ]);
        assert!(chained.operands_have_views(&int()));
    }

    /// The output lists a record's fields in name order, whatever order the `zip` lists them in.
    #[test]
    fn a_record_result_lists_its_fields_in_name_order() {
        let arms = || {
            vec![
                ("b", arith(ArithmeticKind::Mul, 2)),
                ("a", arith(ArithmeticKind::Add, 1)),
            ]
        };
        let listed = fuse(&[zip_record(arms())], &int()).unwrap();
        let reversed = fuse(&[zip_record(arms().into_iter().rev().collect())], &int());
        let Some(Op::Record(fields)) = listed.program.instrs.last().map(|instr| &instr.op) else {
            panic!("a record output, got {}", listed.program)
        };
        let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["a", "b"]);
        let out = listed.program.eval(&ColumnValue::Ints(vec![3]));
        assert_eq!(
            reversed.unwrap().program.eval(&ColumnValue::Ints(vec![3])),
            out
        );
    }

    #[test]
    fn an_arm_outside_the_element_wise_set_declines_the_chain() {
        let chain = vec![
            zip(vec![id(), Expr::builtin(Builtin::Sum)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        ];
        assert!(fuse(&chain, &int()).is_none());
    }

    #[test]
    fn a_column_of_collections_is_not_read() {
        let function = Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(int()),
        };
        assert!(fuse(&conjunction(), &function).is_none());
    }

    /// An element the parse abandons part-way leaves the instructions it emitted past the chosen
    /// prefix, and the program holds none of them, so equal chains give equal programs.
    #[test]
    fn an_abandoned_attempt_leaves_the_same_program() {
        let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let plain = vec![zip(vec![id(), constant(1)]), add.clone()];
        let plain = fuse(&plain, &int()).unwrap().program;
        // A good prefix, then a `zip` whose second arm is not element-wise.
        let abandoned = vec![
            zip(vec![id(), constant(1)]),
            add.clone(),
            zip(vec![
                Expr::compose(vec![zip(vec![id(), constant(9)]), add]),
                Expr::builtin(Builtin::Sum),
            ]),
        ];
        let abandoned = fuse(&abandoned, &int()).unwrap().program;
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
        let fused = fuse(&chain, &int()).unwrap();
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
        let fused = fuse(&chain, &record).unwrap();
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
        let fused = fuse(&chain, &Extent::Base(BaseType::Bool)).unwrap();
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
        let fused = fuse(&conjunction(), &int()).unwrap();
        let total = 3 * BLOCK_ROWS;
        let input = ramp(total);
        let mut scratch = Scratch::new(&input, &fused.program);
        let mut out = scratch.empties.last().cloned().flatten().unwrap();
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
                matches!(instr.op, Op::Bin(..) | Op::Un(..)),
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
        assert!(fuse(&[field("a"), field("b")], &ab).is_none());
        assert!(fuse(&[field("a"), field("b"), field("c")], &abc).is_none());
        let composed = Expr::compose(vec![field("a"), field("b"), field("c")]);
        assert!(fuse(&[composed], &abc).is_none());
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
        let separate = fuse(&separate, &abc).expect("an operation follows the projections");
        let composed = fuse(&composed, &abc).expect("an operation follows the projections");
        assert_eq!(separate.program, composed.program);
        let inputs = |fused: &Fused| {
            fused
                .program
                .instrs
                .iter()
                .filter(|i| matches!(i.op, Op::Input { .. }))
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
