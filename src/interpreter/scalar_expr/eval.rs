//! Evaluate a [`ScalarProgram`] on a column, block by block.

use std::mem::replace;

use smol_str::SmolStr;

use super::case::Captured;
use super::{Instr, ScalarProgram};
use crate::ccl::TagMap;
use crate::interpreter::{
    ColumnValue, ColumnView, UnionArm, Value, apply_binop_views, apply_unaryop_views,
    binop_result_column, unaryop_result_column,
};
use crate::view::View;

/// Rows per block, chosen to keep a kernel's operands and result in L1. Each full 64-bit column
/// occupies 8 KiB, so two operands and a result occupy 24 KiB.
pub(super) const BLOCK_ROWS: usize = 1024;

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

/// Per-evaluation buffers reused across blocks. Inputs and constants are borrowed views.
struct Scratch<'a> {
    input: &'a ColumnValue,
    /// The empty column of each slot's type ([`ScalarProgram::empties`]).
    empties: Vec<ColumnValue>,
    /// `Units(0)` marks unwritten slots; no operation produces that column variant. Inputs,
    /// constants, constructors, and the last instruction never write a scratch slot.
    slots: Vec<ColumnValue>,
    /// The current block: the rows `start..start + len` of the input.
    start: usize,
    len: usize,
}

impl<'a> Scratch<'a> {
    fn new(input: &'a ColumnValue, program: &ScalarProgram) -> Self {
        Self {
            input,
            empties: program.empties(input),
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
            Instr::Bin(..) | Instr::Un(..) | Instr::Case { .. } => self.slots[slot]
                .view()
                .unwrap_or_else(|| panic!("the result s{slot} is a column of a base type")),
            Instr::Record(_) | Instr::Wrap { .. } => {
                unreachable!("no instruction views the constructor s{slot}")
            }
        }
    }

    /// Append the current block of `slot` to `out`, which must have its type. A constructor
    /// builds its block in place. A `Unit` or union input has no view, so its block is copied. A
    /// `Unit` constant adds the block's rows to a `Units` column.
    fn append(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        let rows = self.start..self.start + self.len;
        match &program.instrs[slot] {
            instr if instr.is_constructor() => self.run(program, slot, out),
            Instr::Input { path } if field(self.input, path).view().is_none() => {
                out.append(field(self.input, path).slice(rows))
            }
            Instr::Const(Value::Unit) => out.append(ColumnValue::Units(rows.len())),
            _ => out.extend_from_view(self.view(program, slot)),
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

    /// Evaluate an operation into its scratch buffer. Other instructions have no scratch output.
    fn run_into_slot(&mut self, program: &ScalarProgram, slot: usize) {
        let instr = &program.instrs[slot];
        if let Instr::Case {
            constructs: false, ..
        } = instr
        {
            self.slots[slot] = self.case_block(program, slot);
            return;
        }
        if !matches!(instr, Instr::Bin(..) | Instr::Un(..)) {
            return;
        }
        let mut column = self.slot_column(program, slot, instr);
        self.run(program, slot, &mut column);
        self.slots[slot] = column;
    }

    /// The column an operation writes its block into: its slot's buffer, cleared, or on the first
    /// block a new empty column of the operation's result type.
    fn slot_column(&mut self, program: &ScalarProgram, slot: usize, instr: &Instr) -> ColumnValue {
        let mut column = take(&mut self.slots[slot]);
        if !matches!(column, ColumnValue::Units(_)) {
            column.clear();
            return column;
        }
        match instr {
            Instr::Un(op, a) => unaryop_result_column(*op, &self.view(program, *a as usize)),
            Instr::Bin(op, a, _) => binop_result_column(*op, &self.view(program, *a as usize)),
            Instr::Input { .. }
            | Instr::Const(_)
            | Instr::Record(_)
            | Instr::Wrap { .. }
            | Instr::Case { .. } => unreachable!("only an operation writes a slot"),
        }
    }

    /// Append an operation or constructor's current block to `out`, which must have its result
    /// type. Nested constructors are built recursively because they have no scratch columns.
    fn run(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        match &program.instrs[slot] {
            Instr::Un(op, a) => apply_unaryop_views(*op, &self.view(program, *a as usize), out),
            Instr::Bin(op, a, b) => {
                let (a, b) = (
                    self.view(program, *a as usize),
                    self.view(program, *b as usize),
                );
                apply_binop_views(*op, &a, &b, out);
            }
            Instr::Record(fields) => {
                let ColumnValue::Records(columns) = out else {
                    panic!("a record is appended to a record column, got {out:?}")
                };
                for (name, field) in fields {
                    let column = columns
                        .get_mut(name)
                        .unwrap_or_else(|| panic!("the result has a column for the field {name}"));
                    self.append(program, *field as usize, column);
                }
            }
            Instr::Wrap { tag, payload } => {
                let ColumnValue::Union(arms) = out else {
                    panic!("a wrap is appended to a union column, got {out:?}")
                };
                let arm = arms
                    .get_mut(tag)
                    .unwrap_or_else(|| panic!("the result has an arm for the tag {tag}"));
                // A union's rows are numbered across the whole column, and every row of the
                // result carries this one arm, so the block's rows are its positions in the input.
                arm.extend_rows(self.start..self.start + self.len, |values| {
                    self.append(program, *payload as usize, values)
                });
            }
            Instr::Case { .. } => out.append(self.case_block(program, slot)),
            // An arm's body may answer with a value it reads: `else x`.
            Instr::Input { .. } | Instr::Const(_) => self.append(program, slot, out),
        }
    }

    /// The current block of the `Case` in `slot`: its conditional applied to its captures.
    fn case_block(&self, program: &ScalarProgram, slot: usize) -> ColumnValue {
        let Instr::Case { case, captures, .. } = &program.instrs[slot] else {
            unreachable!("s{slot} is a `Case`")
        };
        let captured: Vec<(SmolStr, Captured)> = captures
            .iter()
            .map(|(name, capture)| (name.clone(), self.captured(program, *capture as usize)))
            .collect();
        case.eval(&captured, self.len)
    }

    /// The current block of `slot` as a capture: a view of a column with one, the input's own
    /// column with the block's offset, or a column built for the block.
    fn captured<'s>(&'s self, program: &'s ScalarProgram, slot: usize) -> Captured<'s> {
        match &program.instrs[slot] {
            Instr::Input { path } => {
                let column = field(self.input, path);
                match column.view() {
                    Some(view) => Captured::View(view.range(self.start..self.start + self.len)),
                    None => Captured::Column(column, self.start),
                }
            }
            Instr::Bin(..)
            | Instr::Un(..)
            | Instr::Case {
                constructs: false, ..
            } => Captured::View(self.view(program, slot)),
            // `case_block` numbers a union's rows from the block's first, as `Captured::Owned`
            // reads them.
            Instr::Case { .. } => Captured::Owned(self.case_block(program, slot)),
            Instr::Const(_) | Instr::Record(_) | Instr::Wrap { .. } => unreachable!(
                "s{slot} is no capture: outlining copies constants, and `Record` and `Wrap` are \
                 emitted only after a conditional's arms, at or after its start"
            ),
        }
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
            .expect("a program has a last instruction");
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
    /// types without evaluating any block. A `Case`'s is its conditional applied to its captures'
    /// empty columns.
    fn empties(&self, input: &ColumnValue) -> Vec<ColumnValue> {
        let mut empties: Vec<ColumnValue> = Vec::with_capacity(self.instrs.len());
        for instr in &self.instrs {
            let empty = match instr {
                Instr::Input { path } => field(input, path).empty_like(),
                Instr::Const(value) => ColumnValue::single(value.clone()).empty_like(),
                Instr::Un(op, a) => {
                    let operand = empties[*a as usize]
                        .view()
                        .expect("an operand is a column of a base type");
                    unaryop_result_column(*op, &operand)
                }
                Instr::Bin(op, a, _) => {
                    let operand = empties[*a as usize]
                        .view()
                        .expect("an operand is a column of a base type");
                    binop_result_column(*op, &operand)
                }
                Instr::Record(fields) => ColumnValue::Records(
                    fields
                        .iter()
                        .map(|(name, field)| (name.clone(), empties[*field as usize].clone()))
                        .collect(),
                ),
                Instr::Wrap { tag, payload } => ColumnValue::Union(TagMap::from_arms(vec![(
                    tag.clone(),
                    UnionArm::new(Vec::new(), empties[*payload as usize].clone()),
                )])),
                Instr::Case { shape, .. } => shape.0.clone(),
            };
            empties.push(empty);
        }
        empties
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind};
    use crate::ccl::{Builtin, Expr};
    use crate::interpreter::{BaseType, Extent, tuple_field};

    use crate::interpreter::scalar_expr::tests::*;

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
        let mut out = scratch.empties.last().cloned().unwrap();
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
}
