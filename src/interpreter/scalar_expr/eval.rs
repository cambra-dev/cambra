//! Evaluate a [`ScalarProgram`] on a column, block by block.

use std::cell::RefCell;
use std::mem::take as take_buffers;

use smol_str::SmolStr;

use super::case::{Captured, CaseBuffers, PAYLOAD, Rows};
use super::junction::JunctionBuffers;
use super::{Instr, ScalarProgram};
use crate::ccl::TagMap;
use crate::interpreter::RowIndex;
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

/// The buffers one program's evaluation reuses across blocks. A `Case` arm's gate and body keep
/// theirs across the blocks of the enclosing program, so an arm allocates them once.
#[derive(Default)]
pub(super) struct Buffers {
    /// The empty column of each slot's type ([`ScalarProgram::empties`]). Empty until the first
    /// evaluation, which finds them from its input's columns.
    empties: Vec<ColumnValue>,
    /// The scratch column of each operation, `None` until its first block. Inputs, constants,
    /// constructors, and the last instruction never write a slot.
    slots: Vec<Option<ColumnValue>>,
    /// The buffers of the `Case` in each slot. A slot holding no `Case` keeps the empty default.
    cases: Vec<RefCell<CaseBuffers>>,
    /// The buffers of the `Predicate` in each slot. A slot holding no `Predicate` keeps the empty
    /// default.
    junctions: Vec<RefCell<JunctionBuffers>>,
}

impl Buffers {
    /// Size the buffers for `program` over the columns of `input`, unless an earlier evaluation
    /// did. Every evaluation reusing them reads an input with the same column types, though a
    /// capture's field may be present in one block's input and read through a view in another.
    fn prepare(&mut self, program: &ScalarProgram, input: &ColumnValue, captures: Captures) {
        if self.slots.len() == program.instrs.len() {
            return;
        }
        self.empties = program.empties(input, captures);
        self.slots = vec![None; program.instrs.len()];
        self.cases = (0..program.instrs.len())
            .map(|_| RefCell::default())
            .collect();
        self.junctions = (0..program.instrs.len())
            .map(|_| RefCell::default())
            .collect();
    }
}

/// The captures of the `Case` running a gate or body, and the positions of the block that
/// program reads. An input naming a capture with a view reads it at those positions through a
/// selection view rather than from a gathered copy ([`View::select`]).
#[derive(Clone, Copy)]
pub(super) struct Captures<'a> {
    pub(super) captures: &'a [(SmolStr, Captured<'a>)],
    pub(super) positions: Option<&'a [RowIndex]>,
    /// A `Tag` arm's payloads at its rows, when they have a view; the program reads [`PAYLOAD`]
    /// through it rather than from a copy in its input.
    pub(super) payload: Option<ColumnView<'a>>,
}

impl<'a> Captures<'a> {
    /// No captures: every input is read from the input column.
    pub(super) const NONE: Captures<'static> = Captures {
        captures: &[],
        positions: None,
        payload: None,
    };

    /// The capture `path` names, as a view at the positions, where it has a view that is not
    /// already a selection. [`PAYLOAD`] names the `Tag` arm's payloads, read through `payload`.
    pub(super) fn selected(&self, path: &[SmolStr]) -> Option<ColumnView<'a>> {
        let [name] = path else { return None };
        if name == PAYLOAD {
            return self.payload;
        }
        let (_, Captured::View(view)) = self.captures.iter().find(|(n, _)| n == name)? else {
            return None;
        };
        match self.positions {
            None => Some(*view),
            Some(positions) => view.select(positions),
        }
    }
}

/// One evaluation: its input, the block being evaluated, and the program's buffers. Inputs and
/// constants are borrowed views.
struct Scratch<'a> {
    input: &'a ColumnValue,
    captures: Captures<'a>,
    buffers: Buffers,
    /// The current block: the rows `start..start + len` of the input.
    start: usize,
    len: usize,
}

impl Scratch<'_> {
    /// The block of instruction `slot` as a view.
    fn view<'s>(&'s self, program: &'s ScalarProgram, slot: usize) -> ColumnView<'s> {
        match &program.instrs[slot] {
            Instr::Input { path } if self.captures.selected(path).is_some() => {
                let view = self.captures.selected(path).expect("checked by the guard");
                view.range(self.start..self.start + self.len)
            }
            Instr::Input { path } => field(self.input, path)
                .view()
                .unwrap_or_else(|| panic!("the input at {path:?} is a column of a base type"))
                .range(self.start..self.start + self.len),
            Instr::Const(value) => const_view(value, self.len),
            Instr::Bin(..) | Instr::Un(..) | Instr::Case { .. } | Instr::Predicate { .. } => {
                self.buffers.slots[slot]
                    .as_ref()
                    .unwrap_or_else(|| panic!("s{slot} is written before an instruction reads it"))
                    .view()
                    .unwrap_or_else(|| panic!("the result s{slot} is a column of a base type"))
            }
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
            Instr::Input { path } if self.captures.selected(path).is_some() => {
                out.extend_from_view(self.view(program, slot))
            }
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
        }
        | Instr::Predicate { .. } = instr
        {
            let mut column = match self.buffers.slots[slot].take() {
                Some(mut column) => {
                    column.clear();
                    column
                }
                None => self.buffers.empties[slot].clone(),
            };
            match instr {
                Instr::Predicate { .. } => self.junction_block(program, slot, &mut column),
                _ => self.case_block(program, slot, &mut column),
            }
            self.buffers.slots[slot] = Some(column);
            return;
        }
        if !matches!(instr, Instr::Bin(..) | Instr::Un(..)) {
            return;
        }
        let mut column = self.slot_column(program, slot, instr);
        self.run(program, slot, &mut column);
        self.buffers.slots[slot] = Some(column);
    }

    /// The column an operation writes its block into: its slot's buffer, cleared, or on the first
    /// block a new empty column of the operation's result type.
    fn slot_column(&mut self, program: &ScalarProgram, slot: usize, instr: &Instr) -> ColumnValue {
        if let Some(mut column) = self.buffers.slots[slot].take() {
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
            | Instr::Case { .. }
            | Instr::Predicate { .. } => unreachable!("only an operation writes a slot"),
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
            Instr::Case { .. } => self.append_case_block(program, slot, out),
            Instr::Predicate { .. } => self.junction_block(program, slot, out),
            // An arm's body may answer with a value it reads: `else x`.
            Instr::Input { .. } | Instr::Const(_) => self.append(program, slot, out),
        }
    }

    /// Write the current block of the `Case` in `slot`, its conditional applied to its captures,
    /// to `out`, an empty column of its type.
    fn case_block(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        let Instr::Case { case, captures, .. } = &program.instrs[slot] else {
            unreachable!("s{slot} is a `Case`")
        };
        let captured: Vec<(SmolStr, Captured)> = captures
            .iter()
            .map(|(name, capture)| (name.clone(), self.captured(program, *capture as usize)))
            .collect();
        let mut buffers = self.buffers.cases[slot].borrow_mut();
        case.eval_into(&captured, self.len, &mut buffers, out);
    }

    /// Append the current block of the `Case` in `slot` to `out`. The `Case` writes an empty
    /// column, so a union's rows are numbered from the block's first before `append` renumbers
    /// them into `out`. A column with a view is copied out and kept for the next block.
    fn append_case_block(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        let cell = &self.buffers.cases[slot];
        let kept = cell.borrow_mut().merged.take();
        let mut column = kept.unwrap_or_else(|| self.buffers.empties[slot].clone());
        column.clear();
        self.case_block(program, slot, &mut column);
        let copied = column
            .view()
            .map(|view| out.extend_from_view(view))
            .is_some();
        if copied {
            cell.borrow_mut().merged = Some(column);
        } else {
            out.append(column);
        }
    }

    /// Append the current block of the `Predicate` in `slot` to `out`, a `Bool` column: `true` at
    /// the rows where its junction holds.
    fn junction_block(&self, program: &ScalarProgram, slot: usize, out: &mut ColumnValue) {
        let ColumnValue::Bools(out) = out else {
            unreachable!("a `Predicate` writes a `Bool` column, got {out:?}")
        };
        if self.len == 0 {
            return;
        }
        let mut rows = std::mem::take(&mut self.buffers.junctions[slot].borrow_mut().rows);
        rows.set_block();
        self.junction_rows(program, slot, &mut rows);
        let start = out.len();
        match rows.positions() {
            None => out.resize(start + self.len, true),
            Some(positions) => {
                out.resize(start + self.len, false);
                for &p in positions {
                    out[start + p] = true;
                }
            }
        }
        self.buffers.junctions[slot].borrow_mut().rows = rows;
    }

    /// Narrow `rows`, rows of the current block, to those where the `Predicate` in `slot` holds.
    fn junction_rows(&self, program: &ScalarProgram, slot: usize, rows: &mut Rows) {
        let Instr::Predicate { junction, captures } = &program.instrs[slot] else {
            unreachable!("s{slot} is a `Predicate`")
        };
        let captured: Vec<(SmolStr, Captured)> = captures
            .iter()
            .map(|(name, capture)| (name.clone(), self.captured(program, *capture as usize)))
            .collect();
        let mut buffers = self.buffers.junctions[slot].borrow_mut();
        junction.holds(&captured, self.len, &mut buffers, rows);
    }

    /// The current block of `slot` as a capture: a view of a column with one, the input's own
    /// column with the block's offset, or a column built for the block.
    fn captured<'s>(&'s self, program: &'s ScalarProgram, slot: usize) -> Captured<'s> {
        match &program.instrs[slot] {
            Instr::Input { path } if self.captures.selected(path).is_some() => {
                Captured::View(self.view(program, slot))
            }
            Instr::Input { path } => {
                let column = field(self.input, path);
                match column.view() {
                    Some(view) => Captured::View(view.range(self.start..self.start + self.len)),
                    None => Captured::Column(column, self.start),
                }
            }
            Instr::Bin(..)
            | Instr::Un(..)
            | Instr::Predicate { .. }
            | Instr::Case {
                constructs: false, ..
            } => Captured::View(self.view(program, slot)),
            // `case_block` numbers a union's rows from the block's first, as `Captured::Owned`
            // reads them.
            Instr::Case { .. } => {
                let mut column = self.buffers.empties[slot].clone();
                self.case_block(program, slot, &mut column);
                Captured::Owned(column)
            }
            Instr::Const(_) | Instr::Record(_) | Instr::Wrap { .. } => unreachable!(
                "s{slot} is no capture: outlining copies constants, and `Record` and `Wrap` are \
                 emitted only after a conditional's arms, at or after its start"
            ),
        }
    }
}

impl ScalarProgram {
    /// Return one result row per input row, evaluating in blocks of [`BLOCK_ROWS`].
    ///
    /// Reserve the output for all input rows before evaluation. Intermediate operations retain
    /// only one block each; inputs and constants are read through borrowed views.
    pub fn eval(&self, input: &ColumnValue) -> ColumnValue {
        let mut buffers = Buffers::default();
        let mut out = self.empty_result(input, Captures::NONE, &mut buffers);
        out.reserve(input.len());
        self.eval_into(input, Captures::NONE, &mut buffers, &mut out);
        out.debug_assert_union_invariants();
        out
    }

    /// Set `rows` to the rows of `input`, one block, where this program holds, for a program whose
    /// last instruction is a `Predicate`: the predicate answers its rows without writing a column.
    pub(super) fn select_root(
        &self,
        input: &ColumnValue,
        captures: Captures,
        buffers: &mut Buffers,
        rows: &mut Rows,
    ) {
        let last = self.instrs.len() - 1;
        debug_assert!(
            matches!(self.instrs[last], Instr::Predicate { .. }),
            "a program selected through its root ends in a `Predicate`, got {self}"
        );
        buffers.prepare(self, input, captures);
        let len = input.len();
        debug_assert!(len <= BLOCK_ROWS, "a selected program reads one block");
        let mut scratch = Scratch {
            input,
            captures,
            buffers: take_buffers(buffers),
            start: 0,
            len,
        };
        for slot in 0..last {
            scratch.run_into_slot(self, slot);
        }
        rows.set_block();
        scratch.junction_rows(self, last, rows);
        *buffers = scratch.buffers;
    }

    /// The empty column of the result's type, sizing `buffers` for an input with the columns of
    /// `input`.
    pub(super) fn empty_result(
        &self,
        input: &ColumnValue,
        captures: Captures,
        buffers: &mut Buffers,
    ) -> ColumnValue {
        buffers.prepare(self, input, captures);
        buffers
            .empties
            .last()
            .cloned()
            .expect("a program has a last instruction")
    }

    /// Write one result row per input row to `out`, an empty column of the result's type, reusing
    /// `buffers` from earlier evaluations over inputs with the same columns.
    pub(super) fn eval_into(
        &self,
        input: &ColumnValue,
        captures: Captures,
        buffers: &mut Buffers,
        out: &mut ColumnValue,
    ) {
        debug_assert!(out.is_empty(), "a program writes an empty column");
        buffers.prepare(self, input, captures);
        let len = input.len();
        let mut scratch = Scratch {
            input,
            captures,
            buffers: take_buffers(buffers),
            start: 0,
            len: 0,
        };
        let mut start = 0;
        loop {
            let rows = BLOCK_ROWS.min(len - start);
            scratch.block(self, start, rows, out);
            start += rows;
            if start >= len {
                break;
            }
        }
        *buffers = scratch.buffers;
        debug_assert_eq!(
            out.len(),
            len,
            "ScalarProgram::eval: one result row per input row"
        );
    }

    /// The empty column of each slot's type, found from the input's columns and the instructions'
    /// types without evaluating any block. A `Case`'s is its conditional applied to its captures'
    /// empty columns.
    fn empties(&self, input: &ColumnValue, captures: Captures) -> Vec<ColumnValue> {
        let mut empties: Vec<ColumnValue> = Vec::with_capacity(self.instrs.len());
        for instr in &self.instrs {
            let empty = match instr {
                Instr::Input { path } => match captures.selected(path) {
                    Some(view) => view.empty_like(),
                    None => field(input, path).empty_like(),
                },
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
                Instr::Predicate { .. } => ColumnValue::Bools(Vec::new()),
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
        let mut buffers = Buffers::default();
        let mut out = fused
            .program
            .empty_result(&input, Captures::NONE, &mut buffers);
        let mut scratch = Scratch {
            input: &input,
            captures: Captures::NONE,
            buffers,
            start: 0,
            len: 0,
        };
        out.reserve(total);
        scratch.block(&fused.program, 0, BLOCK_ROWS, &mut out);
        let result = pointer(&out);
        let (output, body) = scratch.buffers.slots.split_last().unwrap();
        assert!(
            output.is_none(),
            "the output writes to the result, not a slot"
        );
        // An input and a scalar constant are read in place and own no buffer; only an
        // operation's slot holds a column.
        let buffers: Vec<Option<*const u8>> =
            body.iter().map(|slot| slot.as_ref().map(pointer)).collect();
        for (slot, instr) in buffers.iter().zip(&fused.program.instrs) {
            assert_eq!(
                slot.is_some(),
                matches!(instr, Instr::Bin(..) | Instr::Un(..)),
                "{instr}"
            );
        }
        for start in [BLOCK_ROWS, 2 * BLOCK_ROWS] {
            scratch.block(&fused.program, start, BLOCK_ROWS, &mut out);
            let body = &scratch.buffers.slots[..buffers.len()];
            for (slot, before) in body.iter().zip(&buffers) {
                assert_eq!(slot.as_ref().map(pointer), *before, "block at {start}");
            }
            assert_eq!(pointer(&out), result, "block at {start}");
        }
        assert_eq!(out.len(), total);
    }
}
