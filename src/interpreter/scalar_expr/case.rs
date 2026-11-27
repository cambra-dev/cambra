//! A conditional fused into an element-wise chain: a [`CaseFn`] whose arms each hold a gate and a
//! body, a [`ScalarProgram`] run only on the rows its gate takes.
//!
//! A program reads a `CaseFn` through its `Case` instruction, which hands it the columns its arms
//! read, borrowed where the program already holds them ([`Captured`]). A conditional inside an
//! arm is a `Case` instruction of that arm's body, so conditionals nest by recursion. Recognition
//! is in `parse/join.rs`; the design is in `src/interpreter/design-operators.md`, "Conditional
//! programs".

use smol_str::SmolStr;

use std::collections::HashMap;

use super::ScalarProgram;
use super::eval::{Buffers, Captures};
use crate::ccl::{FieldKey, TagMap};
use crate::interpreter::RowIndex;
use crate::interpreter::{ColumnValue, ColumnView, UnionArm};

/// The field of an arm's input holding the payloads of a `Tag` gate's rows.
pub(super) const PAYLOAD: &str = "~payload";

/// The field of an arm's or a gate's input holding its row count, a `Units` column. A program that
/// reads no capture still has rows.
const ROWS: &str = "~rows";

/// The buffers a [`CaseFn`] reuses across the blocks of the program holding it: the rows left,
/// each arm's rows, input, programs' scratch columns and result, and the merged column. A capture
/// without a view, a `Tag` gate's payloads without a view and a union result are still built per
/// block.
#[derive(Default)]
pub(super) struct CaseBuffers {
    /// The rows of the block no earlier arm took.
    rest: Rows,
    /// The positions of `rest` the current gate leaves, swapped into `rest` after the gate.
    left: Vec<RowIndex>,
    arms: Vec<ArmBuffers>,
    /// The merged block that `Scratch::append_case_block` copies into its program's result.
    pub(super) merged: Option<ColumnValue>,
}

/// One arm's buffers: its gate's input, program buffers and result, then its body's.
#[derive(Default)]
struct ArmBuffers {
    /// The rows of the block this arm took.
    taken: Rows,
    /// For a `Tag` gate, the index in its tag's payload column of each row it took.
    slots: Vec<RowIndex>,
    /// Whether this arm took a row of the current block.
    ran: bool,
    gate_input: Option<ColumnValue>,
    gate: Buffers,
    holds: Option<ColumnValue>,
    input: Option<ColumnValue>,
    body: Buffers,
    result: Option<ColumnValue>,
}

/// A set of rows of a block: every row, without listing them, or the positions listed. A `Holds`
/// gate that selects every row of a set moves the whole set, and one that selects none leaves it,
/// so a block that no gate splits lists no position unless a `Tag` gate reads it.
#[derive(Default)]
struct Rows {
    block: bool,
    positions: Vec<RowIndex>,
}

impl Rows {
    /// The positions, or `None` for every row of the block.
    fn positions(&self) -> Option<&[RowIndex]> {
        (!self.block).then_some(self.positions.as_slice())
    }

    fn is_empty(&self) -> bool {
        !self.block && self.positions.is_empty()
    }

    fn set_empty(&mut self) {
        self.block = false;
        self.positions.clear();
    }

    /// List the positions of a set of every row of a block of `len` rows.
    fn list(&mut self, len: usize) {
        if self.block {
            self.block = false;
            self.positions.clear();
            self.positions.extend(0..len);
        }
    }
}

/// The empty column of a `Case`'s result type, which finding a program's empty columns reads
/// instead of evaluating an arm.
///
/// `ColumnValue` has no `Hash`, so a shape hashes as nothing; `Eq` still compares it, which keeps
/// equal values hashing equally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Shape(pub(super) ColumnValue);

impl std::hash::Hash for Shape {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

/// A conditional: arms tried in order, each taking the rows its gate selects among the rows no
/// earlier arm took. The arms' gates split the rows, which recognition proves.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct CaseFn {
    pub(super) arms: Vec<CaseArm>,
}

/// One arm of a [`CaseFn`]: its gate and its body. The body reads the captures it names in
/// `reads`, narrowed to the arm's rows, with the payloads of a `Tag` gate at [`PAYLOAD`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct CaseArm {
    pub(super) gate: CaseGate,
    pub(super) body: ScalarProgram,
    reads: Vec<SmolStr>,
}

impl CaseArm {
    pub(super) fn new(gate: CaseGate, body: ScalarProgram) -> Self {
        let reads = body.input_fields();
        CaseArm { gate, body, reads }
    }
}

/// The rows an arm takes, among the rows no earlier arm took.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum CaseGate {
    /// The rows where `program`, a `Bool` function of the captures it names in `reads`, holds.
    Holds {
        program: ScalarProgram,
        reads: Vec<SmolStr>,
    },
    /// Every row: the final `else`.
    Rest,
    /// The rows whose value in the union field `scrutinee` carries `tag`.
    Tag { scrutinee: SmolStr, tag: FieldKey },
}

impl CaseGate {
    /// A `Holds` gate of `program`.
    pub(super) fn holds(program: ScalarProgram) -> Self {
        let reads = program.input_fields();
        CaseGate::Holds { program, reads }
    }
}

/// A capture a `Case` hands its [`CaseFn`] for one block, borrowed from the program running it
/// where the column is already there.
pub(super) enum Captured<'a> {
    /// The block's values, read through a view.
    View(ColumnView<'a>),
    /// The rows `offset..offset + len` of a column with no view, `len` being the block's.
    Column(&'a ColumnValue, usize),
    /// A column built for the block: the result of a `Case` that constructs, its union rows
    /// numbered from the block's first.
    Owned(ColumnValue),
}

impl CaseFn {
    /// Whether every capture this conditional's arms and gates read is named in `captures`.
    pub(super) fn reads_only<T>(&self, captures: &[(SmolStr, T)]) -> bool {
        let named = |name: &SmolStr| captures.iter().any(|(n, _)| n == name);
        self.arms.iter().all(|arm| {
            arm.reads.iter().all(named)
                && match &arm.gate {
                    CaseGate::Holds { reads, .. } => reads.iter().all(named),
                    CaseGate::Rest => true,
                    CaseGate::Tag { scrutinee, .. } => named(scrutinee),
                }
        })
    }

    /// Write one value per row of a block of `len` rows, whose captures are `captures`, to `out`,
    /// an empty column of the result's type.
    pub(super) fn eval_into(
        &self,
        captures: &[(SmolStr, Captured)],
        len: usize,
        buffers: &mut CaseBuffers,
        out: &mut ColumnValue,
    ) {
        debug_assert!(out.is_empty(), "a `CaseFn` writes an empty column");
        if len == 0 {
            return;
        }
        let CaseBuffers {
            rest, left, arms, ..
        } = buffers;
        arms.resize_with(self.arms.len(), ArmBuffers::default);
        rest.block = true;
        rest.positions.clear();
        for (arm, buffers) in self.arms.iter().zip(arms.iter_mut()) {
            let payload = arm.select(captures, len, rest, left, buffers);
            let ArmBuffers {
                taken,
                slots,
                ran,
                input,
                body,
                result,
                ..
            } = buffers;
            *ran = !taken.is_empty();
            if !*ran {
                continue;
            }
            // One arm taking every row answers the whole block, so its result is not merged.
            // Listed positions that hold every row are `0..len`, so the arm reads the block whole.
            if (taken.block || taken.positions.len() == len) && payload.is_none() {
                let input = gather_into(captures, &arm.reads, None, len, input);
                let selection = Captures {
                    captures,
                    positions: None,
                    payload: None,
                };
                arm.body.eval_into(input, selection, body, out);
                return;
            }
            taken.list(len);
            let taken = &taken.positions;
            let input = gather_into(captures, &arm.reads, Some(taken), len, input);
            // A payload with a view is read in place at its slots; any other is copied into the
            // arm's input.
            let payload = match payload {
                None => None,
                Some(values) => {
                    debug_assert_eq!(slots.len(), taken.len(), "one slot per row taken");
                    match values.view() {
                        Some(view) => Some(view.select(slots).expect("a column's view is a slice")),
                        None => {
                            let copied = values.select_indices(slots.iter().copied(), slots.len());
                            let ColumnValue::Records(fields) = &mut *input else {
                                unreachable!("a `CaseFn`'s input is a record column")
                            };
                            fields.insert(PAYLOAD.into(), copied);
                            None
                        }
                    }
                }
            };
            let selection = Captures {
                captures,
                positions: Some(taken),
                payload,
            };
            let result = cleared(result, || arm.body.empty_result(input, selection, body));
            arm.body.eval_into(input, selection, body, result);
        }
        debug_assert!(rest.is_empty(), "the arms' gates split the rows");
        let parts: Vec<(&ColumnValue, &[RowIndex])> = arms
            .iter()
            .filter(|arm| arm.ran)
            .map(|arm| {
                let result = arm.result.as_ref().expect("an arm that ran has a result");
                (result, arm.taken.positions.as_slice())
            })
            .collect();
        merge_into(&parts, len, out);
    }
}

/// The column in `kept`, cleared, or on its first use the column that `empty` makes.
fn cleared(
    kept: &mut Option<ColumnValue>,
    empty: impl FnOnce() -> ColumnValue,
) -> &mut ColumnValue {
    match kept {
        Some(column) => {
            column.clear();
            column
        }
        None => kept.insert(empty()),
    }
}

impl CaseArm {
    /// Move the rows of `rest` this arm takes to its `taken` buffer, in a block of `len` rows, and
    /// for a `Tag` gate whose tag the union column carries return that tag's payload column, with
    /// each taken row's index in it in the `slots` buffer. A tag the column does not carry takes
    /// no row, so its arm is skipped and needs no payload. `left` is scratch for the positions
    /// that `rest` keeps.
    fn select<'a>(
        &'a self,
        captures: &'a [(SmolStr, Captured<'a>)],
        len: usize,
        rest: &mut Rows,
        left: &mut Vec<RowIndex>,
        buffers: &mut ArmBuffers,
    ) -> Option<&'a ColumnValue> {
        let ArmBuffers {
            taken,
            slots,
            gate_input,
            gate,
            holds,
            ..
        } = buffers;
        taken.set_empty();
        left.clear();
        if rest.is_empty() {
            return None;
        }
        match &self.gate {
            CaseGate::Rest => {
                std::mem::swap(taken, rest);
                rest.set_empty();
                None
            }
            CaseGate::Holds { program, reads } => {
                let positions = rest.positions();
                let input = gather_into(captures, reads, positions, len, gate_input);
                let selection = Captures {
                    captures,
                    positions,
                    payload: None,
                };
                let holds = cleared(holds, || program.empty_result(input, selection, gate));
                program.eval_into(input, selection, gate, holds);
                let ColumnValue::Bools(holds) = holds else {
                    unreachable!("a gate yields a `Bool` column, got {holds:?}")
                };
                debug_assert_eq!(
                    holds.len(),
                    rest.positions().map_or(len, <[RowIndex]>::len),
                    "a gate yields one value per row left"
                );
                let selected = holds.iter().filter(|&&holds| holds).count();
                if selected == holds.len() {
                    std::mem::swap(taken, rest);
                    rest.set_empty();
                } else if selected > 0 {
                    rest.list(len);
                    for (&p, &holds) in rest.positions.iter().zip(holds.iter()) {
                        if holds {
                            taken.positions.push(p);
                        } else {
                            left.push(p);
                        }
                    }
                    std::mem::swap(&mut rest.positions, left);
                }
                None
            }
            CaseGate::Tag { scrutinee, tag } => {
                let (union, offset) = match captured(captures, scrutinee) {
                    Captured::Column(column, offset) => (*column, *offset),
                    Captured::Owned(column) => (column, 0),
                    Captured::View(_) => unreachable!("a union has no view"),
                };
                let ColumnValue::Union(arms) = union else {
                    unreachable!("a `Tag` gate reads a union column, got {union:?}")
                };
                let arm = arms.get(tag)?;
                rest.list(len);
                slots.clear();
                // The arm's rows before the block are skipped by a search, not a walk.
                let first = arm.rows().partition_point(|&row| row < offset);
                let mut rows = arm.rows()[first..]
                    .iter()
                    .enumerate()
                    .map(|(i, &row)| (row, first + i))
                    .peekable();
                for &p in rest.positions.iter() {
                    let row_of_p = offset + p;
                    while rows.next_if(|(row, _)| *row < row_of_p).is_some() {}
                    match rows.peek() {
                        Some(&(row, slot)) if row == row_of_p => {
                            taken.positions.push(p);
                            slots.push(slot);
                        }
                        _ => left.push(p),
                    }
                }
                std::mem::swap(&mut rest.positions, left);
                Some(arm.values())
            }
        }
    }
}

/// The capture named `name`.
fn captured<'c, 'a>(captures: &'c [(SmolStr, Captured<'a>)], name: &str) -> &'c Captured<'a> {
    captures
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, captured)| captured)
        .unwrap_or_else(|| panic!("a `CaseFn` reads the capture {name}"))
}

/// The record of the captures named in `reads`, with [`ROWS`], at `positions` of a block of `len`
/// rows, or at every row with no positions, written into the record kept in `kept`. A capture
/// with a view is left out, since the program reads it through [`Captures::selected`]: the view
/// itself at every row, or a selection of it at the positions. A view that is already a selection
/// is copied at listed positions instead. A capture without a view is rebuilt.
fn gather_into<'k>(
    captures: &[(SmolStr, Captured)],
    reads: &[SmolStr],
    positions: Option<&[RowIndex]>,
    len: usize,
    kept: &'k mut Option<ColumnValue>,
) -> &'k mut ColumnValue {
    let record = kept.get_or_insert_with(|| {
        let mut fields: HashMap<SmolStr, ColumnValue> = reads
            .iter()
            .map(|name| {
                let empty = match captured(captures, name) {
                    Captured::View(view) => view.empty_like(),
                    Captured::Column(column, _) => column.empty_like(),
                    Captured::Owned(column) => column.empty_like(),
                };
                (name.clone(), empty)
            })
            .collect();
        fields.insert(ROWS.into(), ColumnValue::Units(0));
        ColumnValue::Records(fields)
    });
    let ColumnValue::Records(fields) = record else {
        unreachable!("an arm's input is a record column")
    };
    let rows = positions.map_or(len, <[RowIndex]>::len);
    for name in reads {
        let capture = captured(captures, name);
        if let Captured::View(view) = capture
            && positions.is_none_or(|positions| view.select(positions).is_some())
        {
            fields.remove(name);
            continue;
        }
        let column = fields.entry(name.clone()).or_insert_with(|| match capture {
            Captured::View(view) => view.empty_like(),
            Captured::Column(column, _) => column.empty_like(),
            Captured::Owned(column) => column.empty_like(),
        });
        match (captured(captures, name), positions) {
            (Captured::View(view), Some(positions)) => {
                column.clear();
                view.gather_into(positions, column);
            }
            (Captured::View(_), None) => {
                unreachable!("a view is read whole through `Captures::selected`")
            }
            (Captured::Column(source, offset), Some(positions)) => {
                *column =
                    source.select_indices(positions.iter().map(|&p| offset + p), positions.len());
            }
            (Captured::Column(source, offset), None) => {
                *column = source.slice(*offset..offset + len);
            }
            (Captured::Owned(source), Some(positions)) => {
                *column = source.select_indices(positions.iter().copied(), positions.len());
            }
            (Captured::Owned(source), None) => *column = source.clone(),
        }
    }
    fields.insert(ROWS.into(), ColumnValue::Units(rows));
    record
}

/// One arm of a merged union column: its tag, the parts' payloads for it concatenated, and each
/// row's position in the merged column with its index in those payloads.
type MergedArm = (FieldKey, ColumnValue, Vec<(RowIndex, usize)>);

/// One column of `len` rows from `parts`: the row at position `p` is the next row of the one part
/// whose positions hold `p`. The parts' positions are ascending and together hold each of `0..len`
/// once. A record merges field by field, and a union arm by arm, each row keeping its tag.
fn merge_into(parts: &[(&ColumnValue, &[RowIndex])], len: usize, out: &mut ColumnValue) {
    debug_assert!(out.is_empty(), "a merge writes an empty column");
    let first = parts.first().expect("a `Case` has an arm").0;
    if first.view().is_some() {
        let views: Vec<_> = parts
            .iter()
            .map(|(column, positions)| (column.view().expect("parts of one type"), *positions))
            .collect();
        ColumnView::scatter_into(&views, len, out);
        return;
    }
    match out {
        ColumnValue::Units(rows) => *rows = len,
        ColumnValue::Records(fields) => {
            for (name, field) in fields.iter_mut() {
                let field_parts: Vec<(&ColumnValue, &[RowIndex])> = parts
                    .iter()
                    .map(|(column, positions)| {
                        let ColumnValue::Records(fields) = column else {
                            panic!("parts of one type")
                        };
                        (fields.get(name).expect("parts of one type"), *positions)
                    })
                    .collect();
                merge_into(&field_parts, len, field);
            }
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
                for (tag, arm) in arms.iter() {
                    let i = match by_tag.iter().position(|(t, ..)| t == tag) {
                        Some(i) => i,
                        None => {
                            by_tag.push((tag.clone(), arm.values().empty_like(), Vec::new()));
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
            *out = ColumnValue::Union(TagMap::from_arms(
                by_tag
                    .into_iter()
                    .map(|(tag, values, mut rows)| {
                        rows.sort_unstable_by_key(|(position, _)| *position);
                        let values =
                            values.select_indices(rows.iter().map(|(_, i)| *i), rows.len());
                        let rows = rows.iter().map(|(p, _)| *p).collect();
                        (tag, UnionArm::new(rows, values))
                    })
                    .collect(),
            ));
        }
        other => panic!("a `Case` merges columns of base types, records and unions, got {other:?}"),
    }
}
