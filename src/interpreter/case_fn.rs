//! A conditional fused into an element-wise chain: a [`CaseFn`] whose arms each hold a gate and a
//! body, a [`ScalarProgram`] run only on the rows its gate takes.
//!
//! A program reads a `CaseFn` through its `Case` instruction, which hands it the columns its arms
//! read, borrowed where the program already holds them ([`Captured`]). A conditional inside an
//! arm is a `Case` instruction of that arm's body, so conditionals nest by recursion. Recognition
//! is in `scalar_expr.rs`; the design is in `src/interpreter/design-operators.md`, "Conditional
//! programs".

use smol_str::SmolStr;

use super::{ColumnValue, ColumnView, RowIndex, ScalarProgram, UnionArm};
use crate::ccl::{FieldKey, TagMap};

/// The field of an arm's input holding the payloads of a `Tag` gate's rows.
pub(crate) const PAYLOAD: &str = "~payload";

/// The field of an arm's or a gate's input holding its row count, a `Units` column. A program that
/// reads no capture still has rows.
const ROWS: &str = "~rows";

/// The empty column of a payload's type, which an arm reads when its union column lacks the tag.
///
/// `ColumnValue` has no `Hash`, so a shape hashes as nothing; `Eq` still compares it, which keeps
/// equal values hashing equally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Shape(pub(crate) ColumnValue);

impl std::hash::Hash for Shape {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

/// A conditional: arms tried in order, each taking the rows its gate selects among the rows no
/// earlier arm took. The arms' gates split the rows, which recognition proves.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CaseFn {
    pub(crate) arms: Vec<CaseArm>,
}

/// One arm of a [`CaseFn`]: its gate and its body. The body reads the captures it names in
/// `reads`, narrowed to the arm's rows, with the payloads of a `Tag` gate at [`PAYLOAD`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CaseArm {
    pub(crate) gate: CaseGate,
    pub(crate) body: ScalarProgram,
    reads: Vec<SmolStr>,
}

impl CaseArm {
    pub(crate) fn new(gate: CaseGate, body: ScalarProgram) -> Self {
        let reads = body.input_fields();
        CaseArm { gate, body, reads }
    }
}

/// The rows an arm takes, among the rows no earlier arm took.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CaseGate {
    /// The rows where `program`, a `Bool` function of the captures it names in `reads`, holds.
    Holds {
        program: ScalarProgram,
        reads: Vec<SmolStr>,
    },
    /// Every row: the final `else`.
    Rest,
    /// The rows whose value in the union field `scrutinee` carries `tag`, with `shape` the empty
    /// column of the tag's payload.
    Tag {
        scrutinee: SmolStr,
        tag: FieldKey,
        shape: Shape,
    },
}

impl CaseGate {
    /// A `Holds` gate of `program`.
    pub(crate) fn holds(program: ScalarProgram) -> Self {
        let reads = program.input_fields();
        CaseGate::Holds { program, reads }
    }
}

/// A capture a `Case` hands its [`CaseFn`] for one block, borrowed from the program running it
/// where the column is already there.
pub(crate) enum Captured<'a> {
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
    pub(crate) fn reads_only<T>(&self, captures: &[(SmolStr, T)]) -> bool {
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

    /// One value per row of a block of `len` rows, whose captures are `captures`.
    pub(crate) fn eval(&self, captures: &[(SmolStr, Captured)], len: usize) -> ColumnValue {
        // Positions of the block no earlier arm took, ascending.
        let mut rest: Vec<RowIndex> = (0..len).collect();
        let mut results: Vec<ColumnValue> = Vec::with_capacity(self.arms.len());
        let mut takens: Vec<Vec<RowIndex>> = Vec::with_capacity(self.arms.len());
        for arm in &self.arms {
            let (taken, payload) = arm.select(captures, len, &mut rest);
            // One arm taking every row answers the whole block, so its result is not merged.
            if taken.len() == len && payload.is_none() && len > 0 {
                return arm.body.eval(&gather(captures, &arm.reads, None, len));
            }
            let mut arm_input = gather(captures, &arm.reads, Some(&taken), len);
            if let Some(payload) = payload {
                let ColumnValue::Records(fields) = &mut arm_input else {
                    unreachable!("a `CaseFn`'s input is a record column")
                };
                fields.insert(PAYLOAD.into(), payload);
            }
            results.push(arm.body.eval(&arm_input));
            takens.push(taken);
        }
        debug_assert!(rest.is_empty(), "the arms' gates split the rows");
        let parts = results.into_iter().zip(takens.iter().map(Vec::as_slice));
        merge_parts(parts.collect(), len)
    }
}

impl CaseArm {
    /// The positions of `rest` this arm takes, removed from `rest`, and for a `Tag` gate their
    /// payloads, in a block of `len` rows.
    fn select(
        &self,
        captures: &[(SmolStr, Captured)],
        len: usize,
        rest: &mut Vec<RowIndex>,
    ) -> (Vec<RowIndex>, Option<ColumnValue>) {
        match &self.gate {
            CaseGate::Rest => (std::mem::take(rest), None),
            CaseGate::Holds { program, reads } => {
                let holds = program.eval(&gather(captures, reads, Some(rest), len));
                let ColumnValue::Bools(holds) = holds else {
                    unreachable!("a gate yields a `Bool` column, got {holds:?}")
                };
                let mut taken = Vec::new();
                let mut left = Vec::with_capacity(rest.len());
                for (&p, holds) in rest.iter().zip(holds) {
                    if holds {
                        taken.push(p);
                    } else {
                        left.push(p);
                    }
                }
                *rest = left;
                (taken, None)
            }
            // The rows of the union arm and of `rest` are both ascending, so one walk pairs them.
            CaseGate::Tag {
                scrutinee,
                tag,
                shape,
            } => {
                let (union, offset) = match captured(captures, scrutinee) {
                    Captured::Column(column, offset) => (*column, *offset),
                    Captured::Owned(column) => (column, 0),
                    Captured::View(_) => unreachable!("a union has no view"),
                };
                let ColumnValue::Union(arms) = union else {
                    unreachable!("a `Tag` gate reads a union column, got {union:?}")
                };
                let Some(arm) = arms.get(tag) else {
                    return (Vec::new(), Some(shape.0.clone()));
                };
                let mut taken = Vec::new();
                let mut slots = Vec::new();
                let mut left = Vec::with_capacity(rest.len());
                // The arm's rows before the block are skipped by a search, not a walk.
                let first = arm.rows().partition_point(|&row| row < offset);
                let mut rows = arm.rows()[first..]
                    .iter()
                    .enumerate()
                    .map(|(i, &row)| (row, first + i))
                    .peekable();
                for &p in rest.iter() {
                    let row_of_p = offset + p;
                    while rows.next_if(|(row, _)| *row < row_of_p).is_some() {}
                    match rows.peek() {
                        Some(&(row, slot)) if row == row_of_p => {
                            taken.push(p);
                            slots.push(slot);
                        }
                        _ => left.push(p),
                    }
                }
                *rest = left;
                let payload = arm
                    .values()
                    .select_indices(slots.iter().copied(), slots.len());
                (taken, Some(payload))
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
/// rows, in order, or at every row of it when `positions` is `None`.
fn gather(
    captures: &[(SmolStr, Captured)],
    reads: &[SmolStr],
    positions: Option<&[RowIndex]>,
    len: usize,
) -> ColumnValue {
    let rows = positions.map_or(len, <[RowIndex]>::len);
    let mut fields: std::collections::HashMap<SmolStr, ColumnValue> = reads
        .iter()
        .map(|name| {
            let column = match (captured(captures, name), positions) {
                (Captured::View(view), Some(positions)) => view.gather(positions),
                (Captured::View(view), None) => {
                    let mut column = view.empty_like();
                    column.extend_from_view(*view);
                    column
                }
                (Captured::Column(column, offset), Some(positions)) => {
                    column.select_indices(positions.iter().map(|&p| offset + p), positions.len())
                }
                (Captured::Column(column, offset), None) => column.slice(*offset..offset + len),
                (Captured::Owned(column), Some(positions)) => {
                    column.select_indices(positions.iter().copied(), positions.len())
                }
                (Captured::Owned(column), None) => column.clone(),
            };
            (name.clone(), column)
        })
        .collect();
    fields.insert(ROWS.into(), ColumnValue::Units(rows));
    ColumnValue::Records(fields)
}

/// One arm of a merged union column: its tag, the parts' payloads for it concatenated, and each
/// row's position in the merged column with its index in those payloads.
type MergedArm = (FieldKey, ColumnValue, Vec<(RowIndex, usize)>);

/// One column of `len` rows from `parts`: the row at position `p` is the next row of the one part
/// whose positions hold `p`. The parts' positions are ascending and together hold each of `0..len`
/// once. A record merges field by field, and a union arm by arm, each row keeping its tag.
fn merge_parts(parts: Vec<(ColumnValue, &[RowIndex])>, len: usize) -> ColumnValue {
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
                        let rows = rows.iter().map(|(p, _)| *p).collect();
                        (tag, UnionArm::new(rows, values))
                    })
                    .collect(),
            ))
        }
        other => panic!("a `Case` merges columns of base types, records and unions, got {other:?}"),
    }
}

/// The most search nodes [`gates_split_the_rows`] visits before it gives up on a conditional, a
/// compile-time budget: a conditional whose proof needs more is not fused.
const SPLIT_BUDGET: usize = 4096;

/// One node of [`Formulas`]. A node's operands come before it.
pub(super) enum Node {
    /// A `Bool` value no `and`, `or` or `not` produces; the node stands for one such value.
    Atom,
    Known(bool),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
}

/// Gates as formulas over atoms, held as one graph: a formula two gates share, or that one gate
/// reads twice, is one node.
#[derive(Default)]
pub(super) struct Formulas {
    nodes: Vec<Node>,
}

impl Formulas {
    pub(super) fn push(&mut self, node: Node) -> usize {
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
pub(super) fn gates_split_the_rows(formulas: &Formulas, gates: &[usize]) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;

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
        let parity = |n: u32| {
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
}
