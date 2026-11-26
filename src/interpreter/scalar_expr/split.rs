//! Whether a conditional's `Holds` gates split the rows: [`gates_split_the_rows`].

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
