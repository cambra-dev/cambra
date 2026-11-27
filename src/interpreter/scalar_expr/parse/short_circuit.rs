//! Recognize each short-circuit `and` and `or` of a finished scalar program as a `Predicate`.
//!
//! A `Bin` instruction of `and` or `or` evaluates both operands at every row of the block. A
//! `Predicate` tests its right operand, copied into an operand sub-program, only on the rows the
//! left operand leaves undecided. The design is in `src/interpreter/design-operators.md`,
//! "Predicates".

use std::collections::HashMap;

use smol_str::SmolStr;

use super::super::case::{CaseGate, SubProgram};
use super::super::junction::{Junction, JunctionFn};
use super::super::{Instr, ScalarProgram, Slot};
use crate::interpreter::{BinOpKind as InterpreterBinOp, LogicKind};

/// `program`, as the parser emits it, with each `and` and `or` whose right operand the left
/// operand does not read made a `Predicate`, in it and in the gates and bodies of its conditionals.
pub(super) fn short_circuit(mut program: ScalarProgram) -> ScalarProgram {
    for instr in &mut program.instrs {
        debug_assert!(
            !matches!(instr, Instr::Predicate { .. }),
            "the parser emits no `Predicate`"
        );
        if let Instr::Case { case, .. } = instr {
            for arm in &mut case.arms {
                arm.body = rebuilt(&arm.body);
                if let CaseGate::Holds(gate) = &mut arm.gate {
                    *gate = rebuilt(gate);
                }
            }
        }
    }
    junctions(program)
}

/// `program` with each of its own `and` and `or` instructions made a `Predicate`, the programs it
/// holds already passed through [`short_circuit`].
fn junctions(mut program: ScalarProgram) -> ScalarProgram {
    while reassociate(&mut program) {}
    while let Some((at, cone)) = next_junction(&program) {
        program = extract(program, at, &cone);
    }
    program
}

/// For each slot of `instrs`, the instructions that read it.
fn users(instrs: &[Instr]) -> Vec<Vec<usize>> {
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); instrs.len()];
    for (user, instr) in instrs.iter().enumerate() {
        for slot in instr.operands() {
            users[slot as usize].push(user);
        }
    }
    users
}

/// Rewrite the first `𝑎 and (𝑏 and 𝑐)` of `program` to `(𝑎 and 𝑏) and 𝑐` in place, and the same
/// for `or`, and return whether there was one. The inner `and` must be read only by the outer one
/// and come after `𝑎`, so its slot can hold `𝑎 and 𝑏`. Both forms test `𝑏` only where `𝑎` leaves
/// the row undecided and `𝑐` only where `𝑎` and `𝑏` do. Left-nested, [`extract`] splices the
/// inner predicate's operands into the outer one's.
fn reassociate(program: &mut ScalarProgram) -> bool {
    let instrs = &mut program.instrs;
    let users = users(instrs);
    let Some((outer, inner)) = instrs.iter().enumerate().find_map(|(at, instr)| {
        let (junction, a, s) = junction_of(instr)?;
        let (inner, _, _) = junction_of(&instrs[s as usize])?;
        (inner == junction && a < s && users[s as usize] == [at]).then_some((at, s))
    }) else {
        return false;
    };
    let (Instr::Bin(op, a, _), Instr::Bin(_, b, c)) =
        (instrs[outer].clone(), instrs[inner as usize].clone())
    else {
        unreachable!("a junction is a `Bin` instruction")
    };
    instrs[inner as usize] = Instr::Bin(op, a, b);
    instrs[outer] = Instr::Bin(op, inner, c);
    true
}

/// `sub` with its program passed through [`short_circuit`].
fn rebuilt(sub: &SubProgram) -> SubProgram {
    SubProgram::new(short_circuit(sub.program.clone()))
}

/// The junction and the operands of an `and` or `or` instruction.
fn junction_of(instr: &Instr) -> Option<(Junction, Slot, Slot)> {
    match instr {
        Instr::Bin(InterpreterBinOp::BoolLogic(LogicKind::And), a, b) => {
            Some((Junction::And, *a, *b))
        }
        Instr::Bin(InterpreterBinOp::BoolLogic(LogicKind::Or), a, b) => {
            Some((Junction::Or, *a, *b))
        }
        _ => None,
    }
}

/// The slots `slot` reads, directly or through other slots, and `slot` itself.
fn reach(instrs: &[Instr], slot: usize) -> Vec<bool> {
    let mut reach = vec![false; instrs.len()];
    reach[slot] = true;
    for s in (0..=slot).rev() {
        if reach[s] {
            for read in instrs[s].operands() {
                reach[read as usize] = true;
            }
        }
    }
    reach
}

/// The first `and` or `or` of `program` whose right operand it can test only where the left
/// operand leaves the row undecided, with the slots its operand computes: every slot other than
/// an input that the right operand reads, apart from those the left operand reads. The left
/// operand is computed at every row of the junction, so a slot it reads is read as a capture. A
/// right operand that the left one reads, or that is an input or a constant, stays. So does one
/// whose instructions read a constructor, which no capture can hold.
fn next_junction(program: &ScalarProgram) -> Option<(usize, Vec<bool>)> {
    let instrs = &program.instrs;
    instrs.iter().enumerate().find_map(|(at, instr)| {
        let (_, a, b) = junction_of(instr)?;
        let b = b as usize;
        if matches!(instrs[b], Instr::Input { .. } | Instr::Const(_)) {
            return None;
        }
        let left = reach(instrs, a as usize);
        if left[b] {
            return None;
        }
        let mut cone = reach(instrs, b);
        for (slot, instr) in instrs.iter().enumerate() {
            cone[slot] &= !left[slot] && !matches!(instr, Instr::Input { .. });
        }
        let captures_hold_views = (0..instrs.len())
            .filter(|&slot| cone[slot])
            .flat_map(|slot| instrs[slot].operands())
            .all(|read| cone[read as usize] || !instrs[read as usize].is_constructor());
        captures_hold_views.then_some((at, cone))
    })
}

/// The name of the capture of `slot` in `captures`, added if it is not there yet.
fn capture(slot: Slot, captures: &mut Vec<(SmolStr, Slot)>) -> SmolStr {
    match captures.iter().find(|(_, s)| *s == slot) {
        Some((name, _)) => name.clone(),
        None => {
            let name: SmolStr = format!("c{}", captures.len()).into();
            captures.push((name.clone(), slot));
            name
        }
    }
}

/// `operand` with each capture it reads renamed by `names`.
fn renamed(operand: &SubProgram, names: &HashMap<SmolStr, SmolStr>) -> SubProgram {
    let instrs = operand
        .program
        .instrs
        .iter()
        .map(|instr| match instr {
            Instr::Input { path } => {
                let (name, rest) = path.split_first().expect("an operand reads only captures");
                let mut path = vec![names[name].clone()];
                path.extend_from_slice(rest);
                Instr::Input { path }
            }
            instr => instr.clone(),
        })
        .collect();
    SubProgram::new(ScalarProgram { instrs })
}

/// `program` with the `and` or `or` at `at` made a `Predicate`: its right operand the
/// instructions in `cone`, copied into an operand. A slot of `cone` that only the operand reads
/// leaves `program`; one that another instruction reads stays for it too, so each operand that
/// reads a shared slot computes it on its own rows. A left operand that is a predicate of the same
/// junction, read only here, gives its operands, which come first; any other left operand is read
/// as a capture.
fn extract(program: ScalarProgram, at: usize, cone: &[bool]) -> ScalarProgram {
    let mut instrs = program.instrs;
    let (junction, a, b) = junction_of(&instrs[at]).expect("`next_junction` found a junction");
    // Users have higher slots than what they read, so one pass from the last slot down sees
    // every user of a slot before the slot.
    let users = users(&instrs);
    let mut moved = vec![false; instrs.len()];
    for slot in (0..instrs.len()).rev() {
        moved[slot] = cone[slot] && users[slot].iter().all(|&user| user == at || moved[user]);
    }
    let mut captures: Vec<(SmolStr, Slot)> = Vec::new();
    // A slot outside the operand: a constant, copied, or a capture, read as an input.
    let outside = |slot: Slot,
                   captures: &mut Vec<(SmolStr, Slot)>,
                   operand: &mut Vec<Instr>,
                   local: &mut HashMap<Slot, Slot>| {
        if let Some(&local) = local.get(&slot) {
            return local;
        }
        let instr = match &instrs[slot as usize] {
            Instr::Const(value) => Instr::Const(value.clone()),
            _ => Instr::Input {
                path: vec![capture(slot, captures)],
            },
        };
        operand.push(instr);
        let new = (operand.len() - 1) as Slot;
        local.insert(slot, new);
        new
    };
    let mut operands = Vec::new();
    let spliced = match &instrs[a as usize] {
        Instr::Predicate {
            junction: inner,
            captures: inner_captures,
        } if inner.junction == junction && users[a as usize] == [at] => {
            let names: HashMap<SmolStr, SmolStr> = inner_captures
                .iter()
                .map(|(name, slot)| (name.clone(), capture(*slot, &mut captures)))
                .collect();
            operands.extend(
                inner
                    .operands
                    .iter()
                    .map(|operand| renamed(operand, &names)),
            );
            true
        }
        _ => false,
    };
    if spliced {
        moved[a as usize] = true;
    } else {
        let mut left = Vec::new();
        outside(a, &mut captures, &mut left, &mut HashMap::new());
        operands.push(SubProgram::new(ScalarProgram { instrs: left }));
    }
    let mut right = Vec::new();
    let mut local: HashMap<Slot, Slot> = HashMap::new();
    for slot in (0..instrs.len()).filter(|&slot| cone[slot]) {
        let instr = instrs[slot].with_operands(|read| {
            if cone[read as usize] {
                local[&read]
            } else {
                outside(read, &mut captures, &mut right, &mut local)
            }
        });
        right.push(instr);
        local.insert(slot as Slot, (right.len() - 1) as Slot);
    }
    debug_assert_eq!(
        local[&b] as usize,
        right.len() - 1,
        "the right operand is the operand's last instruction"
    );
    // The operand's conditionals and predicates were copied from `program`, which already
    // passed them through `short_circuit`.
    operands.push(SubProgram::new(junctions(ScalarProgram { instrs: right })));
    let junction = JunctionFn { junction, operands };
    debug_assert!(
        junction.reads_only(&captures),
        "every capture a predicate's operands read is one the predicate hands them"
    );
    instrs[at] = Instr::Predicate {
        junction: Box::new(junction),
        captures,
    };
    let mut renumbered: Vec<Slot> = Vec::with_capacity(instrs.len());
    let mut kept = Vec::with_capacity(instrs.len());
    for (slot, instr) in instrs.iter().enumerate() {
        renumbered.push(kept.len() as Slot);
        if !moved[slot] {
            kept.push(instr.with_operands(|read| {
                debug_assert!(
                    !moved[read as usize],
                    "only the predicate reads a moved slot"
                );
                renumbered[read as usize]
            }));
        }
    }
    ScalarProgram { instrs: kept }
}

#[cfg(test)]
mod tests {
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Expr, LogicKind};
    use crate::interpreter::ColumnValue;
    use crate::interpreter::scalar_expr::eval::BLOCK_ROWS;
    use crate::interpreter::scalar_expr::tests::*;
    use crate::interpreter::scalar_expr::{Instr, ScalarProgram};

    /// `𝑎 and 𝑏` or `𝑎 or 𝑏` as a chain over `x`.
    fn junction(kind: LogicKind, a: Expr, b: Expr) -> Vec<Expr> {
        vec![zip(vec![a, b]), binop(BinOpKind::BoolLogic(kind))]
    }

    /// `𝑛 // x > 𝑚`, which divides by zero at `x = 0`.
    fn divides_above(n: i64, m: i64) -> Expr {
        Expr::compose(vec![
            zip(vec![constant(n), id()]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::FloorDiv)),
            compare(CompareKind::Greater, m),
        ])
    }

    /// `𝑛 // x > 𝑚` rounded toward negative infinity, as `//` is.
    fn floor_div_above(n: i64, x: i64, m: i64) -> bool {
        let q = n / x;
        let q = if n % x != 0 && (n < 0) != (x < 0) {
            q - 1
        } else {
            q
        };
        q > m
    }

    /// Three blocks of `x` from -3 to 9 in a scrambled order, with zeros in every block.
    fn scrambled() -> Vec<i64> {
        (0..3 * BLOCK_ROWS as i64)
            .map(|i| (i * 7919) % 13 - 3)
            .collect()
    }

    fn eval(chain: &[Expr], xs: Vec<i64>) -> ColumnValue {
        let fused = fuse(chain, &int()).expect("the chain fuses");
        assert!(
            !predicate_operands(&fused.program).is_empty(),
            "{}",
            fused.program
        );
        fused.program.eval(&ColumnValue::Ints(xs))
    }

    /// `x != 0 and 10 // x > 1` tests the division only where `x != 0`, so no row divides by zero.
    #[test]
    fn an_and_tests_its_right_operand_only_where_the_left_holds() {
        let chain = junction(
            LogicKind::And,
            compare(CompareKind::NotEquals, 0),
            divides_above(10, 1),
        );
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x != 0 && floor_div_above(10, x, 1))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// `x == 0 or 10 // x > 1` tests the division only where `x != 0`.
    #[test]
    fn an_or_tests_its_right_operand_only_where_the_left_fails() {
        let chain = junction(
            LogicKind::Or,
            compare(CompareKind::Equals, 0),
            divides_above(10, 1),
        );
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x == 0 || floor_div_above(10, x, 1))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// `x != 0 and (x > 5 or 100 // x > 30)`: the inner `or` is an operand of the `and`, and its
    /// division runs only where `x != 0` and `x <= 5`.
    #[test]
    fn a_junction_nests_in_an_operand() {
        let inner = Expr::compose(junction(
            LogicKind::Or,
            compare(CompareKind::Greater, 5),
            divides_above(100, 30),
        ));
        let chain = junction(LogicKind::And, compare(CompareKind::NotEquals, 0), inner);
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x != 0 && (x > 5 || floor_div_above(100, x, 30)))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// The operand counts of the predicates in `program`, in order.
    fn predicate_operands(program: &ScalarProgram) -> Vec<usize> {
        program
            .instrs
            .iter()
            .filter_map(|instr| match instr {
                Instr::Predicate { junction, .. } => Some(junction.operands.len()),
                _ => None,
            })
            .collect()
    }

    /// `(x != 0 and x > -2) and 10 // x > 1` and `x != 0 and (x > -2 and 10 // x > 1)` are each
    /// one predicate of three operands.
    #[rstest::rstest]
    #[case::left_nested(false)]
    #[case::right_nested(true)]
    fn a_chain_of_one_junction_is_one_predicate(#[case] right_nested: bool) {
        let (p, q, r) = (
            compare(CompareKind::NotEquals, 0),
            compare(CompareKind::Greater, -2),
            divides_above(10, 1),
        );
        let chain = if right_nested {
            junction(
                LogicKind::And,
                p,
                Expr::compose(junction(LogicKind::And, q, r)),
            )
        } else {
            junction(
                LogicKind::And,
                Expr::compose(junction(LogicKind::And, p, q)),
                r,
            )
        };
        let fused = fuse(&chain, &int()).expect("the chain fuses");
        assert_eq!(predicate_operands(&fused.program), [3], "{}", fused.program);
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x != 0 && x > -2 && floor_div_above(10, x, 1))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// `(x == 0 or x > 5) and x != 0` mixes junctions, so the `or` stays a predicate that
    /// the `and` reads from its slot as a capture.
    #[test]
    fn a_chain_of_two_junctions_stays_nested() {
        let chain = junction(
            LogicKind::And,
            Expr::compose(junction(
                LogicKind::Or,
                compare(CompareKind::Equals, 0),
                compare(CompareKind::Greater, 5),
            )),
            compare(CompareKind::NotEquals, 0),
        );
        let fused = fuse(&chain, &int()).expect("the chain fuses");
        assert_eq!(
            predicate_operands(&fused.program),
            [2, 2],
            "{}",
            fused.program
        );
        let xs = scrambled();
        let want = xs.iter().map(|&x| (x == 0 || x > 5) && x != 0).collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// A block where an operand holds at every row or at none moves its rows whole: here a block
    /// of zeros, a block of fives, and a mixed block, through `x != 0 and 10 // x > 1` and
    /// `x == 0 or 10 // x > 1`.
    #[rstest::rstest]
    #[case::and(LogicKind::And, CompareKind::NotEquals)]
    #[case::or(LogicKind::Or, CompareKind::Equals)]
    fn a_block_an_operand_does_not_split_moves_whole(
        #[case] kind: LogicKind,
        #[case] left: CompareKind,
    ) {
        let chain = junction(kind, compare(left, 0), divides_above(10, 1));
        let mut xs = vec![0; BLOCK_ROWS];
        xs.extend(std::iter::repeat_n(5, BLOCK_ROWS));
        xs.extend(scrambled().into_iter().take(BLOCK_ROWS));
        let want = xs
            .iter()
            .map(|&x| match kind {
                LogicKind::And => x != 0 && floor_div_above(10, x, 1),
                _ => x == 0 || floor_div_above(10, x, 1),
            })
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// `x == 0 or 10 // x > 4 or 10 // x > 1` and `x == 0 or 10 // x > 1 or 10 // x > 1`: the
    /// fusion parser gives the equal instructions one slot, and each operand that reads the shared
    /// division computes it on its own rows, so no row divides by zero.
    #[rstest::rstest]
    #[case::a_shared_division(4)]
    #[case::a_repeated_operand(1)]
    fn operands_compute_what_they_share(#[case] m: i64) {
        let chain = junction(
            LogicKind::Or,
            Expr::compose(junction(
                LogicKind::Or,
                compare(CompareKind::Equals, 0),
                divides_above(10, m),
            )),
            divides_above(10, 1),
        );
        let fused = fuse(&chain, &int()).expect("the chain fuses");
        assert_eq!(predicate_operands(&fused.program), [3], "{}", fused.program);
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x == 0 || floor_div_above(10, x, m) || floor_div_above(10, x, 1))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// `x == 0 or (x > 2 and 10 // x > 1)`: the `or` reads its second operand through a
    /// predicate root, which answers only the rows it fails on, and the division runs only where
    /// `x != 0` and `x > 2`.
    #[test]
    fn an_or_tests_a_nested_and_on_its_undecided_rows() {
        let chain = junction(
            LogicKind::Or,
            compare(CompareKind::Equals, 0),
            Expr::compose(junction(
                LogicKind::And,
                compare(CompareKind::Greater, 2),
                divides_above(10, 1),
            )),
        );
        let fused = fuse(&chain, &int()).expect("the chain fuses");
        assert_eq!(predicate_operands(&fused.program), [2], "{}", fused.program);
        let xs = scrambled();
        let want = xs
            .iter()
            .map(|&x| x == 0 || (x > 2 && floor_div_above(10, x, 1)))
            .collect();
        assert_eq!(eval(&chain, xs), ColumnValue::Bools(want));
    }

    /// A right operand that the left one also computes stays an operand of a strict `and`: it is
    /// evaluated at every row anyway.
    #[test]
    fn a_shared_right_operand_stays_strict() {
        let chain = junction(
            LogicKind::And,
            compare(CompareKind::Greater, 1),
            compare(CompareKind::Greater, 1),
        );
        let fused = fuse(&chain, &int()).expect("the chain fuses");
        assert!(
            predicate_operands(&fused.program).is_empty(),
            "{}",
            fused.program
        );
    }
}
