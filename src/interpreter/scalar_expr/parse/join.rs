//! Recognize a conditional, a `DisjointJoin`, as a `Case` applying a [`CaseFn`]. The arms' gates
//! are proved to split the rows, and each arm is outlined into programs of its own.

use std::collections::HashMap;

use smol_str::SmolStr;

use super::super::case::{CaseArm, CaseFn, CaseGate, PAYLOAD, Shape};
use super::super::split::{Formulas, Node, gates_split_the_rows};
use super::super::{Instr, ScalarProgram, Slot};
use super::{Parser, Val, is_plain};
use crate::ccl::{Builtin, Expr, FieldKey, TypedExprNode};
use crate::interpreter::{
    BaseType, BinOpKind as InterpreterBinOp, ColumnValue, Extent, LogicKind, UnaryOpKind, Value,
};

/// A `DisjointJoin` operand as parsed in the enclosing program: what selects its rows, and the
/// value its chain ends at.
struct ParsedArm {
    gate: ParsedGate,
    result: Val,
}

/// What selects a `DisjointJoin` operand's rows, as parsed in the enclosing program.
enum ParsedGate {
    /// The rows where the `Bool` slot holds.
    Holds(Slot),
    /// The rows whose value in the union slot `union` carries `tag`. `tags` are the tags of the
    /// union's extent. The operand reads its payloads, of `payload` extent, through the input path
    /// `placeholder`, which no input has and which outlining replaces by [`PAYLOAD`].
    Tag {
        union: Slot,
        tag: FieldKey,
        tags: Vec<FieldKey>,
        placeholder: SmolStr,
        payload: Extent,
    },
}

/// What a `DisjointJoin` operand's gate opens ([`Parser::gate`]).
enum Opened {
    /// The gate, and the value the operand's chain continues from.
    Arm(ParsedGate, Val),
    /// A `variant_project` of a variant built in the chain, whose tag is known: the payload when
    /// the tag is the one projected, and `None` when the operand holds no row.
    Known(Option<Val>),
}

/// What an arm takes among the rows no earlier arm took, once the split is proved.
enum Guard {
    /// The rows where the `Bool` slot holds.
    Holds(Slot),
    /// Every row.
    Rest,
    /// The rows its `Tag` gate selects.
    Tag,
}

/// A value an outlined program reads from the enclosing one: an input path, or a slot emitted
/// before the conditional.
#[derive(PartialEq)]
enum Capture {
    Input(Vec<SmolStr>),
    Slot(Slot),
}

impl Parser<'_> {
    /// `e`, a `DisjointJoin` of `operands`, applied to `cur`: one `Case` whose arms are the
    /// operands, each outlined into its own programs over the values it reads. See
    /// `src/ccl/design/optimization.md`, "A conditional in an element-wise chain".
    pub(super) fn join(&mut self, e: &Expr, operands: &[Expr], cur: Val) -> Option<Val> {
        let start = self.instrs.len();
        let joined = self.join_arms(e, operands, cur, start);
        if joined.is_none() {
            self.truncate(start);
        }
        joined
    }

    fn join_arms(&mut self, e: &Expr, operands: &[Expr], cur: Val, start: usize) -> Option<Val> {
        let mut arms: Vec<ParsedArm> = Vec::new();
        let mut known: Option<(Vec<&Expr>, Val)> = None;
        for operand in operands {
            let elements = flattened(operand);
            let (opened, rest) = self.gate(&elements, cur.clone())?;
            match opened {
                Opened::Known(None) => {}
                Opened::Known(Some(payload)) => {
                    if known.replace((rest, payload)).is_some() {
                        return None;
                    }
                }
                Opened::Arm(gate, arm_cur) => {
                    let result = rest.iter().try_fold(arm_cur, |cur, e| self.step(e, cur))?;
                    arms.push(ParsedArm { gate, result });
                }
            }
        }
        // A `match` on a variant built in the chain is the one operand naming its tag.
        if let Some((rest, payload)) = known {
            return if arms.is_empty() {
                rest.iter().try_fold(payload, |cur, e| self.step(e, cur))
            } else {
                None
            };
        }
        let guards = self.split(&arms)?;
        let codomain = (self.extent_of)(&e.ty.codomain()?)?;
        let constructs = matches!(
            codomain,
            Extent::Record(_) | Extent::Union(_) | Extent::Base(BaseType::Unit)
        );
        // A union an arm passes through from the input is copied as its column holds it, which may
        // carry record fields its extent does not name, so `merge_parts` could not combine it
        // with a union another arm builds.
        if constructs && arms.iter().any(|arm| passes_a_union_through(&arm.result)) {
            return None;
        }
        let mut results = Vec::with_capacity(arms.len());
        for arm in &arms {
            let (slot, extent) = if constructs {
                self.output(&arm.result)?
            } else {
                self.column(&arm.result)?
            };
            // Each arm's column must have the join's layout, which `merge_parts` combines: a
            // record arm wider than the join's type would carry a field the others lack.
            if !fits(&extent, &codomain) {
                return None;
            }
            results.push(slot);
        }
        let mut captures: Vec<Capture> = Vec::new();
        let mut case_arms = Vec::with_capacity(arms.len());
        for ((arm, guard), result) in arms.iter().zip(guards).zip(results) {
            let (gate, own) = match (guard, &arm.gate) {
                (Guard::Holds(b), _) => (
                    CaseGate::holds(self.outline(b, start, None, &mut captures)),
                    None,
                ),
                (Guard::Rest, _) => (CaseGate::Rest, None),
                (
                    Guard::Tag,
                    ParsedGate::Tag {
                        union,
                        tag,
                        placeholder,
                        payload,
                        ..
                    },
                ) => {
                    let scrutinee = self.capture(*union, start, &mut captures);
                    let shape = Shape(ColumnValue::from_values(Vec::new(), payload));
                    let gate = CaseGate::Tag {
                        scrutinee,
                        tag: tag.clone(),
                        shape,
                    };
                    (gate, Some(placeholder))
                }
                (Guard::Tag, ParsedGate::Holds(_)) => {
                    unreachable!("a `Tag` guard has a `Tag` gate")
                }
            };
            let body = self.outline(result, start, own, &mut captures);
            case_arms.push(CaseArm::new(gate, body));
        }
        // The conditional's arms read only their own programs and the captures, so what the
        // enclosing program emitted for them is discarded, and the captures are read anew.
        self.truncate(start);
        let captures: Vec<(SmolStr, Slot)> = captures
            .into_iter()
            .enumerate()
            .map(|(i, capture)| {
                let slot = match capture {
                    Capture::Input(path) => self.input(&path),
                    Capture::Slot(slot) => slot,
                };
                (capture_name(i), slot)
            })
            .collect();
        let shape = Shape(ColumnValue::from_values(Vec::new(), &codomain));
        let case = CaseFn { arms: case_arms };
        debug_assert!(
            case.reads_only(&captures),
            "every capture a `CaseFn` reads is one its `Case` hands it"
        );
        debug_assert_eq!(
            constructs,
            shape.0.view().is_none(),
            "a `Case` constructs exactly when its result has no view"
        );
        let case = self.emit(Instr::Case {
            case: Box::new(case),
            captures,
            constructs,
            shape,
        });
        Some(if constructs {
            Val::Built(case, codomain)
        } else {
            Val::Slot(case, codomain)
        })
    }

    /// The gate a `DisjointJoin` operand of `elements` opens on `cur`, with the elements after it.
    ///
    /// - ``(𝑔 ▷ filter_values) ≫ …`` holds where `𝑔` does.
    /// - ``𝑠 ≫ variant_project(`𝑐) ≫ …`` holds where `𝑠` carries `𝑐`, and the chain continues
    ///   from the payload.
    /// - ``(id, 𝑠 ≫ variant_project(`𝑐)) ▷ zip ≫ …`` holds there too, and the chain continues
    ///   from the pair of the element and the payload.
    fn gate<'e>(&mut self, elements: &[&'e Expr], cur: Val) -> Option<(Opened, Vec<&'e Expr>)> {
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
                    return Some((Opened::Arm(ParsedGate::Holds(b), cur), rest.to_vec()));
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
                            let (o, item_rest) = self.gate(&flattened(item), cur.clone())?;
                            let Opened::Arm(gate, payload) = o else {
                                return None;
                            };
                            let value = item_rest
                                .iter()
                                .try_fold(payload, |cur, e| self.step(e, cur))?;
                            vals.push(value);
                            opened = Some(gate);
                        } else {
                            vals.push(self.step(item, cur.clone())?);
                        }
                    }
                    return Some((Opened::Arm(opened?, Val::Tuple(vals)), rest.to_vec()));
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
        let tags = match &scrutinee {
            Val::Wrap(t, payload, _) => {
                let payload = (t == tag).then(|| (**payload).clone());
                return Some((Opened::Known(payload), rest));
            }
            Val::Read(_, Extent::Union(arms)) => arms.keys().cloned().collect(),
            _ => return None,
        };
        let payload = (self.extent_of)(&elements[k].ty.codomain()?)?;
        if !is_plain(&payload) {
            return None;
        }
        let (union, _) = self.copied(&scrutinee)?;
        let placeholder: SmolStr = format!("{PAYLOAD}{}", self.placeholders).into();
        self.placeholders += 1;
        let arm_cur = Val::Read(vec![placeholder.clone()], payload.clone());
        let gate = ParsedGate::Tag {
            union,
            tag: tag.clone(),
            tags,
            placeholder,
            payload,
        };
        Some((Opened::Arm(gate, arm_cur), rest))
    }

    /// What each arm takes among the rows no earlier arm took, when the arms' gates split the
    /// rows, by one of three rules:
    ///
    /// - `lambda_elim`'s first-match gates, `𝑔ᵢ ∧ ¬𝑔₀ ∧ … ∧ ¬𝑔ᵢ₋₁` with a final guard of `true`
    ///   (`synthesize_arm_predicate`), split the rows by construction. Among the rows no earlier
    ///   arm took, arm `𝑖` takes those where `𝑔ᵢ` holds, and the last arm takes the rest.
    /// - Other `Holds` gates split the rows when [`gates_split_the_rows`] proves it, and each arm
    ///   tests its whole gate.
    /// - `Tag` gates split the rows when they read one union, name distinct tags, and name every
    ///   tag of its extent.
    fn split(&self, arms: &[ParsedArm]) -> Option<Vec<Guard>> {
        let holds: Option<Vec<Slot>> = arms
            .iter()
            .map(|arm| match arm.gate {
                ParsedGate::Holds(b) => Some(b),
                ParsedGate::Tag { .. } => None,
            })
            .collect();
        if let Some(gates) = holds {
            if let Some(guards) = self.first_match(&gates) {
                return Some(guards);
            }
            let mut formulas = Formulas::default();
            let mut nodes = HashMap::new();
            let roots: Vec<usize> = gates
                .iter()
                .map(|&b| self.formula(b, &mut formulas, &mut nodes))
                .collect();
            return gates_split_the_rows(&formulas, &roots)
                .then(|| gates.into_iter().map(Guard::Holds).collect());
        }
        let mut union_slot = None;
        let mut named: Vec<&FieldKey> = Vec::new();
        let mut union_tags: &[FieldKey] = &[];
        for arm in arms {
            let ParsedGate::Tag {
                union, tag, tags, ..
            } = &arm.gate
            else {
                return None;
            };
            if union_slot.replace(*union).is_some_and(|u| u != *union) || named.contains(&tag) {
                return None;
            }
            named.push(tag);
            union_tags = tags;
        }
        union_tags
            .iter()
            .all(|tag| named.contains(&tag))
            .then(|| arms.iter().map(|_| Guard::Tag).collect())
    }

    /// The guards of `gates` when they have `lambda_elim`'s first-match shape: gate `𝑖` is its
    /// guard `𝑔ᵢ` conjoined with the negation of every earlier guard, and the last gate's guard is
    /// `true`, so it reads as [`Guard::Rest`].
    fn first_match(&self, gates: &[Slot]) -> Option<Vec<Guard>> {
        let negation_of = |slot: Slot, guards: &[Slot]| match self.instrs[slot as usize] {
            Instr::Un(UnaryOpKind::Not, a) if guards.contains(&a) => Some(a),
            _ => None,
        };
        let mut guards: Vec<Slot> = Vec::new();
        let mut out = Vec::with_capacity(gates.len());
        for (i, &gate) in gates.iter().enumerate() {
            let mut negated: Vec<Slot> = Vec::new();
            let mut guard = Some(gate);
            while let Some(slot) = guard {
                match &self.instrs[slot as usize] {
                    Instr::Bin(InterpreterBinOp::BoolLogic(LogicKind::And), a, b) => {
                        if let Some(g) = negation_of(*b, &guards) {
                            negated.push(g);
                            guard = Some(*a);
                        } else if let Some(g) = negation_of(*a, &guards) {
                            negated.push(g);
                            guard = Some(*b);
                        } else {
                            break;
                        }
                    }
                    Instr::Un(UnaryOpKind::Not, _) if negation_of(slot, &guards).is_some() => {
                        negated.extend(negation_of(slot, &guards));
                        guard = None;
                    }
                    Instr::Const(Value::Bool(true)) => guard = None,
                    _ => break,
                }
            }
            negated.sort_unstable();
            negated.dedup();
            let mut earlier = guards.clone();
            earlier.sort_unstable();
            if negated != earlier {
                return None;
            }
            match guard {
                Some(g) => {
                    guards.push(g);
                    out.push(Guard::Holds(g));
                }
                None if i + 1 == gates.len() => out.push(Guard::Rest),
                None => return None,
            }
        }
        matches!(out.last(), Some(Guard::Rest)).then_some(out)
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
        let node = match &self.instrs[slot as usize] {
            Instr::Const(Value::Bool(value)) => Node::Known(*value),
            Instr::Un(UnaryOpKind::Not, a) => Node::Not(self.formula(*a, formulas, nodes)),
            Instr::Bin(InterpreterBinOp::BoolLogic(LogicKind::And), a, b) => Node::And(
                self.formula(*a, formulas, nodes),
                self.formula(*b, formulas, nodes),
            ),
            Instr::Bin(InterpreterBinOp::BoolLogic(LogicKind::Or), a, b) => Node::Or(
                self.formula(*a, formulas, nodes),
                self.formula(*b, formulas, nodes),
            ),
            _ => Node::Atom,
        };
        let node = formulas.push(node);
        nodes.insert(slot, node);
        node
    }

    /// The name of the capture reading `slot`, adding it to `captures`: an input path, or a slot
    /// emitted before `start`.
    fn capture(&self, slot: Slot, start: usize, captures: &mut Vec<Capture>) -> SmolStr {
        let capture = match &self.instrs[slot as usize] {
            Instr::Input { path } => Capture::Input(path.clone()),
            _ => {
                debug_assert!(
                    (slot as usize) < start,
                    "a capture reads an input or a slot emitted before the conditional"
                );
                Capture::Slot(slot)
            }
        };
        let i = match captures.iter().position(|c| *c == capture) {
            Some(i) => i,
            None => {
                captures.push(capture);
                captures.len() - 1
            }
        };
        capture_name(i)
    }

    /// The program computing `root` on its own: the instructions `root` reads from `start` on,
    /// copied, with each input and each earlier slot read as a capture. The input path `own`
    /// reads the arm's payloads, at [`PAYLOAD`].
    fn outline(
        &self,
        root: Slot,
        start: usize,
        own: Option<&SmolStr>,
        captures: &mut Vec<Capture>,
    ) -> ScalarProgram {
        let mut instrs = Vec::new();
        let mut copied = HashMap::new();
        self.copy(root, start, own, captures, &mut instrs, &mut copied);
        ScalarProgram { instrs }
    }

    fn copy(
        &self,
        slot: Slot,
        start: usize,
        own: Option<&SmolStr>,
        captures: &mut Vec<Capture>,
        instrs: &mut Vec<Instr>,
        copied: &mut HashMap<Slot, Slot>,
    ) -> Slot {
        if let Some(&new) = copied.get(&slot) {
            return new;
        }
        let mut copy = |slot: Slot, instrs: &mut Vec<Instr>, captures: &mut Vec<Capture>| {
            self.copy(slot, start, own, captures, instrs, copied)
        };
        let instr = match &self.instrs[slot as usize] {
            Instr::Const(value) => Instr::Const(value.clone()),
            Instr::Input { path } if own.is_some_and(|own| path.first() == Some(own)) => {
                let mut path = path.clone();
                path[0] = PAYLOAD.into();
                Instr::Input { path }
            }
            Instr::Input { .. } => Instr::Input {
                path: vec![self.capture(slot, start, captures)],
            },
            _ if (slot as usize) < start => Instr::Input {
                path: vec![self.capture(slot, start, captures)],
            },
            Instr::Bin(op, a, b) => {
                let a = copy(*a, instrs, captures);
                let b = copy(*b, instrs, captures);
                Instr::Bin(*op, a, b)
            }
            Instr::Un(op, a) => Instr::Un(*op, copy(*a, instrs, captures)),
            Instr::Record(fields) => Instr::Record(
                fields
                    .iter()
                    .map(|(name, field)| (name.clone(), copy(*field, instrs, captures)))
                    .collect(),
            ),
            Instr::Wrap { tag, payload } => Instr::Wrap {
                tag: tag.clone(),
                payload: copy(*payload, instrs, captures),
            },
            Instr::Case {
                case,
                captures: inner,
                constructs,
                shape,
            } => Instr::Case {
                case: case.clone(),
                captures: inner
                    .iter()
                    .map(|(name, capture)| (name.clone(), copy(*capture, instrs, captures)))
                    .collect(),
                constructs: *constructs,
                shape: shape.clone(),
            },
        };
        instrs.push(instr);
        let new = (instrs.len() - 1) as Slot;
        copied.insert(slot, new);
        new
    }
}

/// Whether `v` holds a union read from the input, which an output copies as its column holds it.
fn passes_a_union_through(v: &Val) -> bool {
    fn holds_a_union(extent: &Extent) -> bool {
        match extent {
            Extent::Union(_) => true,
            Extent::Record(fields) => fields.values().any(holds_a_union),
            _ => false,
        }
    }
    match v {
        Val::Read(_, extent) => holds_a_union(extent),
        Val::Tuple(items) => items.iter().any(passes_a_union_through),
        Val::Record(fields) => fields.iter().any(|(_, v)| passes_a_union_through(v)),
        Val::Wrap(_, payload, _) => passes_a_union_through(payload),
        Val::Slot(..) | Val::Const(..) | Val::Built(..) => false,
    }
}

/// The name of the `i`th capture in a `Case`'s input record.
fn capture_name(i: usize) -> SmolStr {
    format!("c{i}").into()
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
        (Extent::Base(base), Extent::Base(target)) => base == target,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Occurrence;
    use crate::ccl::RecordEntry;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Lit, LogicKind};
    use crate::ccl::{TagMap, Type};
    use crate::interpreter::{BaseType, UnionArm};

    use crate::interpreter::scalar_expr::tests::*;

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
                .any(|instr| matches!(instr, Instr::Case { .. })),
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

    /// Gates without the first-match shape are proved by the search, and each arm tests its whole
    /// gate on the rows no earlier arm took: ``(x > 5 ∧ x > 9) ⊔ (x > 5 ∧ ¬(x > 9)) ⊔ ¬(x > 5)``,
    /// each `▷ filter_values ≫` a constant.
    #[test]
    fn gates_without_the_first_match_shape_are_proved_by_search() {
        let int_ty = || Type::Base(BaseType::Int);
        let (five, nine) = (
            compare(CompareKind::Greater, 5),
            compare(CompareKind::Greater, 9),
        );
        let and = |a: Expr, b: Expr| {
            Expr::compose(vec![
                zip(vec![a, b]),
                binop(BinOpKind::BoolLogic(LogicKind::And)),
            ])
        };
        let chain = vec![joined(
            vec![
                filtered(and(five.clone(), nine.clone()), constant(2), int_ty()),
                filtered(and(five.clone(), negated(nine)), constant(1), int_ty()),
                filtered(negated(five), constant(0), int_ty()),
            ],
            int_ty(),
        )];
        let fused = fuse_typed(&chain, &int(), &[(int_ty(), int())]).expect("the search proves it");
        let out = fused
            .program
            .eval(&ColumnValue::Ints(vec![3, 7, 12, 5, 9, 10]));
        assert_eq!(
            out,
            ColumnValue::Ints(vec![0, 1, 2, 0, 1, 2]),
            "{}",
            fused.program
        );
    }

    /// First-match gates read as their guards: among the rows no earlier arm took, the second arm
    /// tests only `x > 9`, and the last arm takes the rest.
    #[test]
    fn first_match_gates_read_as_their_guards() {
        let int_ty = || Type::Base(BaseType::Int);
        let (nine, five) = (
            compare(CompareKind::Greater, 9),
            compare(CompareKind::Greater, 5),
        );
        let and = |a: Expr, b: Expr| {
            Expr::compose(vec![
                zip(vec![a, b]),
                binop(BinOpKind::BoolLogic(LogicKind::And)),
            ])
        };
        let chain = vec![joined(
            vec![
                filtered(nine.clone(), constant(2), int_ty()),
                filtered(
                    and(five.clone(), negated(nine.clone())),
                    constant(1),
                    int_ty(),
                ),
                filtered(and(negated(nine), negated(five)), constant(0), int_ty()),
            ],
            int_ty(),
        )];
        let fused = fuse_typed(&chain, &int(), &[(int_ty(), int())]).expect("first-match gates");
        let Some(Instr::Case { case, .. }) = fused.program.instrs.last() else {
            panic!("a `Case` result, got {}", fused.program)
        };
        let gates: Vec<String> = case
            .arms
            .iter()
            .map(|arm| match &arm.gate {
                CaseGate::Holds { program, .. } => program.to_string(),
                CaseGate::Rest => "else".into(),
                CaseGate::Tag { .. } => "tag".into(),
            })
            .collect();
        assert_eq!(
            gates,
            [
                "s0 = _.c0; s1 = 9; s2 = >(s0, s1); => s2",
                "s0 = _.c0; s1 = 5; s2 = >(s0, s1); => s2",
                "else"
            ]
        );
        let out = fused.program.eval(&ColumnValue::Ints(vec![3, 7, 12]));
        assert_eq!(out, ColumnValue::Ints(vec![0, 1, 2]));
    }

    /// A `match` inside a `match` arm reads the outer arm's payload as its union: over
    /// ``{`a{{`x{Int} | `y}} | `b}``, the `` `a `` arm matches its payload, ``(variant_project(`x)
    /// ≫ id * 2) ⊔ (variant_project(`y) ≫ 0 ▷ const)``, and the `` `b `` arm is `7`.
    #[test]
    fn a_match_inside_a_match_arm_reads_the_outer_payload() {
        let int_ty = || Type::Base(BaseType::Int);
        let unit_ty = || Type::Base(BaseType::Unit);
        let inner_ty = Type::variant(vec![(tag("x"), int_ty()), (tag("y"), unit_ty())]);
        let outer_ty = Type::variant(vec![(tag("a"), inner_ty.clone()), (tag("b"), unit_ty())]);
        let unit = || Extent::Base(BaseType::Unit);
        let inner = Extent::Union(TagMap::from_arms(vec![
            (tag("x"), int()),
            (tag("y"), unit()),
        ]));
        let outer = Extent::Union(TagMap::from_arms(vec![
            (tag("a"), inner.clone()),
            (tag("b"), unit()),
        ]));
        let project = |from: &Type, name: &str, payload: Type| {
            Expr::builtin(Builtin::VariantProject(tag(name)))
                .with_ty(Type::fun(from.clone(), payload))
        };
        let inner_match = joined(
            vec![
                Expr::compose(vec![
                    project(&inner_ty, "x", int_ty()),
                    arith(ArithmeticKind::Mul, 2),
                ]),
                Expr::compose(vec![project(&inner_ty, "y", unit_ty()), constant(0)]),
            ],
            int_ty(),
        );
        let chain = vec![joined(
            vec![
                Expr::compose(vec![project(&outer_ty, "a", inner_ty.clone()), inner_match]),
                Expr::compose(vec![project(&outer_ty, "b", unit_ty()), constant(7)]),
            ],
            int_ty(),
        )];
        let types = [
            (int_ty(), int()),
            (unit_ty(), unit()),
            (inner_ty, inner.clone()),
            (outer_ty, outer.clone()),
        ];
        let fused = fuse_typed(&chain, &outer, &types).expect("both matches name every tag");
        let n = 2_500;
        let value = |i: i64| match i % 3 {
            0 => Value::Union {
                tag: tag("a"),
                inner: Box::new(Value::Union {
                    tag: tag("x"),
                    inner: Box::new(Value::Int(i)),
                }),
            },
            1 => Value::Union {
                tag: tag("a"),
                inner: Box::new(Value::Union {
                    tag: tag("y"),
                    inner: Box::new(Value::Unit),
                }),
            },
            _ => Value::Union {
                tag: tag("b"),
                inner: Box::new(Value::Unit),
            },
        };
        let column = ColumnValue::from_values((0..n).map(value).collect(), &outer);
        let want = (0..n)
            .map(|i| match i % 3 {
                0 => i * 2,
                1 => 0,
                _ => 7,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            fused.program.eval(&column),
            ColumnValue::Ints(want),
            "{}",
            fused.program
        );
    }

    /// A conditional over a value computed before it captures that value's slot:
    /// ``x + 1 ≫ ((id > 5 ▷ filter_values ≫ id * 2) ⊔ (id > 5 ≫ not_fn ▷ filter_values ≫ 0 ▷
    /// const))``.
    #[test]
    fn a_conditional_captures_a_value_computed_before_it() {
        let int_ty = || Type::Base(BaseType::Int);
        let over = compare(CompareKind::Greater, 5);
        let chain = vec![
            arith(ArithmeticKind::Add, 1),
            joined(
                vec![
                    filtered(over.clone(), arith(ArithmeticKind::Mul, 2), int_ty()),
                    filtered(negated(over), constant(0), int_ty()),
                ],
                int_ty(),
            ),
        ];
        let fused = fuse_typed(&chain, &int(), &[(int_ty(), int())]).expect("the gates split");
        assert_eq!(fused.consumed, 2);
        let out = fused.program.eval(&ColumnValue::Ints(vec![3, 4, 5, 9]));
        assert_eq!(
            out,
            ColumnValue::Ints(vec![0, 0, 12, 20]),
            "{}",
            fused.program
        );
    }

    /// Two arms that build the same tag merge into one arm of the union, rows in order:
    /// ``(x > 1 ▷ filter_values ≫ variant_wrap(`some)) ⊔ (x > 1 ≫ not_fn ▷ filter_values ≫ 0 -
    /// x ≫ variant_wrap(`some))``.
    #[test]
    fn two_arms_building_one_tag_merge_into_one_arm() {
        let over = compare(CompareKind::Greater, 1);
        let negate = Expr::compose(vec![
            zip(vec![constant(0), id()]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Sub)),
            wrap("some"),
        ]);
        let chain = vec![joined(
            vec![
                filtered(over.clone(), wrap("some"), option_type()),
                filtered(negated(over), negate, option_type()),
            ],
            option_type(),
        )];
        let fused = fuse_options(&chain, &int()).expect("the gates split");
        let out = fused.program.eval(&ColumnValue::Ints(vec![0, 5, 1, 9]));
        let some = |n| Value::Union {
            tag: tag("some"),
            inner: Box::new(Value::Int(n)),
        };
        let got: Vec<Value> = (0..4).map(|i| out.index_at(i)).collect();
        assert_eq!(
            got,
            [some(0), some(5), some(-1), some(9)],
            "{}",
            fused.program
        );
    }

    /// A prefix whose output does not read a conditional that builds a union is not taken, since it
    /// would hold an unread constructor: after ``𝑗𝑜𝑖𝑛 ≫ 5 ▷ const ≫ (id, 1 ▷ const) ▷ zip ≫ add``,
    /// only the join is fused.
    #[test]
    fn a_prefix_does_not_leave_a_built_conditional_unread() {
        let over = compare(CompareKind::Greater, 1);
        let chain = vec![
            joined(
                vec![
                    filtered(over.clone(), wrap("some"), option_type()),
                    filtered(negated(over), none(), option_type()),
                ],
                option_type(),
            ),
            constant(5),
            arith(ArithmeticKind::Add, 1),
        ];
        let fused = fuse_options(&chain, &int()).expect("the join fuses");
        assert_eq!(fused.consumed, 1, "{}", fused.program);
    }

    /// A conditional that builds a union inside an arm of another merges both levels, rows in
    /// order across blocks: ``(x > 2000 ▷ filter_values ≫ variant_wrap(`some)) ⊔ (x > 2000 ≫
    /// not_fn ▷ filter_values ≫ ((x > 1000 ▷ filter_values ≫ x * 2 ≫ variant_wrap(`some)) ⊔ (x >
    /// 1000 ≫ not_fn ▷ filter_values ≫ `none(unit) ▷ const)))`` over 2,500 rows.
    #[test]
    fn a_built_union_inside_an_arm_merges_across_levels() {
        let (over_2000, over_1000) = (
            compare(CompareKind::Greater, 2000),
            compare(CompareKind::Greater, 1000),
        );
        let inner = joined(
            vec![
                filtered(
                    over_1000.clone(),
                    Expr::compose(vec![arith(ArithmeticKind::Mul, 2), wrap("some")]),
                    option_type(),
                ),
                filtered(negated(over_1000), none(), option_type()),
            ],
            option_type(),
        );
        let chain = vec![joined(
            vec![
                filtered(over_2000.clone(), wrap("some"), option_type()),
                filtered(negated(over_2000), inner, option_type()),
            ],
            option_type(),
        )];
        let fused = fuse_options(&chain, &int()).expect("both conditionals split the rows");
        let n = 2_500;
        let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
        let want = |x: i64| match x {
            x if x > 2000 => Value::Union {
                tag: tag("some"),
                inner: Box::new(Value::Int(x)),
            },
            x if x > 1000 => Value::Union {
                tag: tag("some"),
                inner: Box::new(Value::Int(x * 2)),
            },
            _ => Value::Union {
                tag: tag("none"),
                inner: Box::new(Value::Unit),
            },
        };
        let got: Vec<Value> = (0..n as usize).map(|i| out.index_at(i)).collect();
        assert_eq!(
            got,
            (0..n).map(want).collect::<Vec<_>>(),
            "{}",
            fused.program
        );
        let empty = fused.program.eval(&ColumnValue::Ints(Vec::new()));
        assert_eq!(empty.len(), 0, "an empty input");
        assert!(matches!(empty, ColumnValue::Union(_)), "{empty:?}");
    }

    /// A `match` over no rows yields an empty column of its result's type, and a conditional of
    /// `String`s merges through a scatter: ``(variant_project(`some) ≫ id * 2) ⊔
    /// (variant_project(`none) ≫ 7 ▷ const)`` over no rows, and ``(x > 1 ▷ filter_values ≫ "big"
    /// ▷ const) ⊔ (x > 1 ≫ not_fn ▷ filter_values ≫ "small" ▷ const)``.
    #[test]
    fn a_match_over_no_rows_and_a_conditional_of_strings() {
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
        let empty = ColumnValue::from_values(Vec::new(), &option_extent());
        assert_eq!(fused.program.eval(&empty), ColumnValue::Ints(Vec::new()));

        let string_ty = || Type::Base(BaseType::String);
        let word = |w: &str| {
            Expr::apply(
                Expr::lit(Lit::String(w.into())),
                Expr::builtin(Builtin::Const),
            )
            .with_ty(Type::fun(int_ty(), string_ty()))
        };
        let over = compare(CompareKind::Greater, 1);
        let chain = vec![joined(
            vec![
                filtered(over.clone(), word("big"), string_ty()),
                filtered(negated(over), word("small"), string_ty()),
            ],
            string_ty(),
        )];
        let types = [(string_ty(), Extent::Base(BaseType::String))];
        let fused = fuse_typed(&chain, &int(), &types).expect("the gates split");
        let out = fused.program.eval(&ColumnValue::Ints(vec![0, 5, 1]));
        let words = ["small", "big", "small"].map(SmolStr::from).to_vec();
        assert_eq!(out, ColumnValue::Strings(words));
    }
}
