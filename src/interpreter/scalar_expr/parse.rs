//! Recognize an element-wise chain as a [`ScalarProgram`]: [`fuse_prefix`].

mod join;
mod short_circuit;

use std::collections::HashMap;

use smol_str::SmolStr;

use super::{Fused, Instr, ScalarProgram, Slot, has_view, value_extent};
use crate::ccl::{Builtin, Expr, FieldKey, ProjKey, Type, TypedExprNode};
use crate::interpreter::binop::compared_fields;
use crate::interpreter::operator_conversion::expr_to_value;
use crate::interpreter::{
    BaseType, BinOpKind as InterpreterBinOp, CompareKind, Extent, LogicKind, UnaryOpKind, Value,
    binop_output_extent, tuple_field,
};

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
    /// A `Case` that constructs, with its extent. Only [`Parser::output`] reads it.
    Built(Slot, Extent),
}

/// The value of an `==` or `!=` comparison as [`Parser::comparison`] reads it.
enum Comparison {
    /// A column of `Bool`s in this slot.
    Computed(Slot),
    /// The same answer at every row, known while parsing.
    Decided(bool),
}

struct Parser<'t> {
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
    /// How many `Tag` arms the parse opened, which numbers their payload placeholders.
    placeholders: usize,
}

impl Parser<'_> {
    /// The slot of `instr`: an equal instruction's slot when one was emitted, or a new one. An
    /// instruction's value is a function of its fields and of the slots it reads, so equal
    /// instructions compute equal columns. Constructors are always new, since a later constructor
    /// or `Case` reads each where it is built
    /// ([`ScalarProgram::constructors_build_only_the_result`]).
    fn emit(&mut self, instr: Instr) -> Slot {
        if let Some(&slot) = self.slots.get(&instr) {
            return slot;
        }
        let slot = self.instrs.len() as Slot;
        if !instr.is_constructor() {
            self.slots.insert(instr.clone(), slot);
        }
        self.instrs.push(instr);
        slot
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
        match v {
            Val::Slot(slot, extent) => Some((*slot, extent.clone())),
            Val::Read(path, extent) if has_view(extent) => Some((self.input(path), extent.clone())),
            Val::Const(value, extent) if has_view(extent) => {
                Some((self.emit(Instr::Const(value.clone())), extent.clone()))
            }
            Val::Read(..)
            | Val::Const(..)
            | Val::Tuple(_)
            | Val::Record(_)
            | Val::Wrap(..)
            | Val::Built(..) => None,
        }
    }

    /// The `Input` instruction reading `path`.
    fn input(&mut self, path: &[SmolStr]) -> Slot {
        self.emit(Instr::Input {
            path: path.to_vec(),
        })
    }

    /// An input or constant with no view as a slot: a `Unit` one, or a union read from the input.
    /// Only a constructor reads the slot, copying its rows.
    fn copied(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        match v {
            Val::Read(path, extent @ (Extent::Base(BaseType::Unit) | Extent::Union(_))) => {
                Some((self.input(path), extent.clone()))
            }
            Val::Const(value @ Value::Unit, extent) => {
                Some((self.emit(Instr::Const(value.clone())), extent.clone()))
            }
            _ => None,
        }
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
            return Some((self.emit(Instr::Bin(op, a, b)), binop_output_extent(&op)));
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
                Val::Read(_, Extent::Base(BaseType::Unit)) | Val::Const(Value::Unit, _)
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
                return Some(Comparison::Computed(self.emit(Instr::Bin(op, a, b))));
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
                        Some(prev) => self.emit(Instr::Bin(join, prev, slot)),
                    });
                }
            }
        }
        Some(joined.map_or(Comparison::Decided(equals), Comparison::Computed))
    }

    /// Extend an input field path. Projections of computed products are not recognized here;
    /// any such projection left after simplification ends the prefix.
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
                Some(Val::Slot(self.emit(Instr::Un(op, a)), extent))
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
            Val::Slot(..) => None,
            Val::Built(slot, extent) if *slot as usize + 1 == self.instrs.len() => {
                Some((*slot, extent.clone()))
            }
            Val::Built(..) => None,
            Val::Tuple(_) | Val::Record(_) | Val::Wrap(..) => self.output(v),
            Val::Read(..) | Val::Const(..) => None,
        }
    }

    /// `v` as a column of the result, with its extent. A variant is a `Wrap` of its payload's
    /// column, and a record ([`Parser::fields_of`]) is a `Record` of its fields' columns. Anything
    /// else is its own column: a computed one, a base value or `Unit` read from the input or held
    /// as a constant, or a union read from the input. A product with no field has no column, since
    /// nothing in it counts its rows.
    fn output(&mut self, v: &Val) -> Option<(Slot, Extent)> {
        if let Val::Built(slot, extent) = v {
            return Some((*slot, extent.clone()));
        }
        if let Val::Wrap(tag, payload, extent) = v {
            let (payload, _) = self.output(payload)?;
            let tag = tag.clone();
            return Some((self.emit(Instr::Wrap { tag, payload }), extent.clone()));
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
        Some((self.emit(Instr::Record(named)), Extent::Record(extents)))
    }
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
/// An eligible prefix ends at an operation, a product or a variant and meets [`Parser::ops`]'s
/// minimum count of two. See `src/ccl/design/optimization.md`, "Element-wise chains", for supported
/// forms and conversion boundaries.
pub fn fuse_prefix(
    chain: &[Expr],
    input: &Extent,
    extent_of: &dyn Fn(&Type) -> Option<Extent>,
) -> Option<Fused> {
    if !is_plain(input) {
        return None;
    }
    let mut parser = Parser {
        extent_of,
        instrs: Vec::new(),
        slots: HashMap::new(),
        ops: 0,
        placeholders: 0,
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
            // A `Case` that constructs is emitted while its element is read, not while the output
            // is probed, so a prefix whose output does not read it would hold an unread
            // constructor.
            if parser.root_of(&cur).is_some() {
                let probed = ScalarProgram {
                    instrs: std::mem::take(&mut parser.instrs),
                };
                if probed.constructors_build_only_the_result() {
                    best = Some((k + 1, len, cur.clone()));
                }
                parser.instrs = probed.instrs;
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
    let program = short_circuit::short_circuit(ScalarProgram {
        instrs: parser.instrs,
    });
    debug_assert!(
        program.constructors_build_only_the_result(),
        "a constructor is the last instruction or a field or payload of a later one, and no \
         operation reads one; got {program}"
    );
    debug_assert!(
        program.operands_have_views(input),
        "an operation reads only a column with a view, over {input}; got {program}"
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
    use crate::ccl::{ArithmeticKind, BinOpKind};

    use crate::interpreter::scalar_expr::tests::*;

    /// A program's result is its last instruction, so a computed value that shares an earlier
    /// slot is no result.
    #[test]
    fn a_computed_value_in_an_earlier_slot_is_no_result() {
        let no_types = |ty: &Type| panic!("no type is read, read {ty}");
        let mut parser = Parser {
            extent_of: &no_types,
            instrs: Vec::new(),
            slots: HashMap::new(),
            ops: 0,
            placeholders: 0,
        };
        let x = parser.emit(Instr::Input { path: Vec::new() });
        let one = parser.emit(Instr::Const(Value::Int(1)));
        let add = InterpreterBinOp::from(BinOpKind::Arithmetic(ArithmeticKind::Add));
        let sum = parser.emit(Instr::Bin(add, x, one));
        assert!(parser.root_of(&Val::Slot(sum, int())).is_some());
        assert_eq!(
            parser.emit(Instr::Bin(add, x, one)),
            sum,
            "an equal operation shares"
        );
        let negated = parser.emit(Instr::Un(UnaryOpKind::Neg, sum));
        assert!(parser.root_of(&Val::Slot(sum, int())).is_none());
        assert!(parser.root_of(&Val::Slot(negated, int())).is_some());
    }
}
