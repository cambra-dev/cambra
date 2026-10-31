//! Link-time constants (`docs/chl-spec.md`, "9.19 Constants").
//!
//! A `const` parameter is a [`ConstParam`], and the value a run passes it is a
//! [`ConstTerm`] over the `const` parameters of the module that writes the `run`. Linking
//! substitutes each of those in turn, from the root down, so every term a program holds
//! once linked is a value. A nominal type that reaches a `const` parameter records the term
//! among its implicit arguments, and two instances are one type when their terms are equal
//! (`docs/chl-spec.md`, "Nominal type identity").
//!
//! A term is kept in normal form: an operation whose operands are all values is replaced by
//! the value it computes. What is left is an operation over a parameter, which a module
//! checked alone compares as written, so `r` and `r + 0` are two arguments.

use std::collections::HashMap;
use std::fmt;

use smol_str::SmolStr;

use crate::ccl::{
    ArithmeticKind, BinOpKind, CompareKind, Label, Lit, LogicKind, TypeParam, TypeParamId,
};

/// A `const` value parameter of a module (`docs/chl-spec.md`, "9.4 Parameters").
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstParam {
    /// Tells apart the parameters of two modules that share a spelling. Drawn from the
    /// [`TypeParam`] counter, so it is distinct from every type parameter's id too.
    pub id: TypeParamId,
    /// The parameter's name, for display.
    pub spelling: SmolStr,
}

impl ConstParam {
    /// A new parameter spelled `spelling`, equal to no other.
    pub fn declared(spelling: impl Into<SmolStr>) -> ConstParam {
        let spelling = spelling.into();
        ConstParam {
            id: TypeParam::declared(spelling.clone()).id,
            spelling,
        }
    }
}

/// A constant, as a term over `const` parameters, in normal form.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstTerm {
    Lit(Lit),
    Param(ConstParam),
    Tuple(Vec<ConstTerm>),
    /// A record, its fields in label order.
    Record(Vec<(Label, ConstTerm)>),
    List(Vec<ConstTerm>),
    BinOp(BinOpKind, Box<ConstTerm>, Box<ConstTerm>),
    Neg(Box<ConstTerm>),
    Not(Box<ConstTerm>),
    /// `then if cond else otherwise`, as `If(cond, then, otherwise)`.
    If(Box<ConstTerm>, Box<ConstTerm>, Box<ConstTerm>),
    /// A record's field, `r.f`.
    Field(Box<ConstTerm>, Label),
    /// A tuple's or a list's element, `xs[i]`.
    Element(Box<ConstTerm>, Box<ConstTerm>),
}

/// A function that may be called in a constant (`docs/chl-spec.md`, "9.19 Constants"): its
/// body, as a term over its parameters and the `const` parameters of its module. A call is the
/// body with each parameter replaced by its argument's term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstFunction {
    pub params: Vec<ConstParam>,
    pub body: ConstTerm,
}

impl ConstFunction {
    /// The term a call with `args`, one per parameter, computes.
    pub fn applied(&self, args: Vec<ConstTerm>) -> Result<ConstTerm, NoValue> {
        debug_assert_eq!(
            args.len(),
            self.params.len(),
            "a call passes each parameter"
        );
        let values = self.params.iter().map(|p| p.id).zip(args).collect();
        self.body.substituted(&values)
    }

    /// The function with each `const` parameter of its module that `values` maps replaced
    /// by its term, as [`ConstTerm::substituted`] does.
    pub fn substituted(
        &self,
        values: &HashMap<TypeParamId, ConstTerm>,
    ) -> Result<ConstFunction, NoValue> {
        Ok(ConstFunction {
            params: self.params.clone(),
            body: self.body.substituted(values)?,
        })
    }
}

/// Why a constant has no value: an operation the runtime gives no result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoValue(pub String);

impl ConstTerm {
    /// Whether the term is a value: it reads no parameter.
    pub fn is_value(&self) -> bool {
        match self {
            ConstTerm::Lit(_) => true,
            ConstTerm::Tuple(items) | ConstTerm::List(items) => items.iter().all(Self::is_value),
            ConstTerm::Record(fields) => fields.iter().all(|(_, t)| t.is_value()),
            _ => false,
        }
    }

    /// The parameters the term reads, each once, in the order it reads them.
    pub fn params(&self) -> Vec<&ConstParam> {
        fn go<'a>(term: &'a ConstTerm, out: &mut Vec<&'a ConstParam>) {
            match term {
                ConstTerm::Lit(_) => {}
                ConstTerm::Param(p) => {
                    if !out.contains(&p) {
                        out.push(p);
                    }
                }
                ConstTerm::Tuple(items) | ConstTerm::List(items) => {
                    items.iter().for_each(|t| go(t, out));
                }
                ConstTerm::Record(fields) => fields.iter().for_each(|(_, t)| go(t, out)),
                ConstTerm::BinOp(_, l, r) | ConstTerm::Element(l, r) => {
                    go(l, out);
                    go(r, out);
                }
                ConstTerm::Neg(t) | ConstTerm::Not(t) | ConstTerm::Field(t, _) => go(t, out),
                ConstTerm::If(c, t, e) => {
                    go(c, out);
                    go(t, out);
                    go(e, out);
                }
            }
        }
        let mut out = Vec::new();
        go(self, &mut out);
        out
    }

    /// The term with each parameter `values` maps replaced by its term, in normal form. As
    /// the runtime does, a decided condition leaves the other arm unread, and so does an
    /// operand of `and` or `or` that decides the answer.
    pub fn substituted(&self, values: &HashMap<TypeParamId, ConstTerm>) -> Result<Self, NoValue> {
        let sub = |t: &ConstTerm| t.substituted(values);
        let boxed = |t: &ConstTerm| sub(t).map(Box::new);
        let term = match self {
            ConstTerm::If(c, t, e) => match sub(c)? {
                ConstTerm::Lit(Lit::Bool(true)) => return sub(t),
                ConstTerm::Lit(Lit::Bool(false)) => return sub(e),
                c => ConstTerm::If(Box::new(c), boxed(t)?, boxed(e)?),
            },
            ConstTerm::BinOp(
                op @ BinOpKind::BoolLogic(kind @ (LogicKind::And | LogicKind::Or)),
                l,
                r,
            ) => {
                let l = sub(l)?;
                if l == ConstTerm::Lit(Lit::Bool(*kind == LogicKind::Or)) {
                    return Ok(l);
                }
                ConstTerm::BinOp(*op, Box::new(l), boxed(r)?)
            }
            ConstTerm::Lit(_) => return Ok(self.clone()),
            ConstTerm::Param(p) => match values.get(&p.id) {
                Some(term) => return Ok(term.clone()),
                None => return Ok(self.clone()),
            },
            ConstTerm::Tuple(items) => {
                ConstTerm::Tuple(items.iter().map(sub).collect::<Result<_, _>>()?)
            }
            ConstTerm::List(items) => {
                ConstTerm::List(items.iter().map(sub).collect::<Result<_, _>>()?)
            }
            ConstTerm::Record(fields) => ConstTerm::Record(
                fields
                    .iter()
                    .map(|(l, t)| Ok((l.clone(), sub(t)?)))
                    .collect::<Result<_, _>>()?,
            ),
            ConstTerm::BinOp(op, l, r) => ConstTerm::BinOp(*op, boxed(l)?, boxed(r)?),
            ConstTerm::Neg(t) => ConstTerm::Neg(boxed(t)?),
            ConstTerm::Not(t) => ConstTerm::Not(boxed(t)?),
            ConstTerm::Field(t, f) => ConstTerm::Field(boxed(t)?, f.clone()),
            ConstTerm::Element(t, i) => ConstTerm::Element(boxed(t)?, boxed(i)?),
        };
        term.normalized()
    }

    /// The term with each operation over values replaced by the value it computes. The
    /// operands are already in normal form.
    ///
    /// # Errors
    ///
    /// An operation over values that has no result: an integer overflow, a division by
    /// zero, a missing field, or an index past the end.
    pub fn normalized(self) -> Result<Self, NoValue> {
        match self {
            ConstTerm::BinOp(op, l, r) => match (&*l, &*r) {
                (ConstTerm::Lit(a), ConstTerm::Lit(b)) => binop(op, a, b).map(ConstTerm::Lit),
                (a, b) if a.is_value() && b.is_value() && is_equality(op) => {
                    let equal = a == b;
                    let answer = matches!(op, BinOpKind::Compare(CompareKind::Equals)) == equal;
                    Ok(ConstTerm::Lit(Lit::Bool(answer)))
                }
                _ => Ok(ConstTerm::BinOp(op, l, r)),
            },
            ConstTerm::Neg(t) => match *t {
                ConstTerm::Lit(Lit::Int(n)) => n
                    .checked_neg()
                    .map(|n| ConstTerm::Lit(Lit::Int(n)))
                    .ok_or_else(|| NoValue(format!("`-{n}` overflows an `Int`"))),
                t => Ok(ConstTerm::Neg(Box::new(t))),
            },
            ConstTerm::Not(t) => match *t {
                ConstTerm::Lit(Lit::Bool(b)) => Ok(ConstTerm::Lit(Lit::Bool(!b))),
                t => Ok(ConstTerm::Not(Box::new(t))),
            },
            ConstTerm::If(c, t, e) => match *c {
                ConstTerm::Lit(Lit::Bool(true)) => Ok(*t),
                ConstTerm::Lit(Lit::Bool(false)) => Ok(*e),
                c => Ok(ConstTerm::If(Box::new(c), t, e)),
            },
            ConstTerm::Field(t, f) => match *t {
                ConstTerm::Record(fields) => fields
                    .into_iter()
                    .find(|(l, _)| *l == f)
                    .map(|(_, t)| t)
                    .ok_or_else(|| NoValue(format!("the record has no field `{}`", f.name()))),
                t => Ok(ConstTerm::Field(Box::new(t), f)),
            },
            ConstTerm::Element(t, i) => match (*t, *i) {
                (ConstTerm::Tuple(items) | ConstTerm::List(items), ConstTerm::Lit(Lit::Int(i))) => {
                    let len = items.len();
                    usize::try_from(i)
                        .ok()
                        .and_then(|i| items.into_iter().nth(i))
                        .ok_or_else(|| {
                            NoValue(format!("index {i} is past the end of {len} elements"))
                        })
                }
                (t, i) => Ok(ConstTerm::Element(Box::new(t), Box::new(i))),
            },
            term => Ok(term),
        }
    }
}

/// Whether `op` is `==` or `!=`, which compare compound values too.
fn is_equality(op: BinOpKind) -> bool {
    matches!(
        op,
        BinOpKind::Compare(CompareKind::Equals | CompareKind::NotEquals)
    )
}

/// `a op b` as the runtime's operator computes it, or `None` when it has no result.
/// `+` lowers to `Arithmetic(Add)` for every operand type, and the runtime picks the
/// operation by the operands: on strings it concatenates.
pub fn fold_binop(op: BinOpKind, a: &Lit, b: &Lit) -> Option<Lit> {
    let op = match (op, a, b) {
        (BinOpKind::Arithmetic(ArithmeticKind::Add), Lit::String(_), Lit::String(_)) => {
            BinOpKind::Concat
        }
        _ => op,
    };
    crate::ccl::planning::eval_binop(op, a, b)
}

/// `a op b` ([`fold_binop`]), or the reason it has no result.
fn binop(op: BinOpKind, a: &Lit, b: &Lit) -> Result<Lit, NoValue> {
    fold_binop(op, a, b).ok_or_else(|| {
        NoValue(format!(
            "`{} {} {}` has no value",
            ConstTerm::Lit(a.clone()),
            symbol(op),
            ConstTerm::Lit(b.clone())
        ))
    })
}

/// How CHL spells `op`.
fn symbol(op: BinOpKind) -> &'static str {
    match op {
        BinOpKind::Arithmetic(ArithmeticKind::Add) | BinOpKind::Concat => "+",
        BinOpKind::Arithmetic(ArithmeticKind::AddRefined) => "^+",
        BinOpKind::Arithmetic(ArithmeticKind::Sub) => "-",
        BinOpKind::Arithmetic(ArithmeticKind::Mul) => "*",
        BinOpKind::Arithmetic(ArithmeticKind::FloorDiv) => "//",
        BinOpKind::Arithmetic(ArithmeticKind::Pow) => "**",
        BinOpKind::Compare(CompareKind::Equals) => "==",
        BinOpKind::Compare(CompareKind::NotEquals) => "!=",
        BinOpKind::Compare(CompareKind::Less) => "<",
        BinOpKind::Compare(CompareKind::LessOrEq) => "<=",
        BinOpKind::Compare(CompareKind::Greater) => ">",
        BinOpKind::Compare(CompareKind::GreaterOrEq) => ">=",
        BinOpKind::BoolLogic(LogicKind::And) => "and",
        BinOpKind::BoolLogic(LogicKind::Or) => "or",
        BinOpKind::BoolLogic(LogicKind::Xor) => "^",
        BinOpKind::BoolLogic(LogicKind::Nand) => "nand",
        BinOpKind::BoolLogic(LogicKind::Nor) => "nor",
        BinOpKind::BoolLogic(LogicKind::Xnor) => "xnor",
    }
}

/// As CHL writes the term: `30`, `"us"`, `(a=1, b=2)`, `r + 1`.
impl fmt::Display for ConstTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |f: &mut fmt::Formatter<'_>, items: &[ConstTerm]| -> fmt::Result {
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{item}")?;
            }
            Ok(())
        };
        match self {
            ConstTerm::Lit(Lit::Int(n)) => write!(f, "{n}"),
            ConstTerm::Lit(Lit::String(s)) => write!(f, "{s:?}"),
            ConstTerm::Lit(Lit::Bool(true)) => write!(f, "True"),
            ConstTerm::Lit(Lit::Bool(false)) => write!(f, "False"),
            ConstTerm::Lit(Lit::Unit) => write!(f, "()"),
            ConstTerm::Param(p) => write!(f, "{}", p.spelling),
            ConstTerm::Tuple(items) => {
                write!(f, "(")?;
                list(f, items)?;
                if items.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            ConstTerm::List(items) => {
                write!(f, "[")?;
                list(f, items)?;
                write!(f, "]")
            }
            ConstTerm::Record(fields) => {
                write!(f, "(")?;
                for (i, (label, term)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}={term}", label.name())?;
                }
                write!(f, ")")
            }
            ConstTerm::BinOp(op, l, r) => write!(f, "({l} {} {r})", symbol(*op)),
            ConstTerm::Neg(t) => write!(f, "-{t}"),
            ConstTerm::Not(t) => write!(f, "not {t}"),
            ConstTerm::If(c, t, e) => write!(f, "({t} if {c} else {e})"),
            ConstTerm::Field(t, l) => write!(f, "{t}.{}", l.name()),
            ConstTerm::Element(t, i) => write!(f, "{t}[{i}]"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(n: i64) -> ConstTerm {
        ConstTerm::Lit(Lit::Int(n))
    }

    fn op(kind: ArithmeticKind, l: ConstTerm, r: ConstTerm) -> ConstTerm {
        ConstTerm::BinOp(BinOpKind::Arithmetic(kind), Box::new(l), Box::new(r))
    }

    /// An operation over values is the value it computes, and one over a parameter stays as
    /// written until the parameter has a value.
    #[test]
    fn a_term_reduces_once_its_parameters_have_values() {
        assert_eq!(
            op(ArithmeticKind::Add, int(2), int(3)).normalized(),
            Ok(int(5))
        );
        let r = ConstParam::declared("r");
        let over_r = op(ArithmeticKind::Add, ConstTerm::Param(r.clone()), int(1))
            .normalized()
            .unwrap();
        assert!(!over_r.is_value());
        assert_eq!(over_r.to_string(), "(r + 1)");
        let values = HashMap::from([(r.id, int(4))]);
        assert_eq!(over_r.substituted(&values), Ok(int(5)));
    }

    /// `r` and `r + 0` are two terms, which a module checked alone compares as written.
    #[test]
    fn a_term_over_a_parameter_compares_as_written() {
        let r = ConstTerm::Param(ConstParam::declared("r"));
        let plus_zero = op(ArithmeticKind::Add, r.clone(), int(0))
            .normalized()
            .unwrap();
        assert_ne!(r, plus_zero);
    }

    /// An operation the runtime gives no result has no value.
    #[test]
    fn a_division_by_zero_has_no_value() {
        let error = op(ArithmeticKind::FloorDiv, int(1), int(0))
            .normalized()
            .unwrap_err();
        assert_eq!(error.0, "`1 // 0` has no value");
    }

    /// A condition decided once its parameter has a value leaves the other arm unread, and
    /// so does an operand of `and` or `or` that decides the answer, as the runtime's
    /// ternary and boolean operators do.
    #[test]
    fn a_decided_operand_leaves_the_rest_unread() {
        let d = ConstParam::declared("d");
        let param = || ConstTerm::Param(d.clone());
        let nonzero = || {
            ConstTerm::BinOp(
                BinOpKind::Compare(CompareKind::NotEquals),
                Box::new(param()),
                Box::new(int(0)),
            )
        };
        let quotient = || op(ArithmeticKind::FloorDiv, int(10), param());
        let ternary = ConstTerm::If(Box::new(nonzero()), Box::new(quotient()), Box::new(int(0)));
        let both = ConstTerm::BinOp(
            BinOpKind::BoolLogic(LogicKind::And),
            Box::new(nonzero()),
            Box::new(ConstTerm::BinOp(
                BinOpKind::Compare(CompareKind::Greater),
                Box::new(quotient()),
                Box::new(int(1)),
            )),
        );
        let zero = HashMap::from([(d.id, int(0))]);
        assert_eq!(ternary.substituted(&zero), Ok(int(0)));
        assert_eq!(
            both.substituted(&zero),
            Ok(ConstTerm::Lit(Lit::Bool(false)))
        );
        let five = HashMap::from([(d.id, int(5))]);
        assert_eq!(ternary.substituted(&five), Ok(int(2)));
        assert_eq!(both.substituted(&five), Ok(ConstTerm::Lit(Lit::Bool(true))));
    }

    /// `+` on two strings concatenates them, as the runtime's operator does.
    #[test]
    fn adding_strings_concatenates() {
        let s = |v: &str| ConstTerm::Lit(Lit::String(v.into()));
        assert_eq!(
            op(ArithmeticKind::Add, s("a"), s("b")).normalized(),
            Ok(s("ab"))
        );
    }
}
