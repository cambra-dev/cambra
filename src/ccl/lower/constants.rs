//! A module's link-time constants as it lowers (`docs/chl-spec.md`, "9.19 Constants").
//!
//! [`ModuleConstants::of`] records the module's top-level bindings and its `const`
//! parameters before anything lowers, and [`LoweringContext::const_term`] reads a constant
//! expression as a [`ConstTerm`] over the module's `const` parameters. The term is built
//! from the syntax: a constant reads only literals, `const` bindings and `const` parameters,
//! so no lowering is needed to know its value, and the term is ready wherever a constant is
//! required, before the statements above it have lowered. A call, a comprehension, and any
//! other form are refused.

use std::collections::HashMap;

use smol_str::SmolStr;

use super::{LoweringContext, LoweringError};
use crate::ccl::constant::{ConstParam, ConstTerm};
use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Lit, LogicKind};
use crate::chl_parser::ast::{
    AssignTarget, BinOp as ChlBinOp, BoolOp, CmpOp, Expr as ChlExpr, Lit as ChlLit,
    QualifiedName as ParserQualifiedName, Span, Spanned, Stmt as ChlStmt, UnaryOp,
};

/// The top-level bindings and `const` parameters of the module being lowered.
#[derive(Debug, Default)]
pub(in crate::ccl) struct ModuleConstants {
    /// Each top-level binding of a value, by name, in source order.
    bindings: HashMap<SmolStr, Vec<TopBinding>>,
    /// The term of each `const` binding read so far, by name and the start of its
    /// statement, or `None` when it is in error, which was reported once.
    terms: HashMap<(SmolStr, usize), Option<ConstTerm>>,
}

/// One top-level binding of a name.
#[derive(Debug, Clone)]
struct TopBinding {
    /// Where its statement starts.
    start: usize,
    kind: BindingKind,
}

#[derive(Debug, Clone)]
enum BindingKind {
    /// `const x = e`, or the element at `path` of the tuple `e` is, for a destructuring
    /// target.
    Const {
        definition: Spanned<ChlExpr>,
        path: Vec<usize>,
    },
    /// `const param x`.
    ConstParam(ConstParam),
    /// A value parameter without `const`.
    Param,
    /// A mutable variable.
    Mutable,
    Function,
    /// Any other binding: `x = e`.
    Plain,
}

impl ModuleConstants {
    /// The bindings `stmts`, a module's top level, write, with a [`ConstParam`] minted for
    /// each `const param`.
    pub(super) fn of(stmts: &[Spanned<ChlStmt>]) -> ModuleConstants {
        let mut out = ModuleConstants::default();
        for stmt in stmts {
            let start = stmt.span.start;
            let stmt = match &stmt.node {
                ChlStmt::Pub { stmt, .. } => &stmt.node,
                other => other,
            };
            let mut push = |name: &SmolStr, kind: BindingKind| {
                out.bindings
                    .entry(name.clone())
                    .or_default()
                    .push(TopBinding { start, kind });
            };
            match stmt {
                ChlStmt::Assign {
                    target,
                    value,
                    constant,
                    ..
                }
                | ChlStmt::AnnAssign {
                    target,
                    value,
                    constant,
                    ..
                } => each_name(&target.node, &mut Vec::new(), &mut |name, path| {
                    let kind = match constant {
                        Some(_) => BindingKind::Const {
                            definition: value.clone(),
                            path,
                        },
                        None => BindingKind::Plain,
                    };
                    push(name, kind);
                }),
                ChlStmt::MutAssign { target, .. } | ChlStmt::LoadFrom { target, .. } => {
                    each_name(&target.node, &mut Vec::new(), &mut |name, _| {
                        push(name, BindingKind::Mutable);
                    });
                }
                ChlStmt::FunctionDef {
                    owner: None, name, ..
                } => push(&name.node, BindingKind::Function),
                ChlStmt::Param { name, constant, .. } => {
                    let kind = match constant {
                        Some(_) => BindingKind::ConstParam(ConstParam::declared(name.node.clone())),
                        None => BindingKind::Param,
                    };
                    push(&name.node, kind);
                }
                _ => {}
            }
        }
        out
    }

    /// The `const` parameter `name` names, if it names one.
    pub(super) fn param(&self, name: &str) -> Option<&ConstParam> {
        self.bindings
            .get(name)?
            .iter()
            .find_map(|binding| match &binding.kind {
                BindingKind::ConstParam(param) => Some(param),
                _ => None,
            })
    }

    /// Whether `name` is bound at the top level only by `const` bindings, so a reference
    /// to it from anywhere in the module reads a constant.
    pub(super) fn is_constant(&self, name: &str) -> bool {
        self.bindings.get(name).is_some_and(|bindings| {
            bindings.iter().all(|b| {
                matches!(
                    b.kind,
                    BindingKind::Const { .. } | BindingKind::ConstParam(_)
                )
            })
        })
    }

    /// Each `const` binding, by name, with where its statement starts.
    pub(super) fn constant_bindings(&self) -> Vec<(SmolStr, usize)> {
        let mut out: Vec<(SmolStr, usize)> = self
            .bindings
            .iter()
            .flat_map(|(name, bindings)| {
                bindings
                    .iter()
                    .filter(|b| matches!(b.kind, BindingKind::Const { .. }))
                    .map(move |b| (name.clone(), b.start))
            })
            .collect();
        out.sort_by_key(|(_, start)| *start);
        out
    }

    /// The term of the last top-level binding of `name`, when it is a `const` binding whose
    /// term has been read.
    pub(super) fn term_of(&self, name: &str) -> Option<ConstTerm> {
        let last = self.bindings.get(name)?.iter().max_by_key(|b| b.start)?;
        matches!(last.kind, BindingKind::Const { .. })
            .then(|| {
                self.terms
                    .get(&(SmolStr::from(name), last.start))
                    .cloned()
                    .flatten()
            })
            .flatten()
    }

    /// The binding a reference to `name` from a statement starting at `at` reads: the last
    /// above it.
    fn above(&self, name: &str, at: usize) -> Option<&TopBinding> {
        self.bindings
            .get(name)?
            .iter()
            .filter(|b| b.start < at)
            .max_by_key(|b| b.start)
    }
}

/// Call `f` on each name `target` binds, with the tuple indices that lead to it.
fn each_name(
    target: &AssignTarget,
    path: &mut Vec<usize>,
    f: &mut dyn FnMut(&SmolStr, Vec<usize>),
) {
    match target {
        AssignTarget::Name(name) => f(name, path.clone()),
        AssignTarget::Tuple(items) => {
            for (i, item) in items.iter().enumerate() {
                path.push(i);
                each_name(&item.node, path, f);
                path.pop();
            }
        }
        // A subscript target binds no name of its own.
        _ => {}
    }
}

/// An error at `span` that `what` is no constant.
fn refused(span: Span, what: impl Into<String>) -> LoweringError {
    LoweringError::unsupported(span, what.into())
}

/// Why an expression has no term: its error, or `None` when it reads a `const` binding
/// whose own error was reported at the binding.
#[derive(Debug)]
pub(super) struct Refused(pub Option<LoweringError>);

impl From<LoweringError> for Refused {
    fn from(error: LoweringError) -> Self {
        Refused(Some(error))
    }
}

impl Refused {
    /// Record the error, if it has one of its own, in `errors`.
    pub(super) fn report(self, errors: &mut Vec<LoweringError>) {
        errors.extend(self.0);
    }
}

impl LoweringContext {
    /// Read the term of each `const` binding of the module, in source order: the error of
    /// each that is not a constant.
    pub(super) fn check_constants(&mut self) -> Vec<LoweringError> {
        let mut errors = Vec::new();
        for (name, start) in self.constants.constant_bindings() {
            self.const_binding_term(&name, start, &mut errors);
        }
        errors
    }

    /// The term of the `const` binding `name` whose statement starts at `start`, reading
    /// it once. `None` when it is in error, reported the first time it is read.
    pub(super) fn const_binding_term(
        &mut self,
        name: &SmolStr,
        start: usize,
        errors: &mut Vec<LoweringError>,
    ) -> Option<ConstTerm> {
        let key = (name.clone(), start);
        if let Some(term) = self.constants.terms.get(&key) {
            return term.clone();
        }
        let binding = self.constants.bindings[name]
            .iter()
            .find(|b| b.start == start)
            .cloned()
            .expect("a `const` binding is recorded");
        let BindingKind::Const { definition, path } = binding.kind else {
            unreachable!("asked for the term of a binding that is not `const`");
        };
        // A binding read while its own term is computed is read below itself, which its
        // scope already refuses; recording `None` first keeps the read from recurring.
        self.constants.terms.insert(key.clone(), None);
        let term = self.const_term(&definition, start).and_then(|term| {
            path.iter().try_fold(term, |term, &i| {
                let index = ConstTerm::Lit(Lit::Int(i64::try_from(i).expect("a tuple index fits")));
                ConstTerm::Element(Box::new(term), Box::new(index))
                    .normalized()
                    .map_err(|e| Refused::from(refused(definition.span, e.0)))
            })
        });
        let term = match term {
            Ok(term) => Some(term),
            Err(refusal) => {
                refusal.report(errors);
                None
            }
        };
        self.constants.terms.insert(key, term.clone());
        term
    }

    /// `expr`, a constant written in a statement that starts at `at`, as a term over the
    /// module's `const` parameters.
    ///
    /// # Errors
    ///
    /// A form a constant does not take, a name that is not a constant, or an operation
    /// over values that has no result.
    pub(super) fn const_term(
        &mut self,
        expr: &Spanned<ChlExpr>,
        at: usize,
    ) -> Result<ConstTerm, Refused> {
        let span = expr.span;
        let no_value = |e: crate::ccl::constant::NoValue| Refused::from(refused(span, e.0));
        match &expr.node {
            ChlExpr::Lit(lit) => Ok(ConstTerm::Lit(match lit {
                ChlLit::Int(n) => Lit::Int(*n),
                ChlLit::String(s) => Lit::String(s.clone()),
                ChlLit::Bool(b) => Lit::Bool(*b),
            })),
            ChlExpr::Name(name) => self.const_name(name, span, at),
            ChlExpr::Qualified(q) => self.const_member(q, span),
            ChlExpr::BinOp { left, op, right } => {
                let op = match op {
                    ChlBinOp::Add | ChlBinOp::AddRefined => {
                        BinOpKind::Arithmetic(ArithmeticKind::Add)
                    }
                    ChlBinOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
                    ChlBinOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
                    ChlBinOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
                    ChlBinOp::Pow => BinOpKind::Arithmetic(ArithmeticKind::Pow),
                    ChlBinOp::LogicalAnd => BinOpKind::BoolLogic(LogicKind::And),
                    ChlBinOp::LogicalOr => BinOpKind::BoolLogic(LogicKind::Or),
                    ChlBinOp::LogicalXor => BinOpKind::BoolLogic(LogicKind::Xor),
                    ChlBinOp::CollectionUnion => {
                        return Err(refused(span, "`++` in a constant is not supported yet").into());
                    }
                };
                let left = self.const_term(left, at)?;
                let right = self.const_term(right, at)?;
                ConstTerm::BinOp(op, Box::new(left), Box::new(right))
                    .normalized()
                    .map_err(no_value)
            }
            ChlExpr::UnaryOp { op, operand } => {
                let operand = Box::new(self.const_term(operand, at)?);
                match op {
                    UnaryOp::Neg => ConstTerm::Neg(operand),
                    UnaryOp::Not => ConstTerm::Not(operand),
                }
                .normalized()
                .map_err(no_value)
            }
            ChlExpr::BoolOp { op, operands } => {
                let kind = match op {
                    BoolOp::And => LogicKind::And,
                    BoolOp::Or => LogicKind::Or,
                };
                // As the runtime does, an operand that decides the answer leaves the rest
                // unread.
                let decides = Lit::Bool(matches!(op, BoolOp::Or));
                let mut acc: Option<ConstTerm> = None;
                for operand in operands {
                    if matches!(&acc, Some(ConstTerm::Lit(l)) if *l == decides) {
                        break;
                    }
                    let term = self.const_term(operand, at)?;
                    acc = Some(match acc {
                        None => term,
                        Some(acc) => ConstTerm::BinOp(
                            BinOpKind::BoolLogic(kind),
                            Box::new(acc),
                            Box::new(term),
                        )
                        .normalized()
                        .map_err(no_value)?,
                    });
                }
                Ok(acc.expect("a boolean operation has an operand"))
            }
            ChlExpr::Compare {
                left,
                ops,
                comparators,
            } => {
                // `a < b < c` is `a < b and b < c`, reading `b` once.
                let mut lhs = self.const_term(left, at)?;
                let mut acc: Option<ConstTerm> = None;
                for (op, rhs) in ops.iter().zip(comparators) {
                    let rhs = self.const_term(rhs, at)?;
                    let kind = BinOpKind::Compare(match op {
                        CmpOp::Eq => CompareKind::Equals,
                        CmpOp::NotEq => CompareKind::NotEquals,
                        CmpOp::Lt => CompareKind::Less,
                        CmpOp::LtE => CompareKind::LessOrEq,
                        CmpOp::Gt => CompareKind::Greater,
                        CmpOp::GtE => CompareKind::GreaterOrEq,
                    });
                    let step = ConstTerm::BinOp(kind, Box::new(lhs), Box::new(rhs.clone()))
                        .normalized()
                        .map_err(no_value)?;
                    acc = Some(match acc {
                        None => step,
                        Some(acc) => ConstTerm::BinOp(
                            BinOpKind::BoolLogic(LogicKind::And),
                            Box::new(acc),
                            Box::new(step),
                        )
                        .normalized()
                        .map_err(no_value)?,
                    });
                    lhs = rhs;
                }
                Ok(acc.expect("a comparison compares"))
            }
            ChlExpr::IfExp {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond = self.const_term(cond, at)?;
                // A decided condition leaves the other arm unread.
                match cond {
                    ConstTerm::Lit(Lit::Bool(true)) => self.const_term(then_expr, at),
                    ConstTerm::Lit(Lit::Bool(false)) => self.const_term(else_expr, at),
                    cond => {
                        let then_term = self.const_term(then_expr, at)?;
                        let else_term = self.const_term(else_expr, at)?;
                        Ok(ConstTerm::If(
                            Box::new(cond),
                            Box::new(then_term),
                            Box::new(else_term),
                        ))
                    }
                }
            }
            ChlExpr::Tuple(items) => Ok(ConstTerm::Tuple(
                items
                    .iter()
                    .map(|item| self.const_term(item, at))
                    .collect::<Result<_, _>>()?,
            )),
            ChlExpr::List(items) => Ok(ConstTerm::List(
                items
                    .iter()
                    .map(|item| self.const_term(item, at))
                    .collect::<Result<_, _>>()?,
            )),
            ChlExpr::Record(fields) => {
                let mut terms = Vec::new();
                for field in fields {
                    let label = self.label(&field.qualifier, &field.name, field.name_span)?;
                    terms.push((label, self.const_term(&field.value, at)?));
                }
                terms.sort_by(|(a, _), (b, _)| a.cmp(b));
                Ok(ConstTerm::Record(terms))
            }
            ChlExpr::Attribute {
                target,
                attr,
                attr_span,
                attr_qualifier,
            } => {
                let label = self.label(attr_qualifier, attr, *attr_span)?;
                let target = self.const_term(target, at)?;
                ConstTerm::Field(Box::new(target), label)
                    .normalized()
                    .map_err(no_value)
            }
            ChlExpr::Subscript {
                target,
                index,
                checked: false,
            } => {
                let target = self.const_term(target, at)?;
                let index = self.const_term(index, at)?;
                ConstTerm::Element(Box::new(target), Box::new(index))
                    .normalized()
                    .map_err(no_value)
            }
            ChlExpr::Call { .. } | ChlExpr::MethodCall { .. } => Err(refused(
                span,
                "a call in a constant is not supported yet; a constant is built from \
                 literals, `const` names, operators, and tuples, records and lists of them",
            )
            .into()),
            _ => Err(refused(
                span,
                "this is not a constant: a constant is built from literals, `const` names, \
                 operators, and tuples, records and lists of them",
            )
            .into()),
        }
    }

    /// The constant `name` reads from a statement starting at `at`.
    fn const_name(&mut self, name: &SmolStr, span: Span, at: usize) -> Result<ConstTerm, Refused> {
        if self.constants.above(name, at).is_none()
            && let Some(term) = self.used_const(name, span)
        {
            return term;
        }
        let Some(binding) = self.constants.above(name, at).cloned() else {
            return Err(refused(
                span,
                format!("`{name}` is not a constant: no `const` binding above names it"),
            )
            .into());
        };
        let not_const = |what: &str| {
            refused(
                span,
                format!(
                    "`{name}` is {what}, so it is not a constant: a constant names only \
                     `const` bindings and `const` parameters"
                ),
            )
        };
        match binding.kind {
            BindingKind::Const { .. } => {
                let mut errors = Vec::new();
                // The binding's own error is reported at the binding, by whichever read of
                // it comes first.
                self.const_binding_term(name, binding.start, &mut errors)
                    .ok_or(Refused(errors.pop()))
            }
            BindingKind::ConstParam(param) => Ok(ConstTerm::Param(param)),
            BindingKind::Param => Err(not_const("a parameter without `const`").into()),
            BindingKind::Mutable => Err(not_const("a mutable variable").into()),
            BindingKind::Function => Err(not_const("a function").into()),
            BindingKind::Plain => Err(refused(
                span,
                format!(
                    "`{name}` is not a constant: it is bound without `const`. Mark it \
                     `const {name} = …` if its value is fixed at link time"
                ),
            )
            .into()),
        }
    }

    /// The constant another module's member `q` is, `cfg::port`, as this module writes it.
    fn const_member(&mut self, q: &ParserQualifiedName, span: Span) -> Result<ConstTerm, Refused> {
        let [qualifier] = q.qualifier.as_slice() else {
            return Err(refused(
                span,
                "a constant reached through more than one qualifier is not supported yet",
            )
            .into());
        };
        self.qualified_const(&qualifier.node, &q.name.node, span)
    }

    /// The constant the `use` name `name` reads, if it is a `use` name of a value: another
    /// module's member, which is a constant if that module declares it `pub const`.
    pub(super) fn used_const(
        &mut self,
        name: &str,
        span: Span,
    ) -> Option<Result<ConstTerm, Refused>> {
        let used = self.module.uses.get(name)?;
        let super::modules::Reached::Value(reference) = &used.reached else {
            return None;
        };
        // A `use` name of a module with errors of its own reads nothing, as reported there.
        let Some(reference) = reference else {
            return Some(Err(Refused(None)));
        };
        let (qualifier, member) = reference.name.segments().split_first()?;
        let member = member
            .iter()
            .map(SmolStr::as_str)
            .collect::<Vec<_>>()
            .join("::");
        let qualifier = qualifier.clone();
        Some(self.qualified_const(&qualifier, &member, span))
    }

    /// The constant `qualifier::member` is, as this module writes it: a term over this
    /// module's `const` parameters, which the run or import `qualifier` names passes.
    pub(super) fn qualified_const(
        &mut self,
        qualifier: &str,
        member: &str,
        span: Span,
    ) -> Result<ConstTerm, Refused> {
        if member.contains("::") {
            return Err(refused(
                span,
                "a constant reached through more than one qualifier is not supported yet",
            )
            .into());
        }
        let Some(at) = self.module.qualifiers.get(qualifier) else {
            return Err(refused(span, format!("`{qualifier}` names no module")).into());
        };
        let Some(interface) = at.reachable() else {
            // The module's own errors account for the reference.
            return Err(Refused(None));
        };
        match interface.constants.get(member) {
            Some(term) => term
                .substituted(&at.types.consts)
                .map_err(|e| refused(span, e.0).into()),
            None => Err(refused(
                span,
                format!(
                    "`{qualifier}::{member}` is not a constant: module `{}` has no public \
                     `const` member `{member}`",
                    interface.module
                ),
            )
            .into()),
        }
    }
}
