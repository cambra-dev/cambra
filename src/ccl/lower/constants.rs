//! A module's link-time constants as it lowers (`docs/chl-spec.md`, "9.19 Constants").
//!
//! [`ModuleConstants::of`] records the module's top-level bindings and its `const`
//! parameters before anything lowers, and [`LoweringContext::const_term`] reads a constant
//! expression as a [`ConstTerm`] over the module's `const` parameters. The term is built
//! from the syntax: a constant reads only literals, constants and `const` parameters, so no
//! lowering is needed to know its value, and the term is ready wherever a constant is
//! required, before the statements above it have lowered. A call, a comprehension, and any
//! other form are refused.
//!
//! A top-level `=` binding is a constant when its definition is one, with no marker
//! ([`LoweringContext::settle_constants`]). Whether it is one is reported only where a
//! constant is required: a binding that is not one is an ordinary value elsewhere.

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
    /// What each `=` binding read so far is as a constant, by name and the start of its
    /// statement: its term, or why its definition is not one.
    terms: HashMap<(SmolStr, usize), Result<ConstTerm, Refused>>,
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
    /// `x = e`, a constant when `e` is one, or the element at `path` of the tuple `e` is,
    /// for a destructuring target.
    Value {
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
                ChlStmt::Assign { target, value, .. }
                | ChlStmt::AnnAssign { target, value, .. } => {
                    each_name(&target.node, &mut Vec::new(), &mut |name, path| {
                        let definition = value.clone();
                        push(name, BindingKind::Value { definition, path });
                    });
                }
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

    /// Each `=` binding, by name, with where its statement starts, in source order.
    fn value_bindings(&self) -> Vec<(SmolStr, usize)> {
        let mut out: Vec<(SmolStr, usize)> = self
            .bindings
            .iter()
            .flat_map(|(name, bindings)| {
                bindings
                    .iter()
                    .filter(|b| matches!(b.kind, BindingKind::Value { .. }))
                    .map(move |b| (name.clone(), b.start))
            })
            .collect();
        out.sort_by_key(|(_, start)| *start);
        out
    }

    /// What the last top-level binding of `name` is as a constant, when it is an `=` binding:
    /// its term, or why its definition is not one. [`LoweringContext::settle_constants`] has
    /// read every such binding.
    pub(super) fn settled(&self, name: &str) -> Option<Result<ConstTerm, Refused>> {
        let last = self.bindings.get(name)?.iter().max_by_key(|b| b.start)?;
        if !matches!(last.kind, BindingKind::Value { .. }) {
            return None;
        }
        self.terms.get(&(SmolStr::from(name), last.start)).cloned()
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

/// Why an expression has no term: its error, or `None` when it reads a member of a module
/// with errors of its own, which those errors account for.
#[derive(Debug, Clone)]
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

    /// The refusal of `name`, read at `span`, whose definition is not a constant for this
    /// reason: an error at the read, with the definition's own error beside it.
    fn of_definition(self, name: &str, span: Span) -> Refused {
        let Refused(Some(why)) = self else {
            return self;
        };
        let mut error = refused(
            span,
            format!("`{name}` is not a constant, since its definition is not one"),
        )
        .with_related(why.span(), why.to_string());
        error.related_mut().extend(why.related().iter().cloned());
        Refused(Some(error))
    }
}

impl LoweringContext {
    /// Read each `=` binding of the module as a constant, in source order, so the
    /// interface records which public members are constants. A binding that is not one
    /// reports nothing here: a read that requires a constant reports why.
    pub(super) fn settle_constants(&mut self) {
        for (name, start) in self.constants.value_bindings() {
            // The result is cached; nothing is reported unless a read requires it.
            let _ = self.const_binding_term(&name, start);
        }
    }

    /// The term of the `=` binding `name` whose statement starts at `start`, reading it
    /// once, or why its definition is not a constant.
    fn const_binding_term(&mut self, name: &SmolStr, start: usize) -> Result<ConstTerm, Refused> {
        let key = (name.clone(), start);
        if let Some(term) = self.constants.terms.get(&key) {
            return term.clone();
        }
        let binding = self.constants.bindings[name]
            .iter()
            .find(|b| b.start == start)
            .cloned()
            .expect("an `=` binding is recorded");
        let BindingKind::Value { definition, path } = binding.kind else {
            unreachable!("asked for the term of a binding that is not an `=` binding");
        };
        // A definition reads only bindings above it, so a binding is never read while its own
        // term is computed; the entry keeps such a read from recurring if one were.
        self.constants.terms.insert(key.clone(), Err(Refused(None)));
        let term = self.const_term(&definition, start).and_then(|term| {
            path.iter().try_fold(term, |term, &i| {
                let index = ConstTerm::Lit(Lit::Int(i64::try_from(i).expect("a tuple index fits")));
                ConstTerm::Element(Box::new(term), Box::new(index))
                    .normalized()
                    .map_err(|e| Refused::from(refused(definition.span, e.0)))
            })
        });
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
                 literals, constants, operators, and tuples, records and lists of them",
            )
            .into()),
            _ => Err(refused(
                span,
                "this is not a constant: a constant is built from literals, constants, \
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
                format!("`{name}` is not a constant: no top-level binding above names it"),
            )
            .into());
        };
        let not_const = |what: &str| {
            refused(
                span,
                format!(
                    "`{name}` is {what}, so it is not a constant: a constant reads only \
                     literals, constants and `const` parameters"
                ),
            )
        };
        match binding.kind {
            BindingKind::Value { .. } => self
                .const_binding_term(name, binding.start)
                .map_err(|why| why.of_definition(name, span)),
            BindingKind::ConstParam(param) => Ok(ConstTerm::Param(param)),
            BindingKind::Param => Err(not_const("a parameter without `const`").into()),
            BindingKind::Mutable => Err(not_const("a mutable variable").into()),
            BindingKind::Function => Err(not_const("a function").into()),
        }
    }

    /// The constant the top-level name `name` is, read at `span` from a declaration, which
    /// reads the last binding of a name, as the declaration stands ahead of the module's
    /// statements.
    pub(super) fn declared_const(
        &mut self,
        name: &SmolStr,
        span: Span,
    ) -> Result<ConstTerm, Refused> {
        self.const_name(name, span, usize::MAX)
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
    /// module's member, which is a constant if its definition is one.
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
            Some(Ok(term)) => term
                .substituted(&at.types.consts)
                .map_err(|e| refused(span, e.0).into()),
            Some(Err(why)) => Err(why
                .clone()
                .of_definition(&format!("{qualifier}::{member}"), span)),
            None => Err(refused(
                span,
                format!(
                    "`{qualifier}::{member}` is not a constant: module `{}` has no public \
                     binding `{member}`",
                    interface.module
                ),
            )
            .into()),
        }
    }
}
