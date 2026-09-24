//! The list-literal rule: a list literal's elements are constants (`docs/chl-spec.md`,
//! "3.11 List, tuple, record literals").
//!
//! The check is syntactic and runs over the parsed program before lowering, so a refusal
//! carries the element's span. A name **varies** where it is bound by an enclosing `for`
//! loop, comprehension clause, lambda or `def` parameter, where it is a mutable variable
//! written inside the enclosing loop, or where it is assigned from an expression that
//! mentions a varying name. An element that mentions a varying name breaks the rule. The
//! check does not look through calls: a `def` parameter varies inside the body even where
//! every call passes a constant.

use std::collections::HashSet;

use crate::chl_parser::ast::{
    AssignTarget, CompClause, Comprehension, Expr as ChlExpr, PayloadPattern, Spanned,
    Stmt as ChlStmt, VariantPayload,
};

use super::LoweringError;

/// Every list element in `stmts` that mentions a varying name, as a refusal at the
/// element's span.
pub(super) fn check_constant_list_elements(stmts: &[Spanned<ChlStmt>]) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    check_block(stmts, &HashSet::new(), &mut errors);
    errors
}

type Varying = HashSet<String>;

fn check_block(stmts: &[Spanned<ChlStmt>], varying: &Varying, errors: &mut Vec<LoweringError>) {
    let mut varying = varying.clone();
    for stmt in stmts {
        check_stmt(stmt, &mut varying, errors);
    }
}

fn check_stmt(stmt: &Spanned<ChlStmt>, varying: &mut Varying, errors: &mut Vec<LoweringError>) {
    match &stmt.node {
        ChlStmt::Expr(e) | ChlStmt::Return(Some(e)) => check_expr(e, varying, errors),
        ChlStmt::Assign { target, value }
        | ChlStmt::AnnAssign { target, value, .. }
        | ChlStmt::Define { target, value } => {
            check_expr(value, varying, errors);
            // A binding is a new name: it varies exactly when its value does.
            let varies = first_varying(value, varying).is_some();
            for name in target_names(target) {
                bind(varying, name, varies);
            }
        }
        // A loaded value comes from the version this one replaces, not from anything in
        // scope, so the name it binds does not vary.
        ChlStmt::LoadFrom { target, .. } => {
            for name in target_names(target) {
                bind(varying, name, false);
            }
        }
        ChlStmt::MutAssign { target, value, .. } | ChlStmt::AugAssign { target, value, .. } => {
            check_expr(value, varying, errors);
            if let AssignTarget::Subscript { index, .. } = &target.node {
                check_expr(index, varying, errors);
            }
            // A write changes an existing variable, so a varying value makes it vary and a
            // constant one leaves it as it was.
            if first_varying(value, varying).is_some() {
                varying.extend(written_name(target));
            }
        }
        ChlStmt::If {
            branches,
            else_body,
        } => {
            for branch in branches {
                check_expr(&branch.cond, varying, errors);
                check_block(&branch.body, varying, errors);
            }
            if let Some(body) = else_body {
                check_block(body, varying, errors);
            }
        }
        ChlStmt::Match { scrutinee, arms } => {
            check_expr(scrutinee, varying, errors);
            let varies = first_varying(scrutinee, varying).is_some();
            for arm in arms {
                let mut inner = varying.clone();
                if let Some(PayloadPattern::Named(n)) = arm.pattern.as_ref().map(|p| &p.payload) {
                    bind(&mut inner, n.to_string(), varies);
                }
                check_block(&arm.body, &inner, errors);
            }
        }
        ChlStmt::For { target, iter, body } => {
            check_expr(iter, varying, errors);
            // Inside the body the loop variable varies, and so does every mutable variable
            // the body writes: each iteration sees a different value of it.
            let mut inner = varying.clone();
            inner.extend(target_names(target));
            collect_mut_writes(body, &mut inner);
            check_block(body, &inner, errors);
        }
        ChlStmt::FunctionDef { params, body, .. } => {
            let mut inner = varying.clone();
            inner.extend(params.iter().map(|p| p.name.to_string()));
            check_block(body, &inner, errors);
        }
        ChlStmt::With { body, .. } => check_block(body, varying, errors),
        ChlStmt::Return(None) | ChlStmt::Pass | ChlStmt::Error => {}
    }
}

fn check_expr(e: &Spanned<ChlExpr>, varying: &Varying, errors: &mut Vec<LoweringError>) {
    match &e.node {
        ChlExpr::List(elements) => {
            for element in elements {
                if let Some(name) = first_varying(element, varying) {
                    errors.push(LoweringError::unsupported(
                        element.span,
                        format!(
                            "a list element must be a constant, but this one varies with `{name}`"
                        ),
                    ));
                }
                check_expr(element, varying, errors);
            }
        }
        ChlExpr::Lambda { params, body } => {
            let mut inner = varying.clone();
            inner.extend(params.iter().map(|p| p.name.to_string()));
            check_expr(body, &inner, errors);
        }
        ChlExpr::ListComp(comp) | ChlExpr::GenExp(comp) => {
            let inner = comprehension_scope(comp, varying, &mut |e, v| check_expr(e, v, errors));
            check_expr(&comp.element, &inner, errors);
        }
        ChlExpr::Block(stmt) => check_stmt(stmt, &mut varying.clone(), errors),
        _ => {
            for child in children(&e.node) {
                check_expr(child, varying, errors);
            }
        }
    }
}

/// The first varying name `e` mentions, if any.
fn first_varying(e: &Spanned<ChlExpr>, varying: &Varying) -> Option<String> {
    match &e.node {
        ChlExpr::Name(n) => varying.contains(n.as_str()).then(|| n.to_string()),
        // A parameter shadows the name it spells.
        ChlExpr::Lambda { params, body } => {
            let mut inner = varying.clone();
            for p in params {
                inner.remove(p.name.as_str());
            }
            first_varying(body, &inner)
        }
        ChlExpr::ListComp(comp) | ChlExpr::GenExp(comp) => {
            let mut found = None;
            let mut inner = varying.clone();
            for clause in &comp.clauses {
                match clause {
                    CompClause::For { target, iter } => {
                        found = found.or_else(|| first_varying(iter, &inner));
                        for n in target_names(target) {
                            inner.remove(&n);
                        }
                    }
                    CompClause::If(guard) => found = found.or_else(|| first_varying(guard, &inner)),
                }
            }
            found.or_else(|| first_varying(&comp.element, &inner))
        }
        ChlExpr::Block(stmt) => first_varying_in_stmt(stmt, varying),
        other => children(other)
            .into_iter()
            .find_map(|child| first_varying(child, varying)),
    }
}

fn first_varying_in_stmt(stmt: &Spanned<ChlStmt>, varying: &Varying) -> Option<String> {
    match &stmt.node {
        ChlStmt::Expr(e) | ChlStmt::Return(Some(e)) => first_varying(e, varying),
        ChlStmt::If {
            branches,
            else_body,
        } => branches
            .iter()
            .find_map(|b| {
                first_varying(&b.cond, varying).or_else(|| first_varying_in_block(&b.body, varying))
            })
            .or_else(|| {
                else_body
                    .as_ref()
                    .and_then(|b| first_varying_in_block(b, varying))
            }),
        ChlStmt::Match { scrutinee, arms } => first_varying(scrutinee, varying).or_else(|| {
            arms.iter()
                .find_map(|arm| first_varying_in_block(&arm.body, varying))
        }),
        _ => None,
    }
}

fn first_varying_in_block(stmts: &[Spanned<ChlStmt>], varying: &Varying) -> Option<String> {
    stmts.iter().find_map(|s| first_varying_in_stmt(s, varying))
}

/// Walk a comprehension's clauses, calling `visit` on each iterator and guard in the scope it
/// sits in, and answer the scope its element sits in.
fn comprehension_scope(
    comp: &Comprehension,
    varying: &Varying,
    visit: &mut dyn FnMut(&Spanned<ChlExpr>, &Varying),
) -> Varying {
    let mut inner = varying.clone();
    for clause in &comp.clauses {
        match clause {
            CompClause::For { target, iter } => {
                visit(iter, &inner);
                inner.extend(target_names(target));
            }
            CompClause::If(guard) => visit(guard, &inner),
        }
    }
    inner
}

/// The sub-expressions of a node that binds nothing.
fn children(e: &ChlExpr) -> Vec<&Spanned<ChlExpr>> {
    match e {
        ChlExpr::BinOp { left, right, .. } => vec![left, right],
        ChlExpr::UnaryOp { operand, .. } => vec![operand],
        ChlExpr::BoolOp { operands, .. } => operands.iter().collect(),
        ChlExpr::Compare {
            left, comparators, ..
        } => std::iter::once(&**left).chain(comparators).collect(),
        ChlExpr::Call { func, args } => std::iter::once(&**func).chain(args).collect(),
        ChlExpr::List(items) | ChlExpr::Tuple(items) | ChlExpr::BraceGroup(items) => {
            items.iter().collect()
        }
        ChlExpr::Record(fields) | ChlExpr::BraceRecord(fields) => {
            fields.iter().map(|f| &f.value).collect()
        }
        ChlExpr::Subscript { target, index, .. } => vec![target, index],
        ChlExpr::Attribute { target, .. } => vec![target],
        ChlExpr::VariantCtor {
            payload: Some(VariantPayload::Term(inner)),
            ..
        } => vec![inner],
        ChlExpr::IfExp {
            cond,
            then_expr,
            else_expr,
        } => vec![cond, then_expr, else_expr],
        ChlExpr::Yield(inner) => vec![inner],
        ChlExpr::Feed { target, value } => vec![target, value],
        // Type syntax, literals and the binding forms, which the callers handle.
        _ => Vec::new(),
    }
}

fn target_names(target: &Spanned<AssignTarget>) -> Vec<String> {
    match &target.node {
        AssignTarget::Name(n) => vec![n.to_string()],
        AssignTarget::Tuple(parts) => parts.iter().flat_map(target_names).collect(),
        AssignTarget::Subscript { .. } => Vec::new(),
    }
}

/// The mutable variable a write changes: `x` for `x := e`, `m` for `m[k] := e`.
fn written_name(target: &Spanned<AssignTarget>) -> Option<String> {
    match &target.node {
        AssignTarget::Name(n) => Some(n.to_string()),
        AssignTarget::Subscript { target, .. } => match &target.node {
            ChlExpr::Name(n) => Some(n.to_string()),
            _ => None,
        },
        AssignTarget::Tuple(_) => None,
    }
}

/// Record whether a newly bound `name` varies, shadowing any earlier binding of it.
fn bind(varying: &mut Varying, name: String, varies: bool) {
    if varies {
        varying.insert(name);
    } else {
        varying.remove(&name);
    }
}

/// Every mutable variable a write anywhere in `stmts` changes.
fn collect_mut_writes(stmts: &[Spanned<ChlStmt>], out: &mut Varying) {
    for stmt in stmts {
        match &stmt.node {
            ChlStmt::MutAssign { target, .. } | ChlStmt::AugAssign { target, .. } => {
                out.extend(written_name(target));
            }
            ChlStmt::If {
                branches,
                else_body,
            } => {
                for b in branches {
                    collect_mut_writes(&b.body, out);
                }
                if let Some(body) = else_body {
                    collect_mut_writes(body, out);
                }
            }
            ChlStmt::Match { arms, .. } => {
                for arm in arms {
                    collect_mut_writes(&arm.body, out);
                }
            }
            ChlStmt::For { body, .. } | ChlStmt::With { body, .. } => collect_mut_writes(body, out),
            _ => {}
        }
    }
}
