//! The refusal of module syntax, which parses and does not lower yet.
//!
//! A program is one file until loading and imports exist (`docs/modules.md`,
//! "Implementation stack"). [`refuse_module_syntax`] finds every module construct
//! in a module, at any depth, and [`super::lower_stmts`] lowers nothing when it
//! finds one. No other lowering site therefore sees an [`ChlStmt::Import`],
//! [`ChlStmt::Run`], [`ChlStmt::Param`], [`ChlStmt::Discard`], [`ChlStmt::Pub`],
//! [`ChlExpr::Qualified`], a qualified label, or a qualified tag.

use super::LoweringError;
use crate::chl_parser::ast::{
    AssignTarget, CompClause, Comprehension, Expr as ChlExpr, IfBranch, MatchArm,
    Module as ChlModule, Param, RecordField, Span, Spanned, Stmt as ChlStmt, TypeAnnotation,
    VariantPayload,
};
use smol_str::SmolStr;

/// One error per module construct in `module`, in source order of traversal.
pub(super) fn refuse_module_syntax(module: &ChlModule) -> Vec<LoweringError> {
    let mut refusals = Refusals::default();
    refusals.stmts(&module.body);
    refusals.errors
}

/// Spell a qualified name as written: `shop::eu::stock`.
fn spell(qualifier: &[Spanned<SmolStr>], name: &str) -> String {
    let mut out = String::new();
    for segment in qualifier {
        out.push_str(&segment.node);
        out.push_str("::");
    }
    out.push_str(name);
    out
}

#[derive(Default)]
struct Refusals {
    errors: Vec<LoweringError>,
}

impl Refusals {
    fn refuse(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(LoweringError::unsupported(span, message));
    }

    fn stmts(&mut self, stmts: &[Spanned<ChlStmt>]) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn stmt(&mut self, stmt: &Spanned<ChlStmt>) {
        match &stmt.node {
            ChlStmt::Import { .. } => self.refuse(
                stmt.span,
                "`import` is not supported yet: a program is a single module",
            ),
            ChlStmt::Run { args, .. } => {
                self.refuse(
                    stmt.span,
                    "`run` is not supported yet: a program is a single module",
                );
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ChlStmt::Param {
                annotation,
                default,
                ..
            } => {
                self.refuse(
                    stmt.span,
                    "`param` is not supported yet: a program is a single module, and only a \
                     `run` supplies a parameter",
                );
                self.annotation(annotation.as_ref());
                if let Some(default) = default {
                    self.expr(default);
                }
            }
            ChlStmt::Discard(_) => self.refuse(stmt.span, "`@Discard` is not supported yet"),
            ChlStmt::Pub { keyword, stmt } => {
                self.refuse(
                    *keyword,
                    "`pub` is not supported yet: a program is a single module, and nothing \
                     imports its members",
                );
                // The statement `pub` marks is checked as any other.
                self.stmt(stmt);
            }
            ChlStmt::Expr(e) | ChlStmt::Return(Some(e)) => self.expr(e),
            ChlStmt::Assign { target, value } | ChlStmt::Define { target, value } => {
                self.target(target);
                self.expr(value);
            }
            ChlStmt::AugAssign { target, value, .. } => {
                self.target(target);
                self.expr(value);
            }
            ChlStmt::AnnAssign {
                target,
                annotation,
                value,
            } => {
                self.target(target);
                self.annotation(Some(annotation));
                self.expr(value);
            }
            ChlStmt::MutAssign {
                target,
                annotation,
                value,
            } => {
                self.target(target);
                self.annotation(annotation.as_ref());
                self.expr(value);
            }
            ChlStmt::LoadFrom {
                target, annotation, ..
            } => {
                self.target(target);
                self.annotation(Some(annotation));
            }
            ChlStmt::If {
                branches,
                else_body,
            } => {
                for IfBranch { cond, body } in branches {
                    self.expr(cond);
                    self.stmts(body);
                }
                if let Some(body) = else_body {
                    self.stmts(body);
                }
            }
            ChlStmt::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                self.arms(arms);
            }
            ChlStmt::For { target, iter, body } => {
                self.target(target);
                self.expr(iter);
                self.stmts(body);
            }
            ChlStmt::FunctionDef {
                params,
                output,
                body,
                ..
            } => {
                self.params(params);
                if let Some(output) = output {
                    self.expr(output);
                }
                self.stmts(body);
            }
            ChlStmt::With { context, body, .. } => {
                self.expr(context);
                self.stmts(body);
            }
            ChlStmt::Return(None) | ChlStmt::Pass | ChlStmt::Error => {}
        }
    }

    fn arms(&mut self, arms: &[MatchArm]) {
        for arm in arms {
            if let Some(pattern) = &arm.pattern {
                self.tag(&pattern.tag_qualifier, &pattern.tag, pattern.tag_span);
            }
            self.stmts(&arm.body);
        }
    }

    fn tag(&mut self, qualifier: &[Spanned<SmolStr>], tag: &str, tag_span: Span) {
        if let Some(first) = qualifier.first() {
            self.refuse(
                first.span.join(tag_span),
                format!(
                    "the qualified tag `{}` is not supported yet: a program is a single module",
                    spell(qualifier, &format!("`{tag}"))
                ),
            );
        }
    }

    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.annotation(param.annotation.as_ref());
        }
    }

    fn annotation(&mut self, annotation: Option<&TypeAnnotation>) {
        if let Some(annotation) = annotation {
            self.expr(&annotation.ty);
        }
    }

    fn target(&mut self, target: &Spanned<AssignTarget>) {
        match &target.node {
            AssignTarget::Name(_) => {}
            AssignTarget::Tuple(targets) => {
                for target in targets {
                    self.target(target);
                }
            }
            AssignTarget::Subscript { target, index } => {
                self.expr(target);
                self.expr(index);
            }
        }
    }

    fn fields(&mut self, fields: &[RecordField]) {
        for field in fields {
            self.label(&field.qualifier, &field.name, field.name_span);
            self.expr(&field.value);
        }
    }

    fn label(&mut self, qualifier: &[Spanned<SmolStr>], name: &str, name_span: Span) {
        if let Some(first) = qualifier.first() {
            self.refuse(
                first.span.join(name_span),
                format!(
                    "the qualified label `{}` is not supported yet: a program is a single module",
                    spell(qualifier, name)
                ),
            );
        }
    }

    fn comprehension(&mut self, comp: &Comprehension) {
        self.expr(&comp.element);
        for clause in &comp.clauses {
            match clause {
                CompClause::For { target, iter } => {
                    self.target(target);
                    self.expr(iter);
                }
                CompClause::If(guard) => self.expr(guard),
            }
        }
    }

    fn expr(&mut self, expr: &Spanned<ChlExpr>) {
        match &expr.node {
            ChlExpr::Qualified(q) => self.refuse(
                expr.span,
                format!(
                    "the qualified name `{}` is not supported yet: a program is a single module",
                    spell(&q.qualifier, &q.name.node)
                ),
            ),
            ChlExpr::Attribute {
                target,
                attr,
                attr_span,
                attr_qualifier,
            } => {
                self.expr(target);
                self.label(attr_qualifier, attr, *attr_span);
            }
            ChlExpr::Record(fields) | ChlExpr::BraceRecord(fields) => self.fields(fields),
            ChlExpr::Lit(_) | ChlExpr::Name(_) | ChlExpr::Error => {}
            ChlExpr::BinOp { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ChlExpr::UnaryOp { operand, .. } => self.expr(operand),
            ChlExpr::BoolOp { operands, .. } => {
                for operand in operands {
                    self.expr(operand);
                }
            }
            ChlExpr::Compare {
                left, comparators, ..
            } => {
                self.expr(left);
                for comparator in comparators {
                    self.expr(comparator);
                }
            }
            ChlExpr::Call { func, args } => {
                self.expr(func);
                for arg in args {
                    self.expr(arg);
                }
            }
            ChlExpr::List(elts) | ChlExpr::Tuple(elts) | ChlExpr::BraceGroup(elts) => {
                for elt in elts {
                    self.expr(elt);
                }
            }
            ChlExpr::BraceRefinement { base, predicate } => {
                self.expr(base);
                self.expr(predicate);
            }
            ChlExpr::FunctionType { domain, codomain } => {
                self.expr(domain);
                self.expr(codomain);
            }
            ChlExpr::Subscript { target, index, .. } => {
                self.expr(target);
                self.expr(index);
            }
            ChlExpr::VariantCtor {
                tag,
                tag_span,
                tag_qualifier,
                payload,
            } => {
                self.tag(tag_qualifier, tag, *tag_span);
                if let Some(VariantPayload::Term(p) | VariantPayload::Fields(p)) = payload {
                    self.expr(p);
                }
            }
            ChlExpr::Lambda { params, body } => {
                self.params(params);
                self.expr(body);
            }
            ChlExpr::IfExp {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr(cond);
                self.expr(then_expr);
                self.expr(else_expr);
            }
            ChlExpr::ListComp(comp) | ChlExpr::GenExp(comp) => self.comprehension(comp),
            ChlExpr::Yield(value) => self.expr(value),
            ChlExpr::Feed { target, value } => {
                self.expr(target);
                self.expr(value);
            }
            ChlExpr::Block(stmt) => self.stmt(stmt),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{LoweringContext, lower_stmts, test_helpers::parse_module};
    use indoc::indoc;

    /// Each refusal of `src`, as the source text its span covers and its
    /// message.
    fn refusals(src: &str) -> Vec<(String, String)> {
        let result = lower_stmts(&parse_module(src), &mut LoweringContext::default());
        assert!(
            result.value.is_none(),
            "a module using module syntax lowers nothing"
        );
        result
            .errors
            .iter()
            .map(|e| (src[e.span().as_range()].to_string(), e.to_string()))
            .collect()
    }

    /// The source text each refusal of `src` covers.
    fn refused_spans(src: &str) -> Vec<String> {
        refusals(src).into_iter().map(|(text, _)| text).collect()
    }

    #[test]
    fn each_module_statement_is_refused_at_its_span() {
        let refused = refusals(indoc! {r#"
            import catalog use Item
            run audit
            param port: String
            @Discard
            stock
            1
        "#});
        let messages: Vec<&str> = refused.iter().map(|(_, m)| m.as_str()).collect();
        assert!(messages[0].starts_with("`import` is not supported yet"));
        assert!(messages[1].starts_with("`run` is not supported yet"));
        assert!(messages[2].starts_with("`param` is not supported yet"));
        assert_eq!(messages[3], "`@Discard` is not supported yet");
        let spans: Vec<&str> = refused.iter().map(|(s, _)| s.trim_end()).collect();
        assert_eq!(
            spans,
            [
                "import catalog use Item",
                "run audit",
                "param port: String",
                "@Discard\nstock"
            ]
        );
    }

    /// `pub` is refused at the keyword, and the statement it marks is checked
    /// as any other.
    #[test]
    fn pub_is_refused_at_its_keyword() {
        let refused = refusals("pub limit = cart::max_items\nlimit\n");
        assert_eq!(refused.len(), 2, "{refused:#?}");
        assert_eq!(refused[0].0, "pub");
        assert!(refused[0].1.starts_with("`pub` is not supported yet"));
        assert_eq!(refused[1].0, "cart::max_items");
        assert!(
            refused[1]
                .1
                .starts_with("the qualified name `cart::max_items` is not supported yet")
        );
    }

    /// A qualified name or label is refused wherever it stands: in a type, a
    /// lambda inside a `def`, a block value, and a comprehension.
    #[test]
    fn a_qualified_name_is_refused_at_any_depth() {
        assert_eq!(
            refused_spans(indoc! {"
                def total(items: catalog::Items):
                    f = \\x -> x.catalog::price
                    [f(i) for i in items if i.this::ok]
                n = if ready:
                        (shop::eu::stock).count
                    else:
                        0
                {k: cart::K}
            "}),
            [
                "catalog::Items",
                "catalog::price",
                "this::ok",
                "shop::eu::stock",
                "cart::K",
            ]
        );
    }

    #[test]
    fn a_qualified_record_label_is_refused() {
        let refused = refusals("r = (catalog::price=25, cost=11)\nr\n");
        assert_eq!(refused.len(), 1, "{refused:#?}");
        assert_eq!(refused[0].0, "catalog::price");
        assert!(
            refused[0]
                .1
                .starts_with("the qualified label `catalog::price` is not supported yet")
        );
    }

    #[test]
    fn a_qualified_tag_is_refused_in_a_constructor_and_a_pattern() {
        let refused = refusals(indoc! {"
            o = mod2::`some(1)
            match o:
                case mod2::`some(v):
                    v
                case `none:
                    0
        "});
        let spans: Vec<&str> = refused.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(spans, ["mod2::`some", "mod2::`some"]);
        assert!(
            refused[0]
                .1
                .starts_with("the qualified tag `mod2::`some` is not supported yet")
        );
    }

    /// A loaded declaration's `pub` is refused at the keyword, on the line
    /// below the decorator.
    #[test]
    fn pub_on_a_loaded_declaration_is_refused_at_its_keyword() {
        assert_eq!(
            refused_spans("@LoadFrom(qty)\npub held: Int\nheld\n"),
            ["pub"]
        );
    }

    #[test]
    fn a_run_argument_is_checked() {
        assert_eq!(
            refused_spans("run storefront(audit=audit_api::log)\n"),
            ["run storefront(audit=audit_api::log)", "audit_api::log"]
        );
    }
}
