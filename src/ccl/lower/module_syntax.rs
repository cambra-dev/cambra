//! The refusal of module syntax that parses and does not lower yet, and the
//! placement rules of module statements.
//!
//! [`refuse_module_syntax`] finds every such construct in a module, at any
//! depth, and the module lowers nothing when it finds one. It refuses
//! `@RenamedFrom`, `@Discard`, `pub` on a mutable variable, a write to another
//! module's member, and a method named through an attribute's qualifier,
//! `x.mod::Price::discounted`. A qualified value, type, label, or tag reaches
//! lowering, which resolves it against the module's names that denote a module
//! (`super::modules`), and so does a name qualified by a type, `Shape::circle`
//! or `shop::Shape::circle`, which lowering resolves among the nominal types the
//! module reaches. Lowering therefore sees a top-level [`ChlStmt::Import`],
//! [`ChlStmt::Run`], [`ChlStmt::Param`], [`ChlStmt::Pub`] on a binding or a
//! declaration, and `const` on a binding or a value parameter, and no other module
//! statement.
//!
//! The walk also collects every binder the module writes, for the rule that no
//! binder takes the spelling of a name that denotes a module
//! (`docs/chl-spec.md`, "9.6 Qualified references").

use super::LoweringError;
use crate::chl_parser::ast::{
    ArmPattern, AssignTarget, CompClause, Comprehension, ConstructorPattern, DiscardHead,
    Expr as ChlExpr, IfBranch, KindAnnotation, MatchArm, Module as ChlModule, Param,
    PayloadPattern, QualifiedName, RecordField, Requirement, Span, Spanned, Stmt as ChlStmt,
    TraitItem, TraitType, TypeAnnotation, TypeDeclBody, TypeParam, VariantPayload, is_type_name,
};
use smol_str::SmolStr;

/// What [`refuse_module_syntax`] finds in a module.
pub(super) struct ModuleSyntax {
    /// One error per refused construct, in source order of traversal.
    pub errors: Vec<LoweringError>,
    /// Every name the module binds, at any depth, with where it is bound.
    pub binders: Vec<(SmolStr, Span)>,
}

/// The refused module constructs of `module`, and the names it binds.
pub(super) fn refuse_module_syntax(module: &ChlModule) -> ModuleSyntax {
    let mut refusals = Refusals::default();
    for stmt in &module.body {
        refusals.stmt(stmt);
    }
    ModuleSyntax {
        errors: refusals.errors,
        binders: refusals.binders,
    }
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

/// Whether a `::` path names a method rather than a module member: a capitalized
/// qualifier segment is the type the method belongs to (`docs/chl-spec.md`, "6.8
/// Nominal types and methods \[Decided\]").
fn names_a_method(qualifier: &[Spanned<SmolStr>]) -> bool {
    qualifier.iter().any(|segment| is_type_name(&segment.node))
}

#[derive(Default)]
struct Refusals {
    errors: Vec<LoweringError>,
    binders: Vec<(SmolStr, Span)>,
    /// How many statement bodies enclose the statement being checked: 0 at the
    /// module's top level.
    depth: usize,
}

impl Refusals {
    fn refuse(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(LoweringError::unsupported(span, message));
    }

    /// The statements of a body nested in a statement or an expression.
    fn stmts(&mut self, stmts: &[Spanned<ChlStmt>]) {
        self.depth += 1;
        for stmt in stmts {
            self.stmt(stmt);
        }
        self.depth -= 1;
    }

    fn stmt(&mut self, stmt: &Spanned<ChlStmt>) {
        // `import`, `run`, `param` and `pub` stand only at a module's top level
        // (`docs/chl-spec.md`, "9.2 Imports"), and so does the tombstone of a
        // `run` or an `import`, which stands where the statement stood
        // (`docs/chl-spec.md`, "8.9 `@Discard` \[Decided\]"). Loading follows only
        // top-level `import` and `run` statements, so a nested one names no module.
        if self.depth > 0 {
            let keyword = match &stmt.node {
                ChlStmt::Import { .. } => Some("import"),
                ChlStmt::Run { .. } => Some("run"),
                ChlStmt::Param { .. } => Some("param"),
                ChlStmt::Pub { .. } => Some("pub"),
                ChlStmt::Discard(DiscardHead::Run { .. }) => Some("@Discard run"),
                _ => None,
            };
            if let Some(keyword) = keyword {
                let span = match &stmt.node {
                    ChlStmt::Pub { keyword, .. } => *keyword,
                    _ => stmt.span,
                };
                return self.refuse(
                    span,
                    format!("`{keyword}` stands only at a module's top level"),
                );
            }
        }
        match &stmt.node {
            ChlStmt::Run {
                args, renamed_from, ..
            } => {
                if let Some(renamed_from) = renamed_from {
                    self.refuse(renamed_from.span, "`@RenamedFrom` is not supported yet");
                }
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ChlStmt::Param {
                name,
                annotation,
                default,
                constant,
            } => {
                if annotation.is_none() && !is_type_name(&name.node) {
                    // A value parameter states its type, if only as `_`, so a module says
                    // what each argument is (`docs/chl-spec.md`, "9.4 Parameters").
                    self.refuse(
                        name.span,
                        format!(
                            "the parameter `{0}` has no annotation: write its type, `param {0}: \
                             Int`, or `param {0}: _` to infer it from the module's uses",
                            name.node
                        ),
                    );
                }
                if let Some(keyword) = constant
                    && is_type_name(&name.node)
                {
                    self.refuse(
                        *keyword,
                        format!(
                            "`{}` is a type parameter, which is fixed at link time already; \
                             `const` marks a value parameter",
                            name.node
                        ),
                    );
                }
                self.binders.push((name.node.clone(), name.span));
                self.annotation(annotation.as_ref());
                if let Some(default) = default {
                    self.expr(default);
                }
            }
            ChlStmt::Discard(_) => self.refuse(stmt.span, "`@Discard` is not supported yet"),
            ChlStmt::Pub { keyword, stmt } => {
                match &stmt.node {
                    ChlStmt::Assign { .. }
                    | ChlStmt::AnnAssign { .. }
                    | ChlStmt::FunctionDef { .. } => {}
                    ChlStmt::MutAssign { .. } | ChlStmt::LoadFrom { .. } => {
                        self.refuse(*keyword, "a public mutable variable is not supported yet")
                    }
                    // `pub` on a `type` exports it, and on any other statement it is a
                    // parse error.
                    _ => {}
                }
                // The statement `pub` marks is checked as any other.
                self.stmt(stmt);
            }
            ChlStmt::Expr(e) | ChlStmt::Return(Some(e)) => self.expr(e),
            ChlStmt::Assign { target, value, .. } | ChlStmt::Define { target, value } => {
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
            }
            | ChlStmt::Declare { target, annotation } => {
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
                owner,
                name,
                type_params,
                params,
                output,
                requires,
                body,
            } => {
                // An associated function's name is a member of its type, not a binder of
                // the module.
                if owner.is_none() {
                    self.binders.push((name.node.clone(), stmt.span));
                }
                self.type_params(type_params);
                self.params(params);
                if let Some(output) = output {
                    self.expr(output);
                }
                self.requires(requires);
                self.stmts(body);
            }
            ChlStmt::With {
                binding,
                context,
                body,
            } => {
                if let Some(binding) = binding {
                    self.binders.push((binding.clone(), stmt.span));
                }
                self.expr(context);
                self.stmts(body);
            }
            ChlStmt::Impl(block) => {
                for arg in &block.args {
                    self.expr(arg);
                }
                for assoc in &block.assoc {
                    self.expr(&assoc.value);
                }
                self.requires(&block.requires);
                // A block's `def`s stand at the block's own depth, so `pub` marks one at a
                // module's top level (`docs/chl-spec.md`, "Associated functions and methods").
                for def in &block.defs {
                    self.stmt(def);
                }
            }
            ChlStmt::TraitDecl(decl) => {
                for item in &decl.items {
                    if let TraitItem::Function(sig) = item {
                        self.type_params(&sig.node.type_params);
                        self.params(&sig.node.params);
                        if let Some(output) = &sig.node.output {
                            self.expr(output);
                        }
                        self.requires(&sig.node.requires);
                    }
                }
            }
            ChlStmt::TypeDecl(decl) => match &decl.body {
                TypeDeclBody::Constructors(ctors) => {
                    for ctor in ctors {
                        for param in &ctor.params {
                            self.expr(&param.ty);
                        }
                    }
                }
                TypeDeclBody::Single(ty) => self.expr(ty),
            },
            // An import's module, arguments, and `use` items resolve against
            // the program (`super::modules`).
            ChlStmt::Import { args, .. } => {
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ChlStmt::Return(None) | ChlStmt::Pass | ChlStmt::Error => {}
        }
    }

    fn arms(&mut self, arms: &[MatchArm]) {
        for arm in arms {
            match &arm.pattern {
                Some(ArmPattern::Tag(pattern)) => {
                    if let PayloadPattern::Named(binder) = &pattern.payload {
                        self.binders.push((binder.node.clone(), pattern.tag_span));
                    }
                }
                Some(ArmPattern::Constructor(pattern)) => self.constructor_pattern(pattern),
                None => {}
            }
            self.stmts(&arm.body);
        }
    }

    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.binders.push((param.name.clone(), param.name_span));
            self.annotation(param.annotation.as_ref());
        }
    }

    fn type_params(&mut self, type_params: &[TypeParam]) {
        for param in type_params {
            match &param.annotation {
                Some(KindAnnotation::Kind(ty) | KindAnnotation::Bound(ty)) => self.expr(ty),
                None => {}
            }
        }
    }

    fn requires(&mut self, requires: &[Spanned<Requirement>]) {
        for requirement in requires {
            match &requirement.node {
                Requirement::Trait { ty, .. } => self.trait_type(ty),
                Requirement::Bound { bound, .. } => self.expr(bound),
            }
        }
    }

    fn trait_type(&mut self, ty: &TraitType) {
        for arg in &ty.args {
            self.expr(arg);
        }
    }

    fn annotation(&mut self, annotation: Option<&TypeAnnotation>) {
        if let Some(annotation) = annotation {
            self.expr(&annotation.ty);
        }
    }

    fn target(&mut self, target: &Spanned<AssignTarget>) {
        match &target.node {
            AssignTarget::Name(name) => self.binders.push((name.clone(), target.span)),
            AssignTarget::Tuple(targets) => {
                for target in targets {
                    self.target(target);
                }
            }
            AssignTarget::Subscript { target, index } => {
                self.expr(target);
                self.expr(index);
            }
            AssignTarget::Qualified(q) => {
                let spelled = spell(&q.qualifier, &q.name.node);
                if names_a_method(&q.qualifier) {
                    return self.method_reference(target.span, &spelled);
                }
                self.refuse(
                    target.span,
                    format!(
                        "writing `{spelled}`, a member of another module, is not supported yet"
                    ),
                );
            }
            AssignTarget::Constructor(pattern) => self.constructor_pattern(pattern),
        }
    }

    /// A constructor pattern's binders.
    fn constructor_pattern(&mut self, pattern: &ConstructorPattern) {
        for binder in pattern.binders.iter().flatten() {
            if let Some(name) = &binder.node {
                self.binders.push((name.clone(), binder.span));
            }
        }
    }

    /// A qualified value reference reaches lowering, which resolves it, unless a
    /// capitalized segment makes it a method reference.
    fn qualified(&mut self, q: &QualifiedName, span: Span) {
        if names_a_method(&q.qualifier) {
            self.method_reference(span, &spell(&q.qualifier, &q.name.node));
        }
    }

    fn method_reference(&mut self, span: Span, spelled: &str) {
        self.refuse(
            span,
            format!("the method reference `{spelled}` is not supported yet"),
        );
    }

    fn fields(&mut self, fields: &[RecordField]) {
        for field in fields {
            self.expr(&field.value);
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
            // A name qualified by a type is a member of that type, which lowering
            // resolves (`lower::nominal`).
            ChlExpr::Qualified(q) if super::nominal::names_a_type_member(q) => {}
            ChlExpr::MethodCall { receiver, args, .. } => {
                self.expr(receiver);
                for a in args {
                    self.expr(a);
                }
            }
            ChlExpr::Qualified(q) => self.qualified(q, expr.span),
            ChlExpr::Summon { trait_type, .. } => self.trait_type(&trait_type.node),
            ChlExpr::Attribute {
                target,
                attr,
                attr_span,
                attr_qualifier,
            } => {
                self.expr(target);
                if let Some(first) = attr_qualifier.first()
                    && names_a_method(attr_qualifier)
                {
                    self.method_reference(
                        first.span.join(*attr_span),
                        &spell(attr_qualifier, attr),
                    );
                }
            }
            ChlExpr::Record(fields) | ChlExpr::BraceRecord(fields) => self.fields(fields),
            ChlExpr::ModuleType(entries) => {
                for entry in entries {
                    self.expr(&entry.value);
                }
            }
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
            ChlExpr::Forall {
                type_params,
                body,
                requires,
            } => {
                self.type_params(type_params);
                self.expr(body);
                self.requires(requires);
            }
            ChlExpr::FunctionType {
                domain, codomain, ..
            } => {
                self.expr(domain);
                self.expr(codomain);
            }
            ChlExpr::Subscript { target, index, .. } => {
                self.expr(target);
                self.expr(index);
            }
            ChlExpr::VariantCtor { payload, .. } => {
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
            @RenamedFrom(old)
            run audit(log=1)
            @Discard
            stock
            1
        "#});
        let messages: Vec<&str> = refused.iter().map(|(_, m)| m.as_str()).collect();
        assert_eq!(messages[0], "`@RenamedFrom` is not supported yet");
        assert_eq!(messages[1], "`@Discard` is not supported yet");
        let spans: Vec<&str> = refused.iter().map(|(s, _)| s.trim_end()).collect();
        assert_eq!(spans, ["old", "@Discard\nstock"]);
    }

    /// `pub` on a mutable variable is refused at the keyword, and the
    /// statement it marks is checked as any other.
    #[test]
    fn pub_on_a_mutable_variable_is_refused_at_its_keyword() {
        let refused = refusals(indoc! {"
            pub stock := x.mod::Price::zero
            stock
        "});
        assert_eq!(refused.len(), 2, "{refused:#?}");
        assert_eq!(refused[0].0, "pub");
        assert_eq!(
            refused[0].1,
            "a public mutable variable is not supported yet"
        );
        assert_eq!(refused[1].0, "mod::Price::zero");
    }

    /// A value binding, a `def` and a type alias take `pub`, and a qualified
    /// value, label or tag is left to lowering, which resolves it.
    #[test]
    fn pub_on_a_value_binding_and_a_qualified_name_pass() {
        let syntax = super::refuse_module_syntax(&parse_module(indoc! {"
            pub limit = cart::max_items
            pub def f(x):
                (cart::price=x.cart::cost, tag=cart::`some(1))
            pub Dollars = Int
            limit
        "}));
        assert!(syntax.errors.is_empty(), "{:#?}", syntax.errors);
    }

    /// Every binder is collected, at any depth, for the rule that none takes an
    /// import name.
    #[test]
    fn every_binder_is_collected() {
        let syntax = super::refuse_module_syntax(&parse_module(indoc! {"
            a, b = (1, 2)
            def f(x, y):
                g = \\z -> z
                [w for w in x]
            match o:
                case `some(v):
                    v
                case `none:
                    0
        "}));
        let names: Vec<&str> = syntax.binders.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["a", "b", "f", "x", "y", "g", "z", "w", "v"]);
    }

    /// A name qualified by a type, `Price::discounted` or `mod::Price::discounted`, is
    /// left to lowering, which resolves it among the nominal types the module reaches. A
    /// type in an attribute's qualifier, `x.mod::Price::discounted`, is refused as a
    /// method reference.
    #[test]
    fn a_type_in_an_attributes_qualifier_is_refused_as_a_method_reference() {
        let refused = refusals(indoc! {"
            e = Price::discounted
            f = mod::Price::discounted
            g = x.mod::Price::discounted(10)
            f
        "});
        let refused: Vec<(&str, &str)> = refused
            .iter()
            .map(|(s, m)| (s.as_str(), m.as_str()))
            .collect();
        assert_eq!(
            refused,
            [(
                "mod::Price::discounted",
                "the method reference `mod::Price::discounted` is not supported yet"
            )]
        );
    }

    /// A variable of another module is a write target, of `+=` and of `:=`
    /// inside a transaction (`docs/chl-spec.md`, "9.6 Qualified references").
    #[test]
    fn a_qualified_write_target_is_refused() {
        assert_eq!(
            refused_spans(indoc! {"
                c::count += 1
                with begin():
                    inv::stock := inv::stock
                1
            "}),
            ["c::count", "inv::stock"]
        );
    }

    /// A loaded declaration's `pub` is refused at the keyword, on the line
    /// below the decorator.
    #[test]
    fn pub_on_a_loaded_declaration_is_refused_at_its_keyword() {
        assert_eq!(
            refused_spans(indoc! {"
                @LoadFrom(qty)
                pub held: Int
                held
            "}),
            ["pub"]
        );
    }

    #[test]
    fn a_renamed_run_is_refused_at_its_decorator() {
        let refused = refusals(indoc! {"
            @RenamedFrom(eu)
            run storefront as eu_west
        "});
        assert_eq!(refused.len(), 1, "{refused:#?}");
        assert_eq!(refused[0].0, "eu");
        assert_eq!(refused[0].1, "`@RenamedFrom` is not supported yet");
    }

    /// A module statement in a nested body is refused as out of place, not as
    /// unsupported, and the statement is not checked further.
    #[test]
    fn a_module_statement_stands_only_at_the_top_level() {
        let refused = refusals(indoc! {"
            def f():
                import shop
                run audit(log=x::y)
                param port: String
                pub limit = 10
                limit
            if ready:
                import cart
            for x in xs:
                @Discard
                run audit as old
                @Discard
                stock
            1
        "});
        let refused: Vec<(&str, &str)> = refused
            .iter()
            .map(|(s, m)| (s.as_str(), m.as_str()))
            .collect();
        assert_eq!(
            refused,
            [
                (
                    "import shop",
                    "`import` stands only at a module's top level"
                ),
                (
                    "run audit(log=x::y)",
                    "`run` stands only at a module's top level"
                ),
                (
                    "param port: String",
                    "`param` stands only at a module's top level"
                ),
                ("pub", "`pub` stands only at a module's top level"),
                (
                    "import cart",
                    "`import` stands only at a module's top level"
                ),
                (
                    "@Discard\n    run audit as old\n",
                    "`@Discard run` stands only at a module's top level"
                ),
                ("@Discard\n    stock\n", "`@Discard` is not supported yet"),
            ]
        );
    }

    /// A run's arguments are expressions of the module that runs it, checked as
    /// any other.
    #[test]
    fn a_run_argument_is_checked() {
        assert_eq!(
            refused_spans("run storefront(audit=x.mod::Price::discounted)\n"),
            ["mod::Price::discounted"]
        );
    }
}
