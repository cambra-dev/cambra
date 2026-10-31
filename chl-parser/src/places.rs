//! Places: where each feed and each named call is written, in terms two versions of a module
//! agree on (`src/ccl/design/sites.md`).
//!
//! A [`Place`] names the module, the bindings the author wrote around the node, what the node
//! is and its spelling, and its index among the places sharing all of those, counted in source
//! order. Nothing counts places across the module, so an edit moves only the places that share
//! its bindings, kind and spelling and follow it.
//!
//! [`places`] is the one numbering: the compiler's lowering and the reference interpreter both
//! look a node's place up in it by the node's span.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use smol_str::SmolStr;

use crate::ast::{
    AssignTarget, CompClause, Expr, KindAnnotation, Param, Requirement, Span, Spanned, Stmt,
    TraitItem, TraitType, TypeAnnotation, TypeDeclBody, TypeParam, VariantPayload,
};

/// What a place is the place of.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PlaceKind {
    /// A feed, `target << value`, spelled by its target.
    Feed,
    /// A `yield`, spelled `yield`.
    Yield,
    /// A call, spelled by the callee's name: `f(x)`, `m::f(x)`, `x.f()`.
    Call,
}

/// Where a feed or a named call is written.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Place {
    /// The module's path, empty for the root.
    pub module: Arc<[SmolStr]>,
    /// The author-written bindings whose definitions enclose it, outermost first.
    pub bindings: Arc<[SmolStr]>,
    pub kind: PlaceKind,
    pub spelling: SmolStr,
    pub index: u32,
}

/// `module::binding.binding.spelling<<#index`, with `()` in place of `<<` for a call, nothing
/// for a `yield`, and no `#index` for the first.
impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for segment in self.module.iter() {
            write!(f, "{segment}::")?;
        }
        for binding in self.bindings.iter() {
            write!(f, "{binding}.")?;
        }
        match self.kind {
            PlaceKind::Feed => write!(f, "{}<<", self.spelling)?,
            PlaceKind::Yield => write!(f, "{}", self.spelling)?,
            PlaceKind::Call => write!(f, "{}()", self.spelling)?,
        }
        if self.index > 0 {
            write!(f, "#{}", self.index)?;
        }
        Ok(())
    }
}

/// The tag a channel's arm for a site carries: the run's path, then each call that reached the
/// place, outermost first, then the place, joined by `/`. A label's `::` names its module, so
/// each `::` is spelled `.`.
pub fn site_tag<'a>(
    run: &str,
    calls: impl IntoIterator<Item = &'a Place>,
    place: &Place,
) -> String {
    let mut tag = String::new();
    if !run.is_empty() {
        tag.push_str(run);
        tag.push('/');
    }
    for call in calls {
        tag.push_str(&format!("{call}/"));
    }
    tag.push_str(&place.to_string());
    tag.replace("::", ".")
}

/// The place of each feed, `yield` and named call in the module at `module` whose body is
/// `body`, by span: a feed's target's, a `yield`'s own, a call's callee's, a method call's
/// method name's, and a field callee's field name's, `f` in `(r.f)(x)`.
///
/// The bindings that enclose a place are the names an assignment to a name binds (`x = …`,
/// `x: T = …`, `x := …`, `x <<= …`) and each `def`'s name, under its owner type's name or its
/// `impl` block's head name where it has one.
pub fn places(module: &[SmolStr], body: &[Spanned<Stmt>]) -> HashMap<Span, Place> {
    let mut walk = Walk {
        module: Arc::from(module),
        bindings: Vec::new(),
        counts: HashMap::new(),
        places: HashMap::new(),
    };
    walk.stmts(body);
    walk.places
}

struct Walk {
    module: Arc<[SmolStr]>,
    bindings: Vec<SmolStr>,
    counts: HashMap<(Vec<SmolStr>, PlaceKind, SmolStr), u32>,
    places: HashMap<Span, Place>,
}

impl Walk {
    fn place(&mut self, at: Span, kind: PlaceKind, spelling: SmolStr) {
        let index = self
            .counts
            .entry((self.bindings.clone(), kind, spelling.clone()))
            .or_insert(0);
        let place = Place {
            module: self.module.clone(),
            bindings: self.bindings.clone().into(),
            kind,
            spelling,
            index: *index,
        };
        *index += 1;
        let earlier = self.places.insert(at, place);
        assert!(earlier.is_none(), "two places share the span {at:?}");
    }

    fn within(&mut self, names: &[&SmolStr], f: impl FnOnce(&mut Self)) {
        let depth = self.bindings.len();
        self.bindings.extend(names.iter().map(|n| (*n).clone()));
        f(self);
        self.bindings.truncate(depth);
    }

    /// `f` under the binding `target` names, when it is a single name.
    fn within_target(&mut self, target: &Spanned<AssignTarget>, f: impl FnOnce(&mut Self)) {
        match &target.node {
            AssignTarget::Name(n) => self.within(&[n], f),
            _ => f(self),
        }
    }

    fn stmts(&mut self, body: &[Spanned<Stmt>]) {
        body.iter().for_each(|s| self.stmt(s));
    }

    fn stmt(&mut self, stmt: &Spanned<Stmt>) {
        match &stmt.node {
            Stmt::Expr(e) | Stmt::Return(Some(e)) => self.expr(e),
            Stmt::Assign { target, value, .. } | Stmt::Define { target, value } => {
                self.target(target);
                self.within_target(target, |w| w.expr(value));
            }
            Stmt::AnnAssign {
                target,
                annotation,
                value,
            } => {
                self.target(target);
                self.annotation(annotation);
                self.within_target(target, |w| w.expr(value));
            }
            Stmt::MutAssign {
                target,
                annotation,
                value,
            } => {
                self.target(target);
                if let Some(a) = annotation {
                    self.annotation(a);
                }
                self.within_target(target, |w| w.expr(value));
            }
            Stmt::AugAssign { target, value, .. } => {
                self.target(target);
                self.expr(value);
            }
            Stmt::Declare { target, annotation }
            | Stmt::LoadFrom {
                target, annotation, ..
            } => {
                self.target(target);
                self.annotation(annotation);
            }
            Stmt::If {
                branches,
                else_body,
            } => {
                for b in branches {
                    self.expr(&b.cond);
                    self.stmts(&b.body);
                }
                if let Some(body) = else_body {
                    self.stmts(body);
                }
            }
            Stmt::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                arms.iter().for_each(|a| self.stmts(&a.body));
            }
            Stmt::For { target, iter, body } => {
                self.target(target);
                self.expr(iter);
                self.stmts(body);
            }
            Stmt::FunctionDef {
                owner,
                name,
                type_params,
                params,
                output,
                requires,
                causes,
                body,
            } => {
                let names: Vec<&SmolStr> = owner.iter().chain([name]).map(|n| &n.node).collect();
                self.within(&names, |w| {
                    w.signature(type_params, params, output.as_ref(), &requires.items);
                    w.trait_types(&causes.items);
                    w.stmts(body);
                });
            }
            Stmt::TypeDecl(decl) => match &decl.body {
                TypeDeclBody::Constructors(ctors) => ctors
                    .iter()
                    .flat_map(|c| &c.params)
                    .for_each(|p| self.expr(&p.ty)),
                TypeDeclBody::Single(e) => self.expr(e),
            },
            Stmt::Impl(block) => {
                block.args.iter().for_each(|a| self.expr(a));
                block.assoc.iter().for_each(|a| self.expr(&a.value));
                self.requirements(&block.requires);
                self.within(&[&block.ty.node], |w| w.stmts(&block.defs));
            }
            Stmt::TraitDecl(decl) => {
                self.requirements(&decl.requires);
                for item in &decl.items {
                    match item {
                        TraitItem::AssocType { bound, .. } => {
                            if let Some(b) = bound {
                                self.expr(b);
                            }
                        }
                        TraitItem::Function(sig) => self.within(&[&sig.node.name.node], |w| {
                            w.signature(
                                &sig.node.type_params,
                                &sig.node.params,
                                sig.node.output.as_ref(),
                                &sig.node.requires,
                            )
                        }),
                    }
                }
            }
            Stmt::With { context, body, .. } => {
                self.expr(context);
                self.stmts(body);
            }
            Stmt::Import { args, .. } | Stmt::Run { args, .. } => {
                args.iter().for_each(|a| self.expr(&a.value));
            }
            Stmt::Param {
                annotation,
                default,
                ..
            } => {
                if let Some(a) = annotation {
                    self.annotation(a);
                }
                if let Some(d) = default {
                    self.expr(d);
                }
            }
            Stmt::Pub { stmt, .. } => self.stmt(stmt),
            Stmt::Return(None) | Stmt::Discard(_) | Stmt::Pass | Stmt::Error => {}
        }
    }

    fn target(&mut self, target: &Spanned<AssignTarget>) {
        match &target.node {
            AssignTarget::Tuple(parts) => parts.iter().for_each(|p| self.target(p)),
            AssignTarget::Subscript { target, index } => {
                self.expr(target);
                self.expr(index);
            }
            AssignTarget::Name(_) | AssignTarget::Qualified(_) | AssignTarget::Constructor(_) => {}
        }
    }

    fn annotation(&mut self, annotation: &TypeAnnotation) {
        self.expr(&annotation.ty);
    }

    fn signature(
        &mut self,
        type_params: &[TypeParam],
        params: &[Param],
        output: Option<&Spanned<Expr>>,
        requires: &[Spanned<Requirement>],
    ) {
        self.type_params(type_params);
        self.params(params);
        if let Some(o) = output {
            self.expr(o);
        }
        self.requirements(requires);
    }

    fn type_params(&mut self, type_params: &[TypeParam]) {
        for p in type_params {
            match &p.annotation {
                Some(KindAnnotation::Kind(e) | KindAnnotation::Bound(e)) => self.expr(e),
                None => {}
            }
        }
    }

    fn params(&mut self, params: &[Param]) {
        params
            .iter()
            .filter_map(|p| p.annotation.as_ref())
            .for_each(|a| self.annotation(a));
    }

    fn trait_types(&mut self, types: &[Spanned<TraitType>]) {
        types
            .iter()
            .for_each(|t| t.node.args.iter().for_each(|a| self.expr(a)));
    }

    fn requirements(&mut self, requires: &[Spanned<Requirement>]) {
        for r in requires {
            match &r.node {
                Requirement::Trait { ty, .. } => ty.args.iter().for_each(|a| self.expr(a)),
                Requirement::Bound { bound, .. } => self.expr(bound),
            }
        }
    }

    fn expr(&mut self, e: &Spanned<Expr>) {
        match &e.node {
            Expr::Call { func, args } => {
                match &func.node {
                    Expr::Name(n) => self.place(func.span, PlaceKind::Call, n.clone()),
                    Expr::Qualified(q) => {
                        self.place(func.span, PlaceKind::Call, qualified(&q.qualifier, &q.name))
                    }
                    // `(r.f)(x)` calls the function a field holds, spelled by the field.
                    Expr::Attribute {
                        target,
                        attr,
                        attr_span,
                        ..
                    } => {
                        self.expr(target);
                        self.place(*attr_span, PlaceKind::Call, attr.clone());
                    }
                    _ => self.expr(func),
                }
                args.iter().for_each(|a| self.expr(a));
            }
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                self.expr(receiver);
                self.place(method.span, PlaceKind::Call, method.node.clone());
                args.iter().for_each(|a| self.expr(a));
            }
            Expr::Feed { target, value } => {
                let spelling = match &target.node {
                    Expr::Name(n) => Some(n.clone()),
                    Expr::Qualified(q) => Some(qualified(&q.qualifier, &q.name)),
                    _ => None,
                };
                match spelling {
                    Some(s) => self.place(target.span, PlaceKind::Feed, s),
                    // A target that is no name is refused where it is lowered.
                    None => self.expr(target),
                }
                self.expr(value);
            }
            Expr::Yield(inner) => {
                self.place(e.span, PlaceKind::Yield, SmolStr::new_static("yield"));
                self.expr(inner);
            }
            Expr::Lit(_)
            | Expr::Name(_)
            | Expr::Qualified(_)
            | Expr::Summon { .. }
            | Expr::Error => {}
            Expr::BinOp { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::UnaryOp { operand, .. } => self.expr(operand),
            Expr::BoolOp { operands, .. } => operands.iter().for_each(|o| self.expr(o)),
            Expr::Compare {
                left, comparators, ..
            } => {
                self.expr(left);
                comparators.iter().for_each(|c| self.expr(c));
            }
            Expr::List(items) | Expr::Tuple(items) | Expr::BraceGroup(items) => {
                items.iter().for_each(|i| self.expr(i))
            }
            Expr::Record(fields) | Expr::BraceRecord(fields) => {
                fields.iter().for_each(|f| self.expr(&f.value))
            }
            Expr::ModuleType(entries) => entries.iter().for_each(|en| self.expr(&en.value)),
            Expr::BraceRefinement { base, predicate } => {
                self.expr(base);
                self.expr(predicate);
            }
            Expr::FunctionType {
                domain,
                codomain,
                requires,
                causes,
                ..
            } => {
                self.expr(domain);
                self.expr(codomain);
                self.requirements(&requires.items);
                self.trait_types(&causes.items);
            }
            Expr::Subscript { target, index, .. } => {
                self.expr(target);
                self.expr(index);
            }
            Expr::Attribute { target, .. } => self.expr(target),
            Expr::VariantCtor { payload, .. } => match payload {
                Some(VariantPayload::Term(p) | VariantPayload::Fields(p)) => self.expr(p),
                None => {}
            },
            Expr::Lambda { params, body } => {
                self.params(params);
                self.expr(body);
            }
            Expr::Forall {
                type_params,
                body,
                requires,
            } => {
                self.type_params(type_params);
                self.expr(body);
                self.requirements(requires);
            }
            Expr::IfExp {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr(cond);
                self.expr(then_expr);
                self.expr(else_expr);
            }
            Expr::ListComp(comp) | Expr::GenExp(comp) => {
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
            Expr::Block(stmt) => self.stmt(stmt),
        }
    }
}

/// `a::b::name`.
fn qualified(qualifier: &[Spanned<SmolStr>], name: &Spanned<SmolStr>) -> SmolStr {
    let mut s = String::new();
    for q in qualifier {
        s.push_str(&q.node);
        s.push_str("::");
    }
    s.push_str(&name.node);
    SmolStr::new(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;

    /// Each place of `source`'s root module, in source order, as its display.
    fn spelled(source: &str) -> Vec<String> {
        let module = crate::parse_module(FileId::ROOT, source)
            .into_result()
            .expect("parses");
        let mut places: Vec<(Span, Place)> = places(&[], &module.body).into_iter().collect();
        places.sort_by_key(|(span, _)| span.start);
        places.into_iter().map(|(_, p)| p.to_string()).collect()
    }

    #[test]
    fn places_count_in_source_order_within_their_bindings() {
        let source = indoc::indoc! {r#"
            out = test_sink()
            def f(y):
                out << y
                out << y + 1
            f(1)
            f(2)
            x = f(3)
        "#};
        assert_eq!(
            spelled(source),
            [
                "out.test_sink()",
                "f.out<<",
                "f.out<<#1",
                "f()",
                "f()#1",
                "x.f()",
            ]
        );
    }

    #[test]
    fn a_new_place_moves_no_place_of_another_binding_or_spelling() {
        let before = spelled("a = f(1)\nb = f(2)\n");
        let after = spelled("a = f(0) + f(1) + g(2)\nb = f(2)\n");
        assert_eq!(before, ["a.f()", "b.f()"]);
        assert_eq!(after, ["a.f()", "a.f()#1", "a.g()", "b.f()"]);
    }

    #[test]
    fn a_site_tag_spells_its_module_path_with_dots() {
        let place = |module: &[&str], spelling: &str, kind| Place {
            module: module.iter().map(SmolStr::new).collect::<Vec<_>>().into(),
            bindings: Arc::from([]),
            kind,
            spelling: SmolStr::new(spelling),
            index: 0,
        };
        let call = place(&[], "m::f", PlaceKind::Call);
        let feed = place(&["m"], "out", PlaceKind::Feed);
        assert_eq!(site_tag("", [&call], &feed), "m.f()/m.out<<");
    }
}
