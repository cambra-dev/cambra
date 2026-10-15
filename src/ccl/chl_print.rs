//! Types written in CHL, for a reader of the language rather than of the checker
//! (`src/ccl/design/diagnostics.md`, "How a diagnostic writes a type").
//!
//! [`Display for Type`](crate::ccl::Type) writes the checker's own notation: `⤇` for a
//! collection, a `Σ` for a sum, `Int@1` for a singleton, a refinement predicate as a
//! CCL term. [`chl_type`] writes the same type the way CHL writes types. A collection is
//! one of the collection types of `docs/chl-spec.md`, "6.3 Direction: collection types
//! \[Decided\]", over its domain; a sum over named alternatives is a `Box`; a predicate is
//! the CHL expression that lowers to it.
//!
//! Some of what it writes has no annotation syntax: a `Box`, a source's rows, a
//! dependent `FullMap(k: …, …)`, an index range written as `{UInt where _ < n}`. What the
//! notation has no form for at all is written in the checker's notation between `‹…›`,
//! never dropped.

use std::collections::HashSet;
use std::fmt;

use crate::ccl::infer::solver::display::InferredPoly;
use crate::ccl::ty::{FunKind, PolyType, TypeKind, TypeParamId};
use crate::ccl::{BaseType, BinOpKind, Builtin, Expr, HistoryKind, Lit, Name, Type, TypedExprNode};
use crate::ccl::{FieldKey, UnaryOpKind};

/// `ty` written in CHL.
pub fn chl_type(ty: &Type) -> String {
    Printer::for_type(ty).ty(ty)
}

/// An inferred polymorphic type written in CHL: its `Poly`, or its body alone when it
/// has no parameters, with each join or meet the notation cannot write written as its
/// operands, `A ∨ Int`.
pub fn chl_inferred_poly(inferred: &InferredPoly) -> String {
    let mut p = Printer {
        joins: inferred.join_texts(chl_type),
        ..Printer::for_type(&Type::Poly(std::rc::Rc::new(inferred.poly.clone())))
    };
    if inferred.poly.params.is_empty() {
        p.ty(&inferred.poly.body)
    } else {
        p.poly(&inferred.poly)
    }
}

#[derive(Default)]
struct Printer {
    /// The functions the walk has descended into the codomain of, innermost last: the
    /// spelling of each one's binder, or `None` for one that names none. A reference
    /// `index` crossings out reads entry `len - 1 - index`, as
    /// `symbolic::PiBinderEnv` does.
    binders: Vec<Option<String>>,
    /// Every binder the printed text introduces and is inside of, innermost last, with
    /// the spelling it is written with. A reference by name reads its spelling here.
    spelled: Vec<(Name, String)>,
    /// Every spelling a name in the printed type has, so a binder the compiler minted is
    /// given one that no other name in the text reads as.
    taken: HashSet<String>,
    /// The text of each parameter that stands for a join or meet
    /// ([`chl_inferred_poly`]).
    joins: Vec<(TypeParamId, String)>,
}

/// Binding tightness of a CHL expression, loosest first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Lowest,
    Or,
    And,
    Not,
    Cmp,
    Xor,
    Add,
    Mul,
    Pow,
    Unary,
    Postfix,
    Atom,
}

/// A name bound to the expression it stands for while a lambda's body is written, and the
/// depth of the environment that expression is written in.
type Env<'a> = Vec<(&'a Name, &'a Expr, usize)>;

impl Printer {
    /// A printer for `ty`, holding the spellings its names have.
    fn for_type(ty: &Type) -> Printer {
        let mut taken = HashSet::new();
        type_spellings(ty, &mut taken);
        Printer {
            taken,
            ..Printer::default()
        }
    }

    /// The spelling a binder the printed text introduces is written with: its own, or,
    /// for one the compiler minted, `preferred` or `preferred` numbered, whichever no
    /// other name in the type or binder in scope reads as.
    fn binder(&self, name: &Name, preferred: &str) -> String {
        if let Some(own) = spelling(name) {
            return own;
        }
        let free = |candidate: &String| {
            !self.taken.contains(candidate)
                && !self.spelled.iter().any(|(_, s)| s == candidate)
                && !self.binders.iter().flatten().any(|s| s == candidate)
        };
        std::iter::once(preferred.to_string())
            .chain((1..).map(|i| format!("{preferred}{i}")))
            .find(free)
            .expect("an unbounded sequence of spellings has one not taken")
    }

    /// Write `ty` in the checker's notation between `‹…›`: a form CHL has no spelling for.
    fn fallback(&mut self, ty: &Type) -> String {
        format!("‹{ty}›")
    }

    /// `forall (T, U <: B) V requires …`.
    fn poly(&mut self, poly: &PolyType) -> String {
        let params: Vec<String> = poly
            .params
            .iter()
            .map(|p| match p.bound() {
                Some(bound) => format!("{} <: {}", p.param.spelling, self.ty(bound)),
                None => p.param.spelling.to_string(),
            })
            .collect();
        let body = self.ty(&poly.body);
        let requires: Vec<String> = poly
            .requires
            .iter()
            .map(|r| {
                let mut args: Vec<String> = r.args.iter().map(|t| self.ty(t)).collect();
                args.extend(r.assoc.iter().map(|(n, t)| format!("{n}={}", self.ty(t))));
                format!("{}({})", r.trait_, args.join(", "))
            })
            .collect();
        let mut text = format!("forall ({}) {body}", params.join(", "));
        if !requires.is_empty() {
            text.push_str(" requires ");
            text.push_str(&requires.join(", "));
        }
        text
    }

    fn ty(&mut self, ty: &Type) -> String {
        match ty {
            Type::Base(BaseType::Unit) => "{}".to_string(),
            Type::Base(b) => b.keyword().to_string(),
            Type::UIntRange(n) => format!("{{UInt where _ < {n}}}"),
            Type::DataSource(name) => format!("Source({name})"),
            Type::Txn => "Txn".to_string(),
            Type::Hole => "_".to_string(),
            // A variable has an identity `_` would drop: two occurrences are one type.
            Type::SharedHole(_) | Type::Infer(_) => self.fallback(ty),
            Type::Param(p) => match self.joins.iter().find(|(id, _)| *id == p.id) {
                Some((_, text)) => text.clone(),
                None => p.spelling.to_string(),
            },
            Type::Tuple(ts) => match ts.as_slice() {
                [] => "{}".to_string(),
                [only] => format!("{{{},}}", self.ty(only)),
                _ => {
                    let parts: Vec<String> = ts.iter().map(|t| self.ty(t)).collect();
                    format!("{{{}}}", parts.join(", "))
                }
            },
            Type::Record(fields) => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", self.ty(t)))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            Type::Variant(..) if ty.option_payload().is_some() => {
                let payload = ty.option_payload().expect("matched above");
                format!("Option({})", self.ty(payload))
            }
            Type::Variant(tags, openness) => {
                let named = tags.iter().all(|(k, _)| matches!(k, FieldKey::Name(_)));
                if !named || openness.permits_extra_tags() {
                    return self.fallback(ty);
                }
                let arms: Vec<(String, Option<String>)> = tags
                    .iter()
                    .map(|(k, t)| {
                        let payload = match t {
                            Type::Base(BaseType::Unit) => None,
                            _ => Some(self.ty(t)),
                        };
                        (k.to_string(), payload)
                    })
                    .collect();
                VariantArms(arms).to_string()
            }
            Type::Refinement(base, refinements) => {
                let mut preds: Vec<String> = refinements
                    .iter()
                    .map(|r| self.expr(&r.predicate, Prec::And, &Vec::new()))
                    .collect();
                preds.sort();
                match base.as_ref() {
                    // An index range is the bound on its `UInt`, so a range refined further
                    // is one refinement of `UInt`.
                    Type::UIntRange(n) => {
                        preds.insert(0, format!("_ < {n}"));
                        format!("{{UInt where {}}}", preds.join(" and "))
                    }
                    // Each refinement of the set is its own `where`: a set of two lowers
                    // from two nested refinements, and `p and q` would be one refinement,
                    // which the checker does not equate with the two.
                    _ => preds
                        .iter()
                        .fold(self.ty(base), |inner, p| format!("{{{inner} where {p}}}")),
                }
            }
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            } => self.fun(ty, name.as_ref(), fun_kind, domain, codomain),
            Type::History {
                value,
                domain,
                history_kind: HistoryKind::Overwrite,
            } => {
                format!("Mut({}, {})", self.ty(value), self.ty(domain))
            }
            Type::History { value, .. } => {
                format!("Feed({})", self.ty(value))
            }
            Type::Poly(poly) => self.poly(poly),
            Type::ChanDom(..) | Type::WitnessRef(_) | Type::BoundedHole(_) => self.fallback(ty),
        }
    }

    /// A function: a collection over its domain when its kind is data, a `=>` otherwise.
    fn fun(
        &mut self,
        ty: &Type,
        name: Option<&Name>,
        fun_kind: &FunKind,
        domain: &Type,
        codomain: &Type,
    ) -> String {
        let witnesses = fun_kind.witnesses();
        if !witnesses.is_empty() {
            return self.sum(ty, witnesses, domain, codomain);
        }
        // A function whose codomain names its binder: CHL writes the binder only in a
        // `def`'s signature, so a type spells it as the key of a `FullMap` or the
        // parameter of a function.
        let dependent = name.filter(|n| crate::ccl::subst::codomain_depends_on(n, codomain));
        // The domain is written only where the form shows it: `Array` and `Source` name
        // theirs by a length and a source.
        let shown_domain = !(fun_kind.resolved().is_data()
            && dependent.is_none()
            && matches!(domain, Type::UIntRange(_) | Type::DataSource(_)));
        let dom = if shown_domain {
            self.ty(domain)
        } else {
            String::new()
        };
        let is_data = fun_kind.resolved().is_data();
        let binder = name.map(|n| (n, self.binder(n, if is_data { "k" } else { "x" })));
        self.binders.push(binder.as_ref().map(|(_, s)| s.clone()));
        if let Some((n, s)) = &binder {
            self.spelled.push(((*n).clone(), s.clone()));
        }
        let cod = self.ty(codomain);
        if binder.is_some() {
            self.spelled.pop();
        }
        self.binders.pop();
        let binder = binder.map(|(_, s)| s).unwrap_or_default();
        if is_data {
            match (dependent, domain) {
                (Some(_), _) => format!("FullMap({binder}: {dom}, {cod})"),
                (None, Type::UIntRange(n)) => format!("Array({n}, {cod})"),
                (None, Type::DataSource(source)) => format!("Source({source}, {cod})"),
                (None, _) => format!("FullMap({dom}, {cod})"),
            }
        } else {
            let dom = match domain {
                Type::Fun { .. } => format!("({dom})"),
                _ => dom,
            };
            match dependent {
                Some(_) => format!("({binder}: {dom}) => {cod}"),
                None => format!("{dom} => {cod}"),
            }
        }
    }

    /// A sum: the collection type its witness's kind names, or the `Box` of the
    /// alternatives it enumerates.
    fn sum(
        &mut self,
        ty: &Type,
        witnesses: &[crate::ccl::ty::Witness],
        domain: &Type,
        codomain: &Type,
    ) -> String {
        let [w] = witnesses else {
            return self.fallback(ty);
        };
        if !matches!(domain, Type::WitnessRef(id) if id == w.id())
            || crate::ccl::ty::has_free_witness_ref(codomain, &[])
        {
            return self.fallback(ty);
        }
        self.binders.push(None);
        let cod = self.ty(codomain);
        self.binders.pop();
        match w.type_kind() {
            TypeKind::UIntRanges => format!("List({cod})"),
            TypeKind::SubtypesOf(key) => {
                let key = self.ty(&key);
                match codomain {
                    Type::Base(BaseType::Unit) => format!("Set({key})"),
                    _ => format!("Map({key}, {cod})"),
                }
            }
            TypeKind::Type => format!("Collection({cod})"),
            TypeKind::Enumerated(candidates) => {
                let alternatives: Vec<String> = candidates
                    .iter()
                    .map(|candidate| {
                        let alternative = Type::data_fun(candidate.clone(), codomain.clone());
                        self.ty(&alternative)
                    })
                    .collect();
                format!("Box({})", alternatives.join(" | "))
            }
        }
    }

    /// A refinement predicate, at least as tight as `min`.
    fn expr<'a>(&mut self, e: &'a Expr, min: Prec, env: &Env<'a>) -> String {
        let (prec, text) = self.expr_inner(e, env);
        if prec < min {
            format!("({text})")
        } else {
            text
        }
    }

    fn expr_inner<'a>(&mut self, e: &'a Expr, env: &Env<'a>) -> (Prec, String) {
        match &e.node {
            TypedExprNode::Lit(lit) => (Prec::Atom, lit_text(lit)),
            TypedExprNode::Var(name) if name.is_elem() => (Prec::Atom, "_".to_string()),
            TypedExprNode::Var(name) => {
                if let Some((_, bound, depth)) = env.iter().rev().find(|(n, _, _)| *n == name) {
                    let outer: Env<'a> = env[..*depth].to_vec();
                    return self.expr_inner(bound, &outer);
                }
                if let Some((_, s)) = self.spelled.iter().rev().find(|(n, _)| n == name) {
                    return (Prec::Atom, s.clone());
                }
                if let Some(index) = name.pi_bound_index() {
                    let spelling = (self.binders.len() as u32)
                        .checked_sub(index + 1)
                        .and_then(|i| self.binders[i as usize].clone());
                    return match spelling {
                        Some(s) => (Prec::Atom, s),
                        None => (Prec::Atom, self.fallback_expr(e)),
                    };
                }
                match spelling(name) {
                    Some(s) => (Prec::Atom, s),
                    None => (Prec::Atom, self.fallback_expr(e)),
                }
            }
            TypedExprNode::BinOp { left, op, right } => {
                let Some((own, l, r)) = binop_prec(op) else {
                    return (Prec::Atom, self.fallback_expr(e));
                };
                let l = self.expr(left, l, env);
                let r = self.expr(right, r, env);
                (own, format!("{l} {} {r}", binop_text(op)))
            }
            TypedExprNode::UnaryOp(UnaryOpKind::Neg, operand) => (
                Prec::Unary,
                format!("-{}", self.expr(operand, Prec::Unary, env)),
            ),
            TypedExprNode::UnaryOp(UnaryOpKind::Not, operand) => (
                Prec::Not,
                format!("not {}", self.expr(operand, Prec::Not, env)),
            ),
            TypedExprNode::List(elts) => {
                let parts: Vec<String> = elts
                    .iter()
                    .map(|x| self.expr(x, Prec::Lowest, env))
                    .collect();
                (Prec::Atom, format!("[{}]", parts.join(", ")))
            }
            TypedExprNode::Tuple(elts) => {
                let parts: Vec<String> = elts
                    .iter()
                    .map(|x| self.expr(x, Prec::Lowest, env))
                    .collect();
                (Prec::Atom, format!("({})", parts.join(", ")))
            }
            TypedExprNode::Record(fields) => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(k, x)| format!("{k}={}", self.expr(x, Prec::Lowest, env)))
                    .collect();
                (Prec::Atom, format!("({})", parts.join(", ")))
            }
            TypedExprNode::Compose(stages) => match self.comprehension(stages, env) {
                Some(text) => (Prec::Atom, text),
                None => (Prec::Atom, self.fallback_expr(e)),
            },
            TypedExprNode::Apply { function, argument } => self.apply(e, function, argument, env),
            _ => (Prec::Atom, self.fallback_expr(e)),
        }
    }

    /// `argument ▷ function`: a field read, a lambda's body at the argument, a
    /// membership test, an index into a collection, or a call. The last two differ
    /// only in the function's kind, so a function whose type does not say which is
    /// written in the checker's notation.
    ///
    /// Only a field read of a name is what lowering builds from the text written here;
    /// each other form is the CHL a reader would write for the term, which lowers to a
    /// different term, so the type it sits in is not an annotation.
    fn apply<'a>(
        &mut self,
        apply: &'a Expr,
        function: &'a Expr,
        argument: &'a Expr,
        env: &Env<'a>,
    ) -> (Prec, String) {
        match &function.node {
            TypedExprNode::Proj(key) => {
                // A field of a literal product is that field.
                if let Some(field) = project(resolve(argument, env), key) {
                    let (field, depth) = field;
                    let outer: Env<'a> = env[..depth].to_vec();
                    return self.expr_inner(field, &outer);
                }
                let target = self.expr(argument, Prec::Postfix, env);
                (Prec::Postfix, format!("{target}.{key}"))
            }
            TypedExprNode::Lambda { param, body } => {
                let mut inner = env.clone();
                inner.push((&param.name, argument, env.len()));
                self.expr_inner(body, &inner)
            }
            TypedExprNode::Apply {
                function: contains,
                argument: collection,
            } if matches!(
                contains.node,
                TypedExprNode::Builtin(Builtin::CollectionContains)
            ) =>
            {
                let member = self.expr(argument, Prec::Cmp.next(), env);
                let collection = self.expr(collection, Prec::Cmp.next(), env);
                (Prec::Cmp, format!("{member} in {collection}"))
            }
            _ => match function.ty.peel_refinements() {
                Type::Fun { fun_kind, .. } => {
                    let target = self.expr(function, Prec::Postfix, env);
                    let arg = self.expr(argument, Prec::Lowest, env);
                    let text = if fun_kind.resolved().is_data() {
                        format!("{target}[{arg}]")
                    } else {
                        format!("{target}({arg})")
                    };
                    (Prec::Postfix, text)
                }
                _ => (Prec::Atom, self.fallback_expr(apply)),
            },
        }
    }

    /// `c ≫ λ x → b` as the comprehension `[b for x in c]`, or, over a list literal,
    /// the list of `b` at each element.
    fn comprehension<'a>(&mut self, stages: &'a [Expr], env: &Env<'a>) -> Option<String> {
        let [source, stage] = stages else {
            return None;
        };
        let TypedExprNode::Lambda { param, body } = &stage.node else {
            return None;
        };
        if let (TypedExprNode::List(elts), depth) = resolve(source, env) {
            let parts: Vec<String> = elts
                .iter()
                .map(|elt| {
                    let mut inner: Env<'a> = env.clone();
                    inner.push((&param.name, elt, depth));
                    self.expr(body, Prec::Lowest, &inner)
                })
                .collect();
            return Some(format!("[{}]", parts.join(", ")));
        }
        let source = self.expr(source, Prec::Lowest, env);
        let mut inner = env.clone();
        // The comprehension binds the parameter itself, so it reads as its spelling.
        inner.retain(|(n, _, _)| *n != &param.name);
        let x = self.binder(&param.name, "x");
        self.spelled.push((param.name.clone(), x.clone()));
        let body = self.expr(body, Prec::Lowest, &inner);
        self.spelled.pop();
        Some(format!("[{body} for {x} in {source}]"))
    }

    /// A predicate term CHL has no spelling for, in the checker's notation.
    fn fallback_expr(&mut self, e: &Expr) -> String {
        format!("‹{}›", crate::ccl::symbolic::symbolic(e))
    }
}

impl Prec {
    fn next(self) -> Prec {
        match self {
            Prec::Lowest => Prec::Or,
            Prec::Or => Prec::And,
            Prec::And => Prec::Not,
            Prec::Not => Prec::Cmp,
            Prec::Cmp => Prec::Xor,
            Prec::Xor => Prec::Add,
            Prec::Add => Prec::Mul,
            Prec::Mul => Prec::Pow,
            Prec::Pow => Prec::Unary,
            Prec::Unary => Prec::Postfix,
            Prec::Postfix | Prec::Atom => Prec::Atom,
        }
    }
}

/// An operator's own level and the levels its left and right operands are written at:
/// left-grouping, except `**`, which groups right and binds a negated base tighter
/// (`docs/chl-spec.md`, "2.3 Expression precedence"). `None` for an operator CHL has no
/// spelling for.
fn binop_prec(op: &BinOpKind) -> Option<(Prec, Prec, Prec)> {
    use crate::ccl::{ArithmeticKind as A, LogicKind as L};
    let leftward = |own: Prec| Some((own, own, own.next()));
    match op {
        BinOpKind::BoolLogic(L::Or) => leftward(Prec::Or),
        BinOpKind::BoolLogic(L::And) => leftward(Prec::And),
        BinOpKind::BoolLogic(L::Xor) => leftward(Prec::Xor),
        BinOpKind::BoolLogic(L::Nand | L::Nor | L::Xnor) => None,
        BinOpKind::Compare(_) => Some((Prec::Cmp, Prec::Cmp.next(), Prec::Cmp.next())),
        BinOpKind::Arithmetic(A::Add | A::AddRefined | A::Sub) | BinOpKind::Concat => {
            leftward(Prec::Add)
        }
        BinOpKind::Arithmetic(A::Mul | A::FloorDiv) => leftward(Prec::Mul),
        BinOpKind::Arithmetic(A::Pow) => Some((Prec::Pow, Prec::Postfix, Prec::Pow)),
    }
}

/// An operator's CHL spelling: [`BinOpKind::sym`], except xor, which CHL writes `^`, and
/// string concatenation, which it writes `+`.
fn binop_text(op: &BinOpKind) -> &'static str {
    match op {
        BinOpKind::BoolLogic(crate::ccl::LogicKind::Xor) => "^",
        BinOpKind::Concat => "+",
        _ => op.sym(),
    }
}

/// `e` with the variables an environment binds followed to what they stand for, and the
/// depth of the environment that is written in.
fn resolve<'a>(mut e: &'a Expr, env: &Env<'a>) -> (&'a TypedExprNode, usize) {
    let mut depth = env.len();
    while let TypedExprNode::Var(name) = &e.node {
        match env[..depth].iter().rev().find(|(n, _, _)| *n == name) {
            Some((_, bound, d)) => {
                e = bound;
                depth = *d;
            }
            None => break,
        }
    }
    (&e.node, depth)
}

/// The `key` field of a literal tuple or record, with the depth it is written at.
fn project<'a>(
    (node, depth): (&'a TypedExprNode, usize),
    key: &crate::ccl::ProjKey,
) -> Option<(&'a Expr, usize)> {
    use crate::ccl::ProjKey;
    match (node, key) {
        (TypedExprNode::Tuple(elts), ProjKey::Index(i)) => elts.get(*i).map(|x| (x, depth)),
        (TypedExprNode::Record(fields), ProjKey::Field(n)) => {
            fields.iter().find(|(k, _)| k == n).map(|(_, x)| (x, depth))
        }
        _ => None,
    }
}

/// A name as a reader sees it, or `None` for one the compiler minted with no spelling a
/// reader knows. An imported module's member is qualified by its module, as
/// [`Name`]'s `Display` writes it.
fn spelling(name: &Name) -> Option<String> {
    let base = name.base();
    (!base.starts_with("__")).then(|| match name.home() {
        Some(home) => format!("{home}::{base}"),
        None => base.to_string(),
    })
}

/// Collect into `out` the spelling of every name `ty` holds: its parameters, its
/// functions' binders, and the variables of its predicates.
fn type_spellings(ty: &Type, out: &mut HashSet<String>) {
    match ty {
        Type::Param(p) => {
            out.insert(p.spelling.to_string());
        }
        Type::Fun { name: Some(n), .. } => out.extend(spelling(n)),
        Type::Refinement(_, refinements) => {
            for r in refinements.iter() {
                expr_spellings(&r.predicate, out);
            }
        }
        Type::Poly(poly) => {
            out.extend(poly.params.iter().map(|p| p.param.spelling.to_string()));
        }
        _ => {}
    }
    ty.walk_children(|t| type_spellings(t, out));
}

/// [`type_spellings`] for a predicate term.
fn expr_spellings(e: &Expr, out: &mut HashSet<String>) {
    match &e.node {
        TypedExprNode::Var(n) => out.extend(spelling(n)),
        TypedExprNode::Lambda { param, .. } => out.extend(spelling(&param.name)),
        _ => {}
    }
    e.walk_children(|c| expr_spellings(c, out));
}

fn lit_text(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::String(s) => format!("{s:?}"),
        Lit::Bool(true) => "True".to_string(),
        Lit::Bool(false) => "False".to_string(),
        Lit::Unit => "{}".to_string(),
    }
}

/// A variant type's arms, written by [`crate::util::fmt_variant_arms`].
struct VariantArms(Vec<(String, Option<String>)>);

impl fmt::Display for VariantArms {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::util::fmt_variant_arms(f, self.0.iter().cloned(), false)
    }
}

#[cfg(test)]
mod tests {
    use super::chl_type;
    use crate::ccl::lower::test_helpers::lower_type;
    use crate::ccl::{ChanLevel, Name, Type};

    /// A type an annotation writes prints as an annotation, and that annotation lowers
    /// to the same type.
    #[rstest::rstest]
    #[case("Int", "Int")]
    #[case("UInt", "UInt")]
    #[case("{}", "{}")]
    #[case("{Int, String}", "{Int, String}")]
    #[case("{Int,}", "{Int,}")]
    #[case("{a: Int, b: Bool}", "{a: Int, b: Bool}")]
    #[case("{`a{Int} | `b}", "{`a{Int} | `b}")]
    #[case("Option(Int)", "Option(Int)")]
    #[case("{Int where _ > 0}", "{Int where _ > 0}")]
    #[case("{Int where _ > 0 and _ < 10}", "{Int where _ > 0 and _ < 10}")]
    // Two refinements of one base are one set, written nested in a fixed order.
    #[case("{{Int where _ > 0} where _ < 10}", "{{Int where _ < 10} where _ > 0}")]
    #[case(
        "{ {x: Int, y: Int} where _.y != 0}",
        "{{x: Int, y: Int} where _.y != 0}"
    )]
    #[case("Int => Bool", "Int => Bool")]
    #[case("{Int, Int} => Int", "{Int, Int} => Int")]
    #[case("(Int => Int) => Int", "(Int => Int) => Int")]
    #[case("Int => Int => Int", "Int => Int => Int")]
    #[case("List(Int)", "List(Int)")]
    #[case("List({Int where _ > 0})", "List({Int where _ > 0})")]
    #[case("Array(3, Int)", "Array(3, Int)")]
    #[case("Map(String, Int)", "Map(String, Int)")]
    #[case("Set(Int)", "Set(Int)")]
    #[case("Collection(Int)", "Collection(Int)")]
    #[case("FullMap(Int, String)", "FullMap(Int, String)")]
    #[case("forall (T) {T, T} => T", "forall (T) {T, T} => T")]
    #[case(
        "forall (T, U <: {at: Int}) {T, U} => T",
        "forall (T, U <: {at: Int}) {T, U} => T"
    )]
    #[case(
        "forall (T) {T, T} => T requires Addable(T, T, Output=T)",
        "forall (T) {T, T} => T requires Addable(T, T, Output=T)"
    )]
    fn a_written_type_prints_as_an_annotation_that_lowers_back(
        #[case] annotation: &str,
        #[case] printed: &str,
    ) {
        let ty = lower_type(annotation);
        let chl = chl_type(&ty);
        assert_eq!(chl, printed);
        let again = lower_type(&chl);
        assert_eq!(
            again.without_pi_names().to_string(),
            ty.without_pi_names().to_string(),
            "{printed} lowers to the type it was printed from",
        );
    }

    /// A form CHL has no spelling for is written in the checker's notation between
    /// `‹…›`.
    #[test]
    fn a_type_chl_cannot_write_is_marked() {
        assert_eq!(
            chl_type(&Type::ChanDom(Name::raw("d"), ChanLevel(0))),
            "‹chan(d)›"
        );
    }

    /// A form only a diagnostic writes reads as CHL.
    #[test]
    fn an_index_range_reads_as_its_bound() {
        assert_eq!(chl_type(&Type::UIntRange(3)), "{UInt where _ < 3}");
    }
}
