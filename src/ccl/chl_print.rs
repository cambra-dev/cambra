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
//! dependent function `(k: …) |=> …` or `(x: …) => …`, an index range written as
//! `{UInt where _ < n}`. What the notation has no form for at all is described between
//! `‹…›`, never dropped and never written with a name the program did not write: an
//! inference variable as `‹?1›`, numbered within its message ([`Writer`]), an argument outside
//! the written type as [`OUTER_ARGUMENT`], and
//! anything else as [`NOT_PRINTABLE`].

use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::infer::solver::display::InferredPoly;
use crate::ccl::names::SyntheticKind;
use crate::ccl::ty::{FunKind, PolyType, TypeKind, TypeParamId};
use crate::ccl::{BaseType, BinOpKind, Builtin, Expr, HistoryKind, Lit, Name, Type, TypedExprNode};
use crate::ccl::{FieldKey, ProjKey, UnaryOpKind};

/// What a written type says for a part CHL has no spelling for and no description fits.
pub const NOT_PRINTABLE: &str = "‹not printable yet›";

/// An argument bound outside the written type, which reads a function's parameter or a
/// collection's key without its binder in scope.
pub const OUTER_ARGUMENT: &str = "‹outer argument›";

/// The key type of a collection outside the written type.
pub const OUTER_KEYS: &str = "‹outer keys›";

/// `ty` written in CHL.
pub fn chl_type(ty: &Type) -> String {
    Writer::default().ty(ty)
}

/// Types written for one message. Each inference variable is numbered `‹?1›`, `‹?2›`, … in
/// the order the message first writes it, so one variable reads the same in every type
/// the message writes.
#[derive(Default)]
pub struct Writer {
    /// Each variable written so far, by its checker's spelling, in the order first written.
    variables: Rc<RefCell<Vec<String>>>,
}

impl Writer {
    /// `ty` written in CHL ([`chl_type`]).
    pub fn ty(&self, ty: &Type) -> String {
        self.ty_in(ty, None)
    }

    fn ty_in(&self, ty: &Type, home: Option<&[SmolStr]>) -> String {
        Printer {
            home: home.map(<[SmolStr]>::to_vec),
            variables: Rc::clone(&self.variables),
            ..Printer::for_type(ty)
        }
        .annotation(ty)
    }

    /// An inferred polymorphic type written in CHL ([`chl_inferred_poly`]).
    pub fn inferred_poly(&self, inferred: &InferredPoly) -> String {
        self.inferred_poly_in(inferred, None)
    }

    fn inferred_poly_in(&self, inferred: &InferredPoly, home: Option<&[SmolStr]>) -> String {
        let mut p = Printer {
            joins: inferred.join_texts(|ty| self.ty_in(ty, home)),
            home: home.map(<[SmolStr]>::to_vec),
            variables: Rc::clone(&self.variables),
            ..Printer::for_type(&Type::Poly(Rc::new(inferred.poly.clone())))
        };
        if inferred.poly.params.is_empty() {
            p.ty(&inferred.poly.body)
        } else {
            p.poly(&inferred.poly)
        }
    }
}

/// An operator as a diagnostic names it: its CHL spelling, in backticks.
pub fn chl_operator(op: &BinOpKind) -> String {
    format!("`{}`", binop_text(op))
}

/// Whether two types have the same diagnostic text, including any descriptions that hide
/// structural differences. This compares what the reader sees, not type equality.
pub fn renders_alike(a: &Type, b: &Type) -> bool {
    chl_type(a) == chl_type(b)
}

/// A refinement predicate written in CHL, `_` for the refined value.
pub fn chl_predicate(predicate: &Expr) -> String {
    let mut taken = HashSet::new();
    expr_spellings(predicate, &mut taken);
    Printer {
        taken,
        ..Printer::default()
    }
    .expr(predicate, Prec::Lowest, &Vec::new())
}

/// `ty` written in CHL as the module at `home` writes it: its own nominal types by their
/// names alone.
pub fn chl_type_in(ty: &Type, home: &[SmolStr]) -> String {
    written_in(ty, Some(home))
}

fn written_in(ty: &Type, home: Option<&[SmolStr]>) -> String {
    Writer::default().ty_in(ty, home)
}

/// An inferred polymorphic type written in CHL: its `Poly`, or its body alone when it
/// has no parameters, with each join or meet the notation cannot write written as its
/// operands, `A ∨ Int`.
pub fn chl_inferred_poly(inferred: &InferredPoly) -> String {
    chl_inferred_poly_in(inferred, None)
}

/// [`chl_inferred_poly`], written as the module at `home` writes it when there is one
/// ([`chl_type_in`]).
pub fn chl_inferred_poly_in(inferred: &InferredPoly, home: Option<&[SmolStr]>) -> String {
    Writer::default().inferred_poly_in(inferred, home)
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
    /// Every binder the compiler minted that a family is applied at outside of it, with the
    /// spelling it is written with ([`Printer::family_arg`]).
    free_spelled: Vec<(Name, String)>,
    /// Every spelling a name in the printed type has, so a binder the compiler minted is
    /// given one that no other name in the text reads as.
    taken: HashSet<String>,
    /// The text of each parameter that stands for a join or meet
    /// ([`chl_inferred_poly`]).
    joins: Vec<(TypeParamId, String)>,
    /// The path of the module the text is written in, whose own nominal types are written
    /// by their names alone ([`chl_type_in`]).
    home: Option<Vec<SmolStr>>,
    /// The variables of the message the text is part of ([`Writer`]).
    variables: Rc<RefCell<Vec<String>>>,
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
        match spelling(name) {
            Some(own) => own,
            None => self.fresh(preferred),
        }
    }

    /// `preferred`, or `preferred` numbered, whichever no other name in the type or binder
    /// in scope reads as.
    fn fresh(&self, preferred: &str) -> String {
        let free = |candidate: &String| {
            !self.taken.contains(candidate)
                && !self.spelled.iter().any(|(_, s)| s == candidate)
                && !self.free_spelled.iter().any(|(_, s)| s == candidate)
                && !self.binders.iter().flatten().any(|s| s == candidate)
        };
        std::iter::once(preferred.to_string())
            .chain((1..).map(|i| format!("{preferred}{i}")))
            .find(free)
            .expect("an unbounded sequence of spellings has one not taken")
    }

    /// `ty` as a whole annotation: a bounded one is written as the bound it states, `<: T`
    /// (`docs/chl-spec.md`, "Two annotation forms: exact and bounded"). Inside another type a
    /// bound has no form, so [`ty`](Self::ty) writes it in the checker's notation.
    fn annotation(&mut self, ty: &Type) -> String {
        match ty {
            Type::BoundedHole(bound) => format!("<: {}", self.ty(bound)),
            _ => self.ty(ty),
        }
    }

    /// An inference variable, numbered within its message ([`Writer`]): its occurrences
    /// are one type, which `_` would not say.
    fn variable(&mut self, ty: &Type) -> String {
        let key = ty.to_string();
        let mut variables = self.variables.borrow_mut();
        let number = match variables.iter().position(|v| *v == key) {
            Some(i) => i + 1,
            None => {
                variables.push(key);
                variables.len()
            }
        };
        format!("‹?{number}›")
    }

    /// `forall (T, U <: B) V requires …`.
    fn poly(&mut self, poly: &PolyType) -> String {
        let poly = &poly.with_member_names();
        // A family parameter is written with its kind, `V: K => Type`, and a bound on its
        // values as a requirement, `forall (k: K) V(k) <: U`, whose binders the kind keeps no
        // names for, so they are spelled `k`, `k1`, ….
        let mut family_bounds: Vec<String> = Vec::new();
        let params: Vec<String> = poly
            .params
            .iter()
            .filter(|p| !poly.is_member(&p.param))
            .map(|p| match p.kind.family_domains() {
                Some(domains) => {
                    let shown: Vec<String> = domains.iter().map(|d| self.ty(d)).collect();
                    let kind = match shown.as_slice() {
                        [one] => format!("{one} => Type"),
                        many => format!("{{{}}} => Type", many.join(", ")),
                    };
                    if let Some(bound) = p.kind.family_bound() {
                        let names: Vec<String> = (0..domains.len())
                            .map(|i| {
                                if i == 0 {
                                    "k".to_string()
                                } else {
                                    format!("k{i}")
                                }
                            })
                            .collect();
                        let binders: Vec<String> = names
                            .iter()
                            .zip(&shown)
                            .map(|(k, d)| format!("{k}: {d}"))
                            .collect();
                        family_bounds.push(format!(
                            "forall ({}) {}({}) <: {}",
                            binders.join(", "),
                            p.param.spelling,
                            names.join(", "),
                            self.ty(bound)
                        ));
                    }
                    format!("{}: {kind}", p.param.spelling)
                }
                None => match p.bound() {
                    Some(bound) => format!("{} <: {}", p.param.spelling, self.ty(bound)),
                    None => p.param.spelling.to_string(),
                },
            })
            .collect();
        let body = self.ty(&poly.body);
        let mut requires = family_bounds;
        requires.extend(poly.requires_text(|t| self.ty(t)));
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
            Type::SharedHole(_) | Type::BarrierVar(_) | Type::Infer(_) => self.variable(ty),
            Type::Param(p) => match self.joins.iter().find(|(id, _)| *id == p.id) {
                Some((_, text)) => text.clone(),
                None => p.spelling.to_string(),
            },
            // A compiler-made family has no CHL spelling.
            Type::FamilyApp(app) if app.param.generalized => NOT_PRINTABLE.to_string(),
            Type::FamilyApp(app) => {
                let args: Vec<String> = app.args.iter().map(|a| self.family_arg(&a.term)).collect();
                format!("{}({})", app.param.spelling, args.join(", "))
            }
            Type::Family { binders, body } => self.family(binders, body),
            Type::Tuple(ts) => match ts.as_slice() {
                [] => "{}".to_string(),
                [only] => format!("{{{},}}", self.ty(only)),
                _ => {
                    let parts: Vec<String> = ts.iter().map(|t| self.ty(t)).collect();
                    format!("{{{}}}", parts.join(", "))
                }
            },
            Type::OpenTuple(ts) => {
                let parts: Vec<String> = ts.iter().map(|t| self.ty(t)).collect();
                format!("{{{}, ..}}", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", self.ty(t)))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            Type::Variant(tags, openness) => {
                let named = tags.iter().all(|(k, _)| matches!(k, FieldKey::Name(_)));
                if !named {
                    return NOT_PRINTABLE.to_string();
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
                let closed = VariantArms(arms).to_string();
                match openness.permits_extra_tags() {
                    true => format!("{} | ‹more arms›}}", &closed[..closed.len() - 1]),
                    false => closed,
                }
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
            } => self.fun(name.as_ref(), fun_kind, domain, codomain),
            Type::History {
                function,
                history_kind,
            } => match function.as_ref() {
                // A value that reads its position has no spelling: `Mut` and `Feed` name
                // one value type for every position.
                Type::Fun {
                    name: Some(key),
                    codomain,
                    ..
                } if crate::ccl::subst::codomain_depends_on(key, codomain) => {
                    NOT_PRINTABLE.to_string()
                }
                Type::Fun {
                    domain, codomain, ..
                } => match history_kind {
                    HistoryKind::Overwrite => {
                        format!("Mut({}, {})", self.ty(codomain), self.ty(domain))
                    }
                    _ => format!("Feed({})", self.ty(codomain)),
                },
                _ => NOT_PRINTABLE.to_string(),
            },
            Type::Poly(poly) => self.poly(poly),
            Type::Nominal(decl, args) => {
                let name = if self.home.as_deref() == Some(decl.module.as_slice()) {
                    decl.name.to_string()
                } else {
                    decl.spelled()
                };
                if args.is_empty() {
                    return name;
                }
                let args: Vec<String> = args.iter().map(|t| self.ty(t)).collect();
                format!("{name}({})", args.join(", "))
            }
            // No program writes one; this names both sides.
            Type::Split { input, output } => {
                format!("in {} out {}", self.ty(input), self.ty(output))
            }
            // A sum's witness, read inside the sum's values: the sum is a collection
            // around the written part, and the witness is its key type.
            Type::WitnessRef(_) => OUTER_KEYS.to_string(),
            Type::WitnessProjection(p) => {
                let collection = self.expr(&p.term, Prec::Lowest, &Vec::new());
                format!("‹the keys of {collection}›")
            }
            Type::DepTuple(components) => self.dep_tuple(components),
            Type::ChanDom(..) | Type::BoundedHole(_) => NOT_PRINTABLE.to_string(),
        }
    }

    /// An argument of a family application. A binder the compiler minted that the printed
    /// text does not introduce is written at a spelling an unnamed binder would take, the
    /// same one at each of its occurrences.
    fn family_arg(&mut self, term: &Expr) -> String {
        if let TypedExprNode::Var(n) = &term.node
            && !n.is_elem()
            && n.pi_bound_index().is_none()
            && spelling(n).is_none()
            && !self.spelled.iter().any(|(m, _)| m == n)
        {
            if let Some((_, s)) = self.free_spelled.iter().find(|(m, _)| m == n) {
                return s.clone();
            }
            let s = self.binder(n, "k");
            self.free_spelled.push((n.clone(), s.clone()));
            return s;
        }
        self.expr(term, Prec::Lowest, &Vec::new())
    }

    /// A family, `\k: K -> T`, or its body alone where the body reads no binder: a type
    /// where a family is wanted is the family constant at it.
    fn family(&mut self, binders: &[(Option<Name>, Type)], body: &Type) -> String {
        let dependent = crate::ccl::subst::references_binder_within(body, binders.len() as u32);
        let mut shown = Vec::with_capacity(binders.len());
        for (name, domain) in binders {
            let spelled = match name {
                Some(n) => self.binder(n, "k"),
                None => "_".to_string(),
            };
            shown.push(format!("{spelled}: {}", self.ty(domain)));
            self.binders.push(Some(spelled.clone()));
            if let Some(n) = name {
                self.spelled.push((n.clone(), spelled));
            }
        }
        let text = self.ty(body);
        for (name, _) in binders {
            self.binders.pop();
            if name.is_some() {
                self.spelled.pop();
            }
        }
        if dependent {
            format!("\\{} -> {text}", shown.join(", "))
        } else {
            text
        }
    }

    /// A function: a collection over its domain when its kind is data, a `=>` otherwise.
    fn fun(
        &mut self,
        name: Option<&Name>,
        fun_kind: &FunKind,
        domain: &Type,
        codomain: &Type,
    ) -> String {
        let witnesses = fun_kind.witnesses();
        if !witnesses.is_empty() {
            return self.sum(name, witnesses, domain, codomain);
        }
        // A function whose codomain names its binder: CHL writes the binder only in a
        // `def`'s signature, so a type spells it as the parameter of the arrow.
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
        let arrow = if is_data { "|=>" } else { "=>" };
        match (dependent, domain) {
            (None, Type::UIntRange(n)) if is_data => format!("Array({n}, {cod})"),
            (None, Type::DataSource(source)) if is_data => format!("Source({source}, {cod})"),
            // `_ |=> V` lowers to a funkind hole, which admits a sum; a plain collection over
            // a hole domain is written `FullMap(_, V)`, which lowers back to it.
            (None, Type::Hole) if matches!(fun_kind, FunKind::Data(None)) => {
                format!("FullMap(_, {cod})")
            }
            (Some(_), _) => format!("({binder}: {dom}) {arrow} {cod}"),
            // An arrow is right-associative, so a function domain is parenthesized.
            (None, Type::Fun { .. }) => format!("({dom}) {arrow} {cod}"),
            (None, _) => format!("{dom} {arrow} {cod}"),
        }
    }

    /// A sum: the collection type its witness's kind names, or the `Box` of the
    /// alternatives it enumerates.
    fn sum(
        &mut self,
        name: Option<&Name>,
        witnesses: &[crate::ccl::ty::Witness],
        domain: &Type,
        codomain: &Type,
    ) -> String {
        let [w] = witnesses else {
            return NOT_PRINTABLE.to_string();
        };
        if !matches!(domain, Type::WitnessRef(id) if id == w.id()) {
            return NOT_PRINTABLE.to_string();
        }
        // An alternative is a collection over its own candidate, which a value reading
        // the witness reads.
        if let TypeKind::Enumerated(candidates) = w.type_kind() {
            let alternatives: Vec<String> = candidates
                .iter()
                .map(|candidate| {
                    let values = crate::ccl::ty::instantiate_witness(codomain, w.id(), candidate);
                    let alternative = Type::Fun {
                        name: name.cloned(),
                        fun_kind: FunKind::Data(None),
                        domain: Box::new(candidate.clone()),
                        codomain: Box::new(values),
                    };
                    self.ty(&alternative)
                })
                .collect();
            return format!("Box({})", alternatives.join(" | "));
        }
        // The collection type names no key, so a value reading it reads a key outside
        // the written value type.
        self.binders.push(Some(OUTER_ARGUMENT.to_string()));
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
            TypeKind::Family { .. } => unreachable!(
                "a family's kind is a family parameter's, and no witness ranges over it"
            ),
            TypeKind::Enumerated(_) => {
                unreachable!("an enumerated sum is written as a `Box` above")
            }
        }
    }

    /// A dependent tuple as the tuple of its components, each reference to an earlier
    /// component described by its position: CHL has no binder in a tuple type.
    fn dep_tuple(&mut self, components: &[(Option<Name>, Type)]) -> String {
        let mut parts = Vec::with_capacity(components.len());
        let spelled = self.spelled.len();
        for (position, (name, component)) in components.iter().enumerate() {
            parts.push(self.ty(component));
            let described = format!("‹position {position}›");
            // A later component reads this one by index in a type and by name in a term.
            if let Some(name) = name {
                self.spelled.push((name.clone(), described.clone()));
            }
            self.binders.push(Some(described));
        }
        self.binders.truncate(self.binders.len() - components.len());
        self.spelled.truncate(spelled);
        format!("{{{}}}", parts.join(", "))
    }

    /// A refinement predicate, at least as tight as `min`.
    fn expr<'a>(&mut self, e: &'a Expr, min: Prec, env: &Env<'a>) -> String {
        at_least(self.expr_inner(e, env), min)
    }

    fn expr_inner<'a>(&mut self, e: &'a Expr, env: &Env<'a>) -> (Prec, String) {
        match &e.node {
            TypedExprNode::Lit(lit) => (Prec::Atom, lit_text(lit)),
            // `_` is the predicate's own element. CHL has no spelling for an enclosing
            // refinement's, `__elem^𝑛`, which `spelling` declines and the fallback marks.
            TypedExprNode::Var(name) if name.is_elem() => (Prec::Atom, "_".to_string()),
            TypedExprNode::Var(name) => {
                if let Some((_, bound, depth)) = env.iter().rev().find(|(n, _, _)| *n == name) {
                    let outer: Env<'a> = env[..*depth].to_vec();
                    return self.expr_inner(bound, &outer);
                }
                if let Some((_, s)) = self.spelled.iter().rev().find(|(n, _)| n == name) {
                    return (Prec::Atom, s.clone());
                }
                // A reference to a function outside the written type is to the key of
                // the collection the written type is the values of.
                if let Some(index) = name.pi_bound_index() {
                    let text = match (self.binders.len() as u32).checked_sub(index + 1) {
                        Some(i) => self.binders[i as usize]
                            .clone()
                            .unwrap_or_else(|| NOT_PRINTABLE.to_string()),
                        None => OUTER_ARGUMENT.to_string(),
                    };
                    return (Prec::Atom, text);
                }
                let text = match (spelling(name), name) {
                    (Some(s), _) => s,
                    // A `def`'s parameters, which it binds as one tuple.
                    (None, _) if let Some(positions) = name.positions() => {
                        format!("({})", positions.join(", "))
                    }
                    // The binder the solver gives an application's expected function, which
                    // the written type is the result of.
                    (
                        None,
                        Name::Synthetic {
                            kind: SyntheticKind::SolverArg,
                            ..
                        },
                    ) => OUTER_ARGUMENT.to_string(),
                    (None, _) => NOT_PRINTABLE.to_string(),
                };
                (Prec::Atom, text)
            }
            TypedExprNode::BinOp { left, op, right } => {
                let l = self.expr_inner(left, env);
                let r = self.expr_inner(right, env);
                infix(op, l, r)
            }
            TypedExprNode::UnaryOp(UnaryOpKind::Neg, operand) => (
                Prec::Unary,
                format!("-{}", self.expr(operand, Prec::Unary, env)),
            ),
            TypedExprNode::UnaryOp(op @ (UnaryOpKind::Not | UnaryOpKind::NotRefined), operand) => (
                Prec::Not,
                format!("{} {}", unary_text(*op), self.expr(operand, Prec::Not, env)),
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
                    .map(|entry| {
                        let k = &entry.label;
                        format!("{k}={}", self.expr(&entry.value, Prec::Lowest, env))
                    })
                    .collect();
                (Prec::Atom, format!("({})", parts.join(", ")))
            }
            TypedExprNode::Compose(stages) => match stages.as_slice() {
                [source, stage] => match &stage.node {
                    TypedExprNode::Lambda { param, body } => {
                        (Prec::Atom, self.comprehension(source, param, body, env))
                    }
                    _ => (Prec::Atom, NOT_PRINTABLE.to_string()),
                },
                _ => (Prec::Atom, NOT_PRINTABLE.to_string()),
            },
            TypedExprNode::Lambda { .. } if crate::ccl::ccl_utils::loop_parts(e).is_some() => {
                let parts = crate::ccl::ccl_utils::loop_parts(e).expect("matched above");
                (
                    Prec::Atom,
                    self.comprehension(parts.source, parts.element, parts.body, env),
                )
            }
            // `unbox` is the second projection of a sum: the collection it holds, which the
            // program wrote as the sum itself.
            TypedExprNode::Apply { function, argument }
                if matches!(function.node, TypedExprNode::Builtin(Builtin::Unbox)) =>
            {
                self.expr_inner(argument, env)
            }
            TypedExprNode::Apply { function, argument } => self.apply(function, argument, env),
            // A ternary, as lowering builds one: a guard with its arm, then `True` with the
            // other.
            TypedExprNode::Case {
                scrutinee: None,
                branches,
            } if let [then, otherwise] = branches.as_slice()
                && then.pattern.is_none()
                && otherwise.pattern.is_none()
                && matches!(otherwise.guard.node, TypedExprNode::Lit(Lit::Bool(true))) =>
            {
                let arm = self.expr(&then.body, Prec::Or, env);
                let guard = self.expr(&then.guard, Prec::Or, env);
                let other = self.expr(&otherwise.body, Prec::Lowest, env);
                (Prec::Lowest, format!("{arm} if {guard} else {other}"))
            }
            _ => (Prec::Atom, NOT_PRINTABLE.to_string()),
        }
    }

    /// `argument ▷ function`: a field read, a lambda's body at the argument, a
    /// membership test, a proven lookup `c[k]!`, a call, or a point-free function read at
    /// its argument ([`point`](Self::point)). A lookup and a call differ only in the
    /// function's kind, so a function whose type does not say which is not printable.
    ///
    /// Only a field read of a name is what lowering builds from the text written here;
    /// each other form is the CHL a reader would write for the term, which lowers to a
    /// different term, so the type it sits in is not an annotation.
    fn apply<'a>(
        &mut self,
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
                // A position of a `def`'s parameter tuple is the parameter.
                if let (TypedExprNode::Var(tuple), ProjKey::Index(i)) = (&argument.node, key)
                    && let Some(parameter) = tuple.positions().and_then(|ps| ps.get(*i))
                {
                    return (Prec::Atom, parameter.to_string());
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
            _ => {
                let argument = self.val(argument, env);
                match self.point(function, argument, env) {
                    Some(value) => value.written(),
                    None => (Prec::Atom, NOT_PRINTABLE.to_string()),
                }
            }
        }
    }

    /// `e` as a [`Val`]: a tuple literal keeps its components apart.
    fn val<'a>(&mut self, e: &'a Expr, env: &Env<'a>) -> Val {
        match &e.node {
            TypedExprNode::Tuple(elts) => {
                Val::Tuple(elts.iter().map(|x| self.val(x, env)).collect())
            }
            _ => {
                let (prec, text) = self.expr_inner(e, env);
                Val::Written(prec, text)
            }
        }
    }

    /// The point-free function `f` read at `argument`: the CHL expression its result is.
    /// `None` for a function with no reading.
    ///
    /// `λ` elimination writes a predicate point-free (`__elem ▷ ((id, 1 ▷ const) ▷ zip ≫
    /// eq)`), and this reads it back to the expression it came from (`_ == 1`). A function
    /// that is neither a combinator nor an operator is a collection, read as a proven
    /// lookup, or a function, read as a call; `box` and a trait's function are calls by
    /// name.
    fn point<'a>(&mut self, f: &'a Expr, argument: Val, env: &Env<'a>) -> Option<Val> {
        let pair = |argument: Val| match argument {
            Val::Tuple(parts) => <[Val; 2]>::try_from(parts).ok(),
            Val::Written(..) => None,
        };
        let written = |(prec, text): (Prec, String)| Some(Val::Written(prec, text));
        match &f.node {
            // `unbox` is the second projection of a sum: the collection it holds.
            TypedExprNode::Builtin(Builtin::Id | Builtin::Unbox) => Some(argument),
            TypedExprNode::Builtin(Builtin::BinOp(op)) => {
                let [l, r] = pair(argument)?;
                written(infix(op, l.written(), r.written()))
            }
            // The same integer as an `Int` and a `UInt`.
            TypedExprNode::Builtin(Builtin::IntEqUint) => {
                let [l, r] = pair(argument)?;
                let (l, r) = (l.written(), r.written());
                let (l, r) = (at_least(l, Prec::Cmp.next()), at_least(r, Prec::Cmp.next()));
                written((Prec::Cmp, format!("{l} == {r}")))
            }
            TypedExprNode::Builtin(Builtin::Neg) => written((
                Prec::Unary,
                format!("-{}", at_least(argument.written(), Prec::Unary)),
            )),
            TypedExprNode::Builtin(Builtin::NotFn) => written((
                Prec::Not,
                format!("not {}", at_least(argument.written(), Prec::Not)),
            )),
            TypedExprNode::Proj(key) => match (argument, key) {
                (Val::Tuple(mut parts), ProjKey::Index(i)) if *i < parts.len() => {
                    Some(parts.swap_remove(*i))
                }
                (argument, _) => {
                    let target = at_least(argument.written(), Prec::Postfix);
                    written((Prec::Postfix, format!("{target}.{key}")))
                }
            },
            TypedExprNode::Compose(stages) => stages
                .iter()
                .try_fold(argument, |at, stage| self.point(stage, at, env)),
            TypedExprNode::Apply {
                function: combinator,
                argument: operand,
            } => match &combinator.node {
                TypedExprNode::Builtin(Builtin::Const) => written(self.expr_inner(operand, env)),
                TypedExprNode::Builtin(Builtin::Zip) => {
                    let TypedExprNode::Tuple(fs) = &operand.node else {
                        return None;
                    };
                    fs.iter()
                        .map(|fi| self.point(fi, argument.clone(), env))
                        .collect::<Option<Vec<Val>>>()
                        .map(Val::Tuple)
                }
                TypedExprNode::Builtin(Builtin::CollectionContains) => {
                    let member = at_least(argument.written(), Prec::Cmp.next());
                    let collection = self.expr(operand, Prec::Cmp.next(), env);
                    written((Prec::Cmp, format!("{member} in {collection}")))
                }
                _ => self.call(f, argument, env),
            },
            TypedExprNode::Builtin(Builtin::Box) => {
                let (_, arg) = argument.written();
                written((Prec::Postfix, format!("box({arg})")))
            }
            TypedExprNode::Builtin(_) => None,
            // A trait function that reads a collection as itself, as a loop source's
            // `elements` call does, is the collection the program wrote.
            TypedExprNode::TraitFn { trait_, .. } if trait_.reads_collections() => Some(argument),
            TypedExprNode::TraitFn {
                trait_, function, ..
            } => {
                let (_, arg) = argument.written();
                written((Prec::Postfix, format!("{trait_}::{function}({arg})")))
            }
            _ => self.call(f, argument, env),
        }
    }

    /// `f` applied to `argument`: a proven lookup `f[a]!` for a collection, a call `f(a)`
    /// for a function, and `None` for a function whose type names no kind.
    fn call<'a>(&mut self, f: &'a Expr, argument: Val, env: &Env<'a>) -> Option<Val> {
        let Type::Fun { fun_kind, .. } = f.ty.peel_refinements() else {
            return None;
        };
        let target = self.expr(f, Prec::Postfix, env);
        let (_, arg) = argument.written();
        let text = if fun_kind.resolved().is_data() {
            format!("{target}[{arg}]!")
        } else {
            format!("{target}({arg})")
        };
        Some(Val::Written(Prec::Postfix, text))
    }

    /// `c ≫ λ x → b` as the comprehension `[b for x in c]`, or, over a list literal,
    /// the list of `b` at each element.
    fn comprehension<'a>(
        &mut self,
        source: &'a Expr,
        param: &'a crate::ccl::TypedBinding,
        body: &'a Expr,
        env: &Env<'a>,
    ) -> String {
        if let (TypedExprNode::List(elts), depth) = resolve(source, env) {
            let parts: Vec<String> = elts
                .iter()
                .map(|elt| {
                    let mut inner: Env<'a> = env.clone();
                    inner.push((&param.name, elt, depth));
                    self.expr(body, Prec::Lowest, &inner)
                })
                .collect();
            return format!("[{}]", parts.join(", "));
        }
        let source = self.expr(source, Prec::Lowest, env);
        let mut inner = env.clone();
        // The comprehension binds the parameter itself, so it reads as its spelling.
        inner.retain(|(n, _, _)| *n != &param.name);
        let x = self.binder(&param.name, "x");
        self.spelled.push((param.name.clone(), x.clone()));
        let body = self.expr(body, Prec::Lowest, &inner);
        self.spelled.pop();
        format!("[{body} for {x} in {source}]")
    }
}

/// A value a point-free function is read at ([`Printer::point`]): an expression, or a
/// tuple whose components a projection or an operator reads apart.
#[derive(Clone)]
enum Val {
    Written(Prec, String),
    Tuple(Vec<Val>),
}

impl Val {
    fn written(self) -> (Prec, String) {
        match self {
            Val::Written(prec, text) => (prec, text),
            Val::Tuple(parts) => {
                let parts: Vec<String> = parts.into_iter().map(|v| v.written().1).collect();
                (Prec::Atom, format!("({})", parts.join(", ")))
            }
        }
    }
}

/// `text`, parenthesized when it binds looser than `min`.
fn at_least((prec, text): (Prec, String), min: Prec) -> String {
    if prec < min {
        format!("({text})")
    } else {
        text
    }
}

/// `l op r` in CHL. `nand`, `nor` and `xnor` have no CHL operator, so each is written as
/// the negation of the operator it complements.
fn infix(op: &BinOpKind, l: (Prec, String), r: (Prec, String)) -> (Prec, String) {
    use crate::ccl::LogicKind as L;
    let complemented = match op.unrefined() {
        BinOpKind::BoolLogic(L::Nand) => Some(L::And),
        BinOpKind::BoolLogic(L::Nor) => Some(L::Or),
        BinOpKind::BoolLogic(L::Xnor) => Some(L::Xor),
        _ => None,
    };
    if let Some(kind) = complemented {
        let (_, inner) = infix(&BinOpKind::BoolLogic(kind), l, r);
        return (Prec::Not, format!("not ({inner})"));
    }
    let (own, lmin, rmin) = binop_prec(op);
    let (l, r) = (at_least(l, lmin), at_least(r, rmin));
    (own, format!("{l} {} {r}", binop_text(op)))
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
/// (`docs/chl-spec.md`, "2.3 Expression precedence"). Only for an operator CHL writes:
/// [`infix`] writes the others as negations.
fn binop_prec(op: &BinOpKind) -> (Prec, Prec, Prec) {
    use crate::ccl::{ArithmeticKind as A, LogicKind as L};
    let leftward = |own: Prec| (own, own, own.next());
    match op.unrefined() {
        BinOpKind::BoolLogic(L::Or) => leftward(Prec::Or),
        BinOpKind::BoolLogic(L::And) => leftward(Prec::And),
        BinOpKind::BoolLogic(L::Xor) => leftward(Prec::Xor),
        BinOpKind::BoolLogic(L::Nand | L::Nor | L::Xnor) => {
            unreachable!("`infix` writes {op:?} as the negation of the operator it complements")
        }
        BinOpKind::Compare(_) => (Prec::Cmp, Prec::Cmp.next(), Prec::Cmp.next()),
        BinOpKind::Arithmetic(A::Add | A::Sub) | BinOpKind::Concat => leftward(Prec::Add),
        BinOpKind::Arithmetic(A::Mul | A::FloorDiv) => leftward(Prec::Mul),
        BinOpKind::Arithmetic(A::Pow) => (Prec::Pow, Prec::Postfix, Prec::Pow),
        refined => unreachable!("`unrefined` answers no `{refined:?}`"),
    }
}

/// A boolean negation's CHL spelling.
fn unary_text(op: UnaryOpKind) -> &'static str {
    match op {
        UnaryOpKind::NotRefined => "^not",
        _ => "not",
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
    key: &ProjKey,
) -> Option<(&'a Expr, usize)> {
    match (node, key) {
        (TypedExprNode::Tuple(elts), ProjKey::Index(i)) => elts.get(*i).map(|x| (x, depth)),
        (TypedExprNode::Record(fields), ProjKey::Field(n)) => fields
            .iter()
            .find(|entry| entry.label == *n)
            .map(|entry| (&entry.value, depth)),
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
        TypedExprNode::Var(n) => {
            out.extend(spelling(n));
            out.extend(n.positions().into_iter().flatten().map(ToString::to_string));
        }
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
    use std::rc::Rc;

    use super::{NOT_PRINTABLE, OUTER_ARGUMENT, chl_type};
    use crate::ccl::lower::test_helpers::lower_type;
    use crate::ccl::{
        BaseType, BinOpKind, Builtin, ChanLevel, CompareKind, Lit, LogicKind, Name, Refinement,
        Type, TypedExpr,
    };

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
    #[case("FullMap(Int, String)", "Int |=> String")]
    #[case("Int |=> String", "Int |=> String")]
    #[case("_ |=> Int", "_ |=> Int")]
    // A plain collection over a hole domain is not `_ |=> Int`, which admits a sum.
    #[case("FullMap(_, Int)", "FullMap(_, Int)")]
    #[case("(Int |=> Int) |=> Int", "(Int |=> Int) |=> Int")]
    #[case("Int => Int |=> Int", "Int => Int |=> Int")]
    #[case("Int |=> Int => Int", "Int |=> Int => Int")]
    #[case("forall (D, T) (D |=> T) => T", "forall (D, T) (D |=> T) => T")]
    #[case("forall (T) {T, T} => T", "forall (T) {T, T} => T")]
    #[case(
        "forall (T, U <: {at: Int}) {T, U} => T",
        "forall (T, U <: {at: Int}) {T, U} => T"
    )]
    #[case(
        "forall (T) {T, T} => T requires r: Addable(T, T), r::Output <: T",
        "forall (T) {T, T} => T requires r: Addable(T, T), r::Output <: T"
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

    /// A form CHL has no spelling for is marked, never written in the checker's notation.
    #[test]
    fn a_type_chl_cannot_write_is_marked() {
        assert_eq!(
            chl_type(&Type::ChanDom(Name::raw("d"), ChanLevel(0))),
            NOT_PRINTABLE
        );
    }

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    fn elem() -> TypedExpr {
        TypedExpr::var(Name::elem()).with_ty(int())
    }

    fn refined(predicate: TypedExpr) -> Type {
        Type::refined_one(int(), Refinement::born(Rc::new(predicate)))
    }

    fn int_lit(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n)).with_ty(int())
    }

    /// A predicate `λ` elimination wrote point-free reads as the expression it came from.
    #[test]
    fn a_point_free_predicate_reads_at_its_argument() {
        let builtin = |b: Builtin| TypedExpr::builtin(b);
        let one = TypedExpr::apply(int_lit(1), builtin(Builtin::Const));
        let pair = TypedExpr::apply(
            TypedExpr::tuple(vec![builtin(Builtin::Id), one]),
            builtin(Builtin::Zip),
        );
        let eq = builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)));
        let function = TypedExpr::compose(vec![pair, eq]);
        let ty = refined(TypedExpr::apply(elem(), function));
        assert_eq!(chl_type(&ty), "{Int where _ == 1}");
    }

    /// `nand`, `nor` and `xnor` have no CHL operator and read as negations.
    #[test]
    fn a_complemented_operator_reads_as_a_negation() {
        let base = Type::Base(BaseType::Bool);
        let b = TypedExpr::var(Name::elem()).with_ty(base.clone());
        let truth = TypedExpr::lit(Lit::Bool(true)).with_ty(base.clone());
        let predicate = TypedExpr::binop(b, BinOpKind::BoolLogic(LogicKind::Nand), truth);
        let ty = Type::refined_one(base, Refinement::born(Rc::new(predicate)));
        assert_eq!(chl_type(&ty), "{Bool where not (_ and True)}");
    }

    /// A reference to the binder of a function around the written type is that
    /// collection's key.
    #[test]
    fn a_key_outside_the_written_type_is_the_outer_key() {
        let k = Name::fresh("__map_k");
        let at_k = TypedExpr::binop(
            elem(),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::var(k.clone()).with_ty(int()),
        );
        let Type::Fun { codomain, .. } = Type::pi(k, int(), refined(at_k)) else {
            unreachable!("`Type::pi` builds a function")
        };
        assert_eq!(
            chl_type(&codomain),
            format!("{{Int where _ == {OUTER_ARGUMENT}}}")
        );
    }

    /// A dependent tuple is the tuple of its components, a read of an earlier one
    /// described by its position.
    #[test]
    fn a_dependent_tuple_names_the_positions_it_reads() {
        let i = Name::fresh("i");
        let at_i = TypedExpr::binop(
            elem(),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::var(i.clone()).with_ty(int()),
        );
        let ty = Type::dep_tuple(vec![(Some(i), int()), (None, refined(at_i))]);
        assert!(matches!(ty, Type::DepTuple(_)), "the premise: {ty}");
        assert_eq!(chl_type(&ty), "{Int, {Int where _ == ‹position 0›}}");
    }

    /// A form only a diagnostic writes reads as CHL.
    #[test]
    fn an_index_range_reads_as_its_bound() {
        assert_eq!(chl_type(&Type::UIntRange(3)), "{UInt where _ < 3}");
    }
}
