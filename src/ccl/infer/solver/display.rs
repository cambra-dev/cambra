//! A diagnostic's rendering of an inferred polymorphic type as an [`InferredPoly`]
//! (`src/ccl/design/type-parameters.md`, "Printing an inferred polymorphic type").
//!
//! Materialization ([`super::coalesce`]) answers what type a position has, so it
//! drops a variable wherever a concrete contribution stands beside it. A rendering
//! of a polymorphic type keeps the variables instead: each one above the cutoff
//! becomes a parameter, its upper bound at a negative position becomes the
//! parameter's bound, and each trait obligation on one becomes a requirement.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::ty::{PolyParam, PolyType, TraitRequirement, TypeParam, TypeParamId};
use crate::ccl::{InferVarId, Level, Type};

use super::coalesce::{coalesce_compact, coalesce_position};
use super::compact::{AtomKey, CompactType, CompactTypeKind, compact_type_polarity_only};
use super::simplify_type::simplify_type_pinning;
use super::traits::TraitObligation;

/// An inferred type written as the polymorphic type an annotation would state: a
/// [`PolyType`] over declared parameters, as lowering writes one, with the joins and
/// meets the notation cannot write recorded beside it.
#[derive(Debug, Clone, PartialEq)]
pub struct InferredPoly {
    /// The type. Without parameters it is its body alone.
    pub poly: PolyType,
    /// The parameters that stand for a join or meet rather than for a variable. Each
    /// occurs in [`poly`](Self::poly) where the join or meet stands, and is not one of
    /// its parameters.
    pub joins: Vec<Join>,
}

/// A join or meet the notation cannot write, which a diagnostic writes as its
/// operands: `A ∨ Int`, `A ∨ B`, `A ∧ B`.
#[derive(Debug, Clone, PartialEq)]
pub struct Join {
    /// The parameter standing where the join or meet does.
    pub at: Rc<TypeParam>,
    /// `true` for a join (at a positive position), `false` for a meet.
    pub join: bool,
    /// The parameters and the type that meet there.
    pub operands: Vec<Type>,
}

impl InferredPoly {
    /// Apply `f` to every type this holds.
    pub fn map_types(&mut self, f: &mut impl FnMut(&mut Type)) {
        for t in self.poly.types_mut() {
            f(t);
        }
        for join in &mut self.joins {
            join.operands.iter_mut().for_each(&mut *f);
        }
    }

    /// The text each join or meet is written as, given how a type is written.
    pub fn join_texts(&self, mut write: impl FnMut(&Type) -> String) -> Vec<(TypeParamId, String)> {
        self.joins
            .iter()
            .map(|j| {
                let operands: Vec<String> = j.operands.iter().map(&mut write).collect();
                (j.at.id, operands.join(if j.join { " ∨ " } else { " ∧ " }))
            })
            .collect()
    }
}

impl std::fmt::Display for InferredPoly {
    /// In the checker's notation, as [`Display for Type`](Type) writes the `Poly`, with
    /// each join or meet written as its operands.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let texts = self.join_texts(|t| t.to_string());
        let mut shown = self.poly.clone();
        // `Display for Type` writes a parameter by its spelling, so each join's stand-in
        // is written as one spelled as its text, for this rendering only.
        for t in shown.types_mut() {
            replace_params(t, &|p| {
                texts
                    .iter()
                    .find(|(id, _)| *id == p.id)
                    .map(|(_, text)| Type::Param(TypeParam::declared(text.as_str())))
            });
        }
        if shown.params.is_empty() {
            write!(f, "{}", shown.body)
        } else {
            write!(f, "{}", Type::Poly(Rc::new(shown)))
        }
    }
}

/// `ty` with each parameter `with` maps replaced.
fn replace_params(ty: &mut Type, with: &impl Fn(&TypeParam) -> Option<Type>) {
    if let Type::Param(p) = ty
        && let Some(replacement) = with(p)
    {
        *ty = replacement;
        return;
    }
    ty.walk_children_mut(|child| replace_params(child, with));
}

/// `ty` as a polymorphic type over its variables above `cutoff`, with a parameter
/// for each, its bounds, and a requirement for each trait obligation on one.
///
/// The variables are named `A`, `B`, … in order of first appearance, skipping a
/// spelling a type parameter in `ty` already has. A part the notation cannot write
/// is a [`Join`]:
///
/// - `A ∨ Int` at a positive position, where a variable and a concrete type meet
///   (`a if c else 1`), and `A ∨ B` where two variables do;
/// - `A ∧ B` at a negative position, where two variables meet, and `A ∧ C` where a
///   variable's second negative occurrence meets another upper bound than its first.
///
/// `None` when `ty` does not materialize, as [`coalesce_compact`] reports: the
/// caller renders it the way it renders any type.
pub fn poly_for_display(ty: &Type, cutoff: Level) -> Option<InferredPoly> {
    let reach = Reach::of(ty, cutoff);
    let requirements: Vec<TraitRequirement> = reach
        .obligations
        .iter()
        .filter_map(|o| o.stated_requirement())
        .collect();

    // One term, so a variable is one identity across the body and every
    // requirement. A requirement's operands receive values, as a function's
    // parameter does from an argument, so they stand at a positive position, where
    // compaction reaches the variables flowing in; at a negative one it would reach
    // only the fresh variable the operator minted. Its associated positions are
    // pinned: the variable standing there may occur nowhere else at the opposite
    // polarity, and it is what ties the requirement's `Output` to the body.
    let mut parts = vec![ty.clone()];
    parts.extend(requirements.iter().map(|r| {
        Type::Tuple(
            r.args
                .iter()
                .cloned()
                .chain(r.assoc.iter().map(|(_, t)| t.clone()))
                .collect(),
        )
    }));
    let mut pinned: BTreeSet<InferVarId> = requirements
        .iter()
        .flat_map(|r| &r.assoc)
        .filter_map(|(_, t)| match t {
            Type::Infer(v) => Some(v.uid),
            _ => None,
        })
        .collect();
    // Polarity-correct throughout: where no value reached a positive position, the
    // variable standing there is what it holds, and a fallback to its upper bound
    // would show a demand as a value.
    let mut compacted = compact_type_polarity_only(&Type::Tuple(parts));
    // A variable at or below the cutoff is one type of the enclosing scope's, not a
    // parameter, so it is pinned at the position it holds: dropped as polar-only, it
    // would leave that position empty, which reads as a parameter of its own.
    let mut enclosing = HashMap::new();
    occurrences(&mut compacted.term, true, &mut enclosing);
    pinned.extend(
        enclosing
            .keys()
            .filter(|v| !reach.quantified(v, cutoff))
            .copied(),
    );
    let mut graph = simplify_type_pinning(compacted, &pinned);
    if !graph.rec_vars.is_empty() {
        return None;
    }

    let mut polarities = HashMap::new();
    occurrences(&mut graph.term, true, &mut polarities);
    let mut st = Parametrize {
        reach: &reach,
        cutoff,
        polarities,
        placeholders: HashMap::new(),
        var_placeholders: HashMap::new(),
        bounds: HashMap::new(),
    };
    st.go(&mut graph.term, true)?;
    let Type::Tuple(mut parts) = coalesce_compact(&graph).ok()? else {
        return None;
    };
    let body = parts.remove(0);

    let mut names = Naming::new(&st, &body, &parts);
    names.visit(&body);
    for part in &parts {
        names.visit(part);
    }
    names.visit_bounds();
    let body = names.rename(&body);

    let params = names
        .order
        .iter()
        .map(|v| {
            PolyParam::with_bound(
                names.param(*v),
                match v {
                    Named::Var(v) => st.bounds.get(v).map(|b| names.rename(b)),
                    Named::Fresh(_) => None,
                    Named::Meet(_) => {
                        unreachable!("a join or meet is not a parameter of its own")
                    }
                },
            )
        })
        .collect();
    let mut requires: Vec<Rc<TraitRequirement>> = Vec::new();
    for (stated, part) in requirements.iter().zip(parts) {
        let Type::Tuple(tys) = part else {
            unreachable!("a requirement is compacted as a tuple and materializes as one");
        };
        // An instance row matches a base whatever its refinements, so a requirement
        // states none.
        let tys: Vec<Type> = tys
            .iter()
            .map(|t| crate::ccl::ccl_utils::strip_refinements(&names.rename(t)))
            .collect();
        let (args, assoc_tys) = tys.split_at(stated.args.len());
        let requirement = TraitRequirement {
            trait_: stated.trait_,
            args: args.to_vec(),
            assoc: stated
                .assoc
                .iter()
                .map(|(name, _)| *name)
                .zip(assoc_tys.iter().cloned())
                .collect(),
        };
        // A requirement about no parameter is one the definition already answered
        // at concrete types.
        if requirement.args.iter().any(|t| names.mentions_param(t))
            && !requires.iter().any(|r| **r == requirement)
        {
            requires.push(Rc::new(requirement));
        }
    }
    Some(InferredPoly {
        poly: PolyType {
            params,
            requires,
            body,
        },
        joins: names.joins.into_inner(),
    })
}

/// What a type reaches through variable bounds: each variable's level, and the
/// obligations watching a variable above the cutoff.
struct Reach {
    levels: HashMap<InferVarId, Level>,
    obligations: Vec<Rc<TraitObligation>>,
}

impl Reach {
    fn of(ty: &Type, cutoff: Level) -> Reach {
        let mut reach = Reach {
            levels: HashMap::new(),
            obligations: Vec::new(),
        };
        let mut seen_obligations = HashSet::new();
        let mut pending = vec![ty.clone()];
        while let Some(ty) = pending.pop() {
            visit_vars(&ty, &mut |v| {
                if reach.levels.insert(v.uid, v.level()).is_some() || v.level() <= cutoff {
                    // A variable at or below the cutoff is the enclosing scope's: its
                    // bounds name nothing deeper, and its obligations are not this
                    // type's requirements.
                    return;
                }
                let bounds = v.bounds.borrow();
                pending.extend(bounds.lower().iter().map(|b| b.ty.clone()));
                pending.extend(bounds.upper().iter().map(|b| b.ty.clone()));
                for (obligation, _) in v.watches.borrow().iter() {
                    if seen_obligations.insert(obligation.uid) {
                        reach.obligations.push(Rc::clone(obligation));
                        pending.extend(obligation.watched_operands());
                        pending.extend(obligation.assoc_types());
                    }
                }
            });
        }
        // Minting order, so the requirements read in the order the body states them.
        reach.obligations.sort_by_key(|o| o.uid);
        reach
    }

    fn quantified(&self, id: &InferVarId, cutoff: Level) -> bool {
        let level = match self.levels.get(id) {
            Some(level) => *level,
            None => crate::ccl::infer_var::lookup(id).map_or(0, |v| v.level()),
        };
        level > cutoff
    }
}

/// Call `f` on every inference variable `ty` names, not entering bounds.
fn visit_vars(ty: &Type, f: &mut impl FnMut(&Rc<crate::ccl::InferVar>)) {
    if let Type::Infer(v) = ty {
        f(v);
    }
    ty.walk_children(|child| visit_vars(child, f));
}

/// The polarities each variable occurs at in `ct`.
fn occurrences(ct: &mut CompactType, pol: bool, out: &mut HashMap<InferVarId, (bool, bool)>) {
    for v in &ct.vars {
        let entry = out.entry(*v).or_default();
        if pol {
            entry.0 = true;
        } else {
            entry.1 = true;
        }
    }
    for_each_child(ct, pol, &mut |child, child_pol| {
        occurrences(child, child_pol, out);
        Some(())
    });
}

/// Call `f` on every position directly under `ct`, with its polarity: fields and
/// payloads as `ct`, a function's domain and its binders' kinds opposite, its codomain
/// as `ct`, a history's parts as `ct` (the polarities [`super::simplify_type`] reads).
/// Stops at the first `None`.
fn for_each_child(
    ct: &mut CompactType,
    pol: bool,
    f: &mut impl FnMut(&mut CompactType, bool) -> Option<()>,
) -> Option<()> {
    for child in ct.rec.iter_mut().flat_map(|r| r.values_mut()) {
        f(child, pol)?;
    }
    for child in ct.var.iter_mut().flat_map(|v| v.tags.values_mut()) {
        f(child, pol)?;
    }
    if let Some(cf) = &mut ct.fun {
        for w in &mut cf.binders {
            match &mut w.type_kind {
                CompactTypeKind::Enumerated(candidates) => {
                    for c in candidates {
                        f(c, !pol)?;
                    }
                }
                CompactTypeKind::SubtypesOf(bound) => f(bound, !pol)?,
                CompactTypeKind::UIntRanges | CompactTypeKind::Type => {}
            }
        }
        f(&mut cf.domain, !pol)?;
        f(&mut cf.codomain, pol)?;
    }
    if let Some((value, domain, _)) = &mut ct.history_slot {
        f(value, pol)?;
        f(domain, pol)?;
    }
    Some(())
}

/// What a placeholder parameter in the rewritten graph stands for.
enum Placeholder {
    /// A variable above the cutoff.
    Var(InferVarId),
    /// A position no variable and no type reached: a parameter of its own.
    Fresh,
    /// Variables, and possibly a type, meeting where the notation has no form for it:
    /// `true` for a join (a positive position), `false` for a meet.
    Meet(bool, Vec<InferVarId>, Option<Type>),
}

/// The rewrite of a simplified graph that puts a placeholder parameter where each
/// variable above the cutoff stands, so that materialization keeps it.
struct Parametrize<'a> {
    reach: &'a Reach,
    cutoff: Level,
    polarities: HashMap<InferVarId, (bool, bool)>,
    placeholders: HashMap<TypeParamId, (Rc<TypeParam>, Placeholder)>,
    var_placeholders: HashMap<InferVarId, Rc<TypeParam>>,
    /// Each variable's upper bound: what stands beside it at a negative position.
    bounds: HashMap<InferVarId, Type>,
}

impl Parametrize<'_> {
    /// Rewrite `ct` and every position under it, children first, so a bound read
    /// off a position already names its children's placeholders.
    fn go(&mut self, ct: &mut CompactType, pol: bool) -> Option<()> {
        for_each_child(ct, pol, &mut |child, child_pol| self.go(child, child_pol))?;
        let quantified: Vec<InferVarId> = ct
            .vars
            .iter()
            .copied()
            .filter(|v| self.reach.quantified(v, self.cutoff))
            .collect();
        let has_content = !ct.atoms.is_empty()
            || ct.rec.is_some()
            || ct.var.is_some()
            || ct.fun.is_some()
            || ct.history_slot.is_some();
        if quantified.is_empty() {
            // Nothing reached this position: it is unconstrained, which a parameter
            // of its own states.
            if !has_content && ct.vars.is_empty() {
                let placeholder = self.mint(Placeholder::Fresh);
                *ct = Self::param_position(placeholder);
            }
            return Some(());
        }
        ct.vars.retain(|v| !quantified.contains(v));
        let content = if has_content {
            Some(coalesce_position(ct, pol).ok()?)
        } else {
            None
        };
        let placeholder = if pol {
            // A variable occurring only here, kept for a requirement, adds nothing
            // beside a type: the type is what the position holds.
            let bipolar: Vec<InferVarId> = quantified
                .iter()
                .copied()
                .filter(|v| self.polarities.get(v).is_some_and(|(p, n)| *p && *n))
                .collect();
            match (content, quantified.as_slice()) {
                (Some(_), _) if bipolar.is_empty() => return Some(()),
                (Some(c), _) => self.mint(Placeholder::Meet(true, bipolar, Some(c))),
                (None, [v]) => self.var(*v),
                (None, _) => self.mint(Placeholder::Meet(true, quantified, None)),
            }
        } else {
            match (content, quantified.as_slice()) {
                (Some(c), [v]) => match self.bounds.get(v) {
                    Some(bound) if *bound != c => {
                        self.mint(Placeholder::Meet(false, vec![*v], Some(c)))
                    }
                    _ => {
                        self.bounds.insert(*v, c);
                        self.var(*v)
                    }
                },
                (None, [v]) => self.var(*v),
                (c, _) => self.mint(Placeholder::Meet(false, quantified, c)),
            }
        };
        *ct = Self::param_position(placeholder);
        Some(())
    }

    fn param_position(placeholder: Rc<TypeParam>) -> CompactType {
        let mut ct = CompactType::value();
        ct.atoms.insert(AtomKey::Param(placeholder));
        ct
    }

    fn var(&mut self, v: InferVarId) -> Rc<TypeParam> {
        if let Some(p) = self.var_placeholders.get(&v) {
            return Rc::clone(p);
        }
        let p = self.mint(Placeholder::Var(v));
        self.var_placeholders.insert(v, Rc::clone(&p));
        p
    }

    fn mint(&mut self, placeholder: Placeholder) -> Rc<TypeParam> {
        let p = TypeParam::declared("_");
        self.placeholders.insert(p.id, (Rc::clone(&p), placeholder));
        p
    }
}

/// The parameter names, in order of first appearance.
struct Naming<'a> {
    st: &'a Parametrize<'a>,
    /// Spellings the type's own parameters have, which a name must not repeat.
    taken: HashSet<SmolStr>,
    /// Each named variable, or a fresh placeholder's id, in naming order.
    order: Vec<Named>,
    names: HashMap<Named, SmolStr>,
    /// The final parameter each named one becomes, minted once so every occurrence is
    /// the same parameter.
    params: std::cell::RefCell<HashMap<Named, Rc<TypeParam>>>,
    /// The joins and meets [`rename`](Self::rename) has met, each once.
    joins: std::cell::RefCell<Vec<Join>>,
}

/// What a final parameter stands for: a variable, a position nothing reached, or a
/// join or meet (a [`Placeholder::Meet`], by its placeholder's id).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Named {
    Var(InferVarId),
    Fresh(TypeParamId),
    Meet(TypeParamId),
}

impl<'a> Naming<'a> {
    fn new(st: &'a Parametrize<'a>, body: &Type, parts: &[Type]) -> Self {
        let mut taken = HashSet::new();
        let mut collect = |t: &Type| {
            visit_params(t, &mut |p| {
                if !st.placeholders.contains_key(&p.id) {
                    taken.insert(p.spelling.clone());
                }
            })
        };
        collect(body);
        parts.iter().for_each(collect);
        Naming {
            st,
            taken,
            order: Vec::new(),
            names: HashMap::new(),
            params: std::cell::RefCell::new(HashMap::new()),
            joins: std::cell::RefCell::new(Vec::new()),
        }
    }

    fn visit(&mut self, ty: &Type) {
        let mut found = Vec::new();
        visit_params(ty, &mut |p| found.push(p.id));
        for id in found {
            match self.st.placeholders.get(&id) {
                Some((_, Placeholder::Var(v))) => self.name(Named::Var(*v)),
                Some((_, Placeholder::Fresh)) => self.name(Named::Fresh(id)),
                Some((_, Placeholder::Meet(_, vars, content))) => {
                    for v in vars {
                        self.name(Named::Var(*v));
                    }
                    if let Some(c) = content {
                        self.visit(c);
                    }
                }
                None => {}
            }
        }
    }

    /// Name what the named variables' bounds mention, until nothing new appears.
    fn visit_bounds(&mut self) {
        let mut i = 0;
        while i < self.order.len() {
            if let Named::Var(v) = self.order[i]
                && let Some(bound) = self.st.bounds.get(&v)
            {
                self.visit(bound);
            }
            i += 1;
        }
    }

    fn name(&mut self, named: Named) {
        if self.names.contains_key(&named) {
            return;
        }
        let spelling = (0..)
            .map(|n: usize| {
                let letter = char::from(b'A' + u8::try_from(n % 26).expect("n % 26 < 26"));
                match n / 26 {
                    0 => SmolStr::from(letter.to_string()),
                    round => SmolStr::from(format!("{letter}{round}")),
                }
            })
            .find(|s| !self.taken.contains(s))
            .expect("the spellings are unbounded");
        self.taken.insert(spelling.clone());
        self.names.insert(named, spelling);
        self.order.push(named);
    }

    fn spelling(&self, named: Named) -> SmolStr {
        self.names[&named].clone()
    }

    /// The final parameter `named` becomes, minted once: a variable's or a fresh
    /// position's spelled by its name, a join's or meet's spelled `_`, its text being
    /// its [`Join`]'s.
    fn param(&self, named: Named) -> Rc<TypeParam> {
        if let Some(p) = self.params.borrow().get(&named) {
            return Rc::clone(p);
        }
        let spelling = match named {
            Named::Var(_) | Named::Fresh(_) => self.spelling(named),
            Named::Meet(_) => SmolStr::new_static("_"),
        };
        let p = TypeParam::declared(spelling);
        self.params.borrow_mut().insert(named, Rc::clone(&p));
        p
    }

    /// `ty` with every placeholder replaced by the parameter it names, a join or
    /// meet's recorded as a [`Join`].
    fn rename(&self, ty: &Type) -> Type {
        let mut out = ty.clone();
        self.rename_in(&mut out);
        out
    }

    fn rename_in(&self, ty: &mut Type) {
        if let Type::Param(p) = ty
            && let Some((_, placeholder)) = self.st.placeholders.get(&p.id)
        {
            let named = match placeholder {
                Placeholder::Var(v) => Named::Var(*v),
                Placeholder::Fresh => Named::Fresh(p.id),
                Placeholder::Meet(..) => Named::Meet(p.id),
            };
            let fresh = !self.params.borrow().contains_key(&named);
            let at = self.param(named);
            if fresh && let Placeholder::Meet(join, vars, content) = placeholder {
                let mut operands: Vec<Type> = vars
                    .iter()
                    .map(|v| Type::Param(self.param(Named::Var(*v))))
                    .collect();
                operands.extend(content.iter().map(|c| self.rename(c)));
                self.joins.borrow_mut().push(Join {
                    at: Rc::clone(&at),
                    join: *join,
                    operands,
                });
            }
            *ty = Type::Param(at);
            return;
        }
        ty.walk_children_mut(|child| self.rename_in(child));
    }

    /// Whether `ty` names a parameter this rendering introduced, a join or meet
    /// included.
    fn mentions_param(&self, ty: &Type) -> bool {
        let params = self.params.borrow();
        let mut found = false;
        visit_params(ty, &mut |p| {
            found |= params.values().any(|mine| mine.id == p.id);
        });
        found
    }
}

fn visit_params(ty: &Type, f: &mut impl FnMut(&Rc<TypeParam>)) {
    if let Type::Param(p) = ty {
        f(p);
    }
    ty.walk_children(|child| visit_params(child, f));
}
