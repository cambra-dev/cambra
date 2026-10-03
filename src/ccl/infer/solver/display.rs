//! A diagnostic's rendering of an inferred polymorphic type as a [`Type::Poly`]
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

use crate::ccl::ty::{PolyParam, PolyRequirement, PolyType, TypeParam, TypeParamId, WrittenAt};
use crate::ccl::{InferVarId, Level, Type};

use super::coalesce::{coalesce_compact, coalesce_position};
use super::compact::{AtomKey, CompactType, CompactTypeKind, compact_type_polarity_only};
use super::simplify_type::simplify_type_pinning;
use super::traits::{StatedRequirement, TraitObligation};

/// `ty` as a polymorphic type over its variables above `cutoff`, or `ty` itself
/// with its variables resolved when it has none.
///
/// The variables are named `A`, `B`, … in order of first appearance, skipping a
/// spelling a type parameter in `ty` already has. A part the notation cannot write
/// is a parameter spelled as what it stands for:
///
/// - `A ∨ Int` at a positive position, where a variable and a concrete type meet
///   (`a if c else 1`), and `A ∨ B` where two variables do;
/// - `A ∧ B` at a negative position, where two variables meet, and `A ∧ C` where a
///   variable's second negative occurrence meets another upper bound than its first.
///
/// `None` when `ty` does not materialize, as [`coalesce_compact`] reports: the
/// caller renders it the way it renders any type.
///
/// The `Poly` is in opened form: its body and bounds hold [`Type::Param`] leaves,
/// and each [`PolyParam::hole`] is the parameter's position, naming no shared hole.
/// It is for display only, and nothing opens it.
pub fn poly_for_display(ty: &Type, cutoff: Level) -> Option<Type> {
    let reach = Reach::of(ty, cutoff);
    let requirements: Vec<StatedRequirement> = reach
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
            r.operands
                .iter()
                .cloned()
                .chain(r.assoc.iter().map(|(_, t)| t.clone()))
                .collect(),
        )
    }));
    let pinned: BTreeSet<InferVarId> = requirements
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
    let mut graph = simplify_type_pinning(compact_type_polarity_only(&Type::Tuple(parts)), &pinned);
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
    if names.order.is_empty() {
        return Some(body);
    }

    let params = names
        .order
        .iter()
        .enumerate()
        .map(|(i, v)| PolyParam {
            hole: u32::try_from(i).expect("a rendered type has fewer than 2³² parameters"),
            spelling: names.spelling(*v),
            bound_at: WrittenAt::default(),
            bound: match v {
                Named::Var(v) => st.bounds.get(v).map(|b| names.rename(b)),
                Named::Fresh(_) => None,
                Named::Meet(_) => unreachable!("a join or meet is not a parameter of its own"),
            },
        })
        .collect();
    let mut requires: Vec<PolyRequirement> = Vec::new();
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
        let (args, assoc_tys) = tys.split_at(stated.operands.len());
        let requirement = PolyRequirement {
            trait_: stated.trait_,
            args: args.to_vec(),
            assoc: stated
                .assoc
                .iter()
                .map(|(name, _)| *name)
                .zip(assoc_tys.iter().cloned())
                .collect(),
            at: WrittenAt::default(),
        };
        // A requirement about no parameter is one the definition already answered
        // at concrete types.
        if requirement.args.iter().any(|t| names.mentions_param(t))
            && !requires.contains(&requirement)
        {
            requires.push(requirement);
        }
    }
    Some(Type::Poly(Rc::new(PolyType {
        params,
        requires,
        body,
    })))
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
                if reach.levels.insert(v.uid, v.level).is_some() || v.level <= cutoff {
                    // A variable at or below the cutoff is the enclosing scope's: its
                    // bounds name nothing deeper, and its obligations are not this
                    // type's requirements.
                    return;
                }
                let bounds = v.bounds.borrow();
                pending.extend(bounds.lower().iter().map(|b| b.ty.clone()));
                pending.extend(bounds.upper().iter().map(|b| b.ty.clone()));
                for (obligation, _) in v.watches.borrow().iter() {
                    // An operand a copy inherited is the definition's own variable,
                    // whose obligations are the definition's, not this type's.
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
            None => crate::ccl::infer_var::lookup(id).map_or(0, |v| v.level),
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
        let p = TypeParam::fresh("_", self.cutoff + 1, None, WrittenAt::default());
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

    fn param(&self, named: Named, spelling: impl FnOnce() -> SmolStr) -> Rc<TypeParam> {
        if let Some(p) = self.params.borrow().get(&named) {
            return Rc::clone(p);
        }
        let p = TypeParam::fresh(spelling(), self.st.cutoff + 1, None, WrittenAt::default());
        self.params.borrow_mut().insert(named, Rc::clone(&p));
        p
    }

    /// `ty` with every placeholder replaced by the parameter it names, or by a
    /// parameter spelled as the join or meet it stands for.
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
            *ty = Type::Param(self.param(named, || match placeholder {
                Placeholder::Meet(join, vars, content) => {
                    let mut operands: Vec<String> = vars
                        .iter()
                        .map(|v| self.spelling(Named::Var(*v)).to_string())
                        .collect();
                    operands.extend(content.iter().map(|c| self.rename(c).to_string()));
                    SmolStr::from(operands.join(if *join { " ∨ " } else { " ∧ " }))
                }
                Placeholder::Var(_) | Placeholder::Fresh => self.spelling(named),
            }));
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
