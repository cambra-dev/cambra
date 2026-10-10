//! Nominal types: the declaration a [`Type::Nominal`] names.
//!
//! A `type` declaration (`docs/chl-spec.md`, "6.8 Nominal types and methods \[Decided\]")
//! lowers to one [`NominalDecl`]. Inference relates two applications of it by the variance
//! of each parameter, and relates it to no other type. A nominal type keeps its name to
//! operator conversion, and a pass that reads a value's shape reads it as the
//! [`representation`](NominalDecl::representation): the closed variant whose tags are the
//! constructor names and whose payloads are the constructors' parameter types. See
//! `src/ccl/design/nominal-types.md`.

use std::cell::OnceCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use chl_parser::ast::Span;
use smol_str::SmolStr;

use crate::ccl::ccl_utils::strip_refinements;
use crate::ccl::{BaseType, FieldKey, FunKind, Type, TypeKind, TypeParam, TypeParamId};

/// Globally unique identity of a [`NominalDecl`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NominalId(pub u32);

static NOMINAL_COUNTER: AtomicU32 = AtomicU32::new(0);

/// A declared nominal type. Equality, ordering and hashing are by `id`.
///
/// Lowering creates the declaration from its head before it lowers any type that names
/// it, and defines its constructors once every declaration of the module has a head
/// ([`NominalDecl::define`]). A [`Type::Nominal`] holds it by `Rc`, so the declarations
/// a program reaches form a graph through their constructors' parameter types. Lowering
/// refuses a cycle in that graph before defining any declaration on it, so no `Rc` cycle
/// forms.
pub struct NominalDecl {
    pub id: NominalId,
    /// The name the declaration binds.
    pub name: SmolStr,
    /// The type parameters, declared ([`TypeParam::declared`]). A constructor's parameter
    /// types name them; [`NominalDecl::instantiate`] replaces them with an application's
    /// arguments.
    pub params: Vec<Rc<TypeParam>>,
    /// The declaration's name, for diagnostics naming it.
    pub span: Span,
    /// Whether the declaration is the single-constructor form `type N = R`, the one form
    /// that declares `N::extract` (`docs/chl-spec.md`, "The single-constructor form").
    pub declares_extract: bool,
    body: OnceCell<NominalBody>,
}

/// What a [`NominalDecl`] declares after its head.
#[derive(Debug)]
pub struct NominalBody {
    /// In declaration order. A value names its constructor by name, so the order is only
    /// for display.
    pub ctors: Vec<NominalCtor>,
    /// One per type parameter, read off the constructors' parameter types.
    pub variances: Vec<Variance>,
}

/// One constructor of a [`NominalDecl`].
#[derive(Debug)]
pub struct NominalCtor {
    pub name: SmolStr,
    pub span: Span,
    /// The declared parameters: the name each is documented by, and its type.
    pub params: Vec<(Option<SmolStr>, Type)>,
}

impl NominalCtor {
    /// The type of the one argument the constructor takes: `Unit` for none, the
    /// parameter's type for one, and their tuple for several. `Shape::rect(w: Int, h: Int)`
    /// takes `{Int, Int}`.
    pub fn payload(&self) -> Type {
        match self.params.as_slice() {
            [] => Type::Base(BaseType::Unit),
            [(_, ty)] => ty.clone(),
            params => Type::Tuple(params.iter().map(|(_, ty)| ty.clone()).collect()),
        }
    }
}

/// How an application of a [`NominalDecl`] varies with one of its type arguments
/// (`docs/chl-spec.md`, "Declaring a nominal type").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Variance {
    Covariant,
    Contravariant,
    Invariant,
}

impl Variance {
    /// The variance of a position reached through `inner` from a position of variance
    /// `self`.
    pub fn compose(self, inner: Variance) -> Variance {
        match (self, inner) {
            (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
            (a, b) if a == b => Variance::Covariant,
            _ => Variance::Contravariant,
        }
    }

    /// The polarity a solver walk reads an argument of this variance at, inside a position
    /// of polarity `pol`: flipped for a contravariant argument, as a function's domain is,
    /// and kept for a covariant or an invariant one, as a history's children keep it.
    pub fn polarity(self, pol: bool) -> bool {
        match self {
            Variance::Contravariant => !pol,
            Variance::Covariant | Variance::Invariant => pol,
        }
    }

    /// The variance of a parameter that occurs at both `self` and `other`.
    fn join(self, other: Variance) -> Variance {
        if self == other {
            self
        } else {
            Variance::Invariant
        }
    }
}

impl NominalDecl {
    /// The declaration of `name`, with no constructors yet.
    pub fn declared(
        name: SmolStr,
        params: Vec<Rc<TypeParam>>,
        span: Span,
        declares_extract: bool,
    ) -> Rc<NominalDecl> {
        Rc::new(NominalDecl {
            id: NominalId(NOMINAL_COUNTER.fetch_add(1, Ordering::Relaxed)),
            name,
            params,
            span,
            declares_extract,
            body: OnceCell::new(),
        })
    }

    /// `self` applied to its own type parameters: the type of `self` inside a function
    /// the declaration declares, such as `extract`.
    pub fn applied_to_params(self: &Rc<Self>) -> Type {
        let args = self
            .params
            .iter()
            .map(|p| Type::Param(Rc::clone(p)))
            .collect();
        Type::Nominal(Rc::clone(self), args)
    }

    /// Define the constructors, computing each parameter's variance.
    ///
    /// Every declaration the constructors' parameter types name must already be defined:
    /// lowering defines them in dependency order.
    ///
    /// # Errors
    ///
    /// The type parameter that no constructor's parameter type names.
    ///
    /// # Panics
    ///
    /// On a declaration defined twice.
    pub fn define(&self, ctors: Vec<NominalCtor>) -> Result<(), Rc<TypeParam>> {
        let mut seen: HashMap<TypeParamId, Variance> = HashMap::new();
        for ctor in &ctors {
            for (_, ty) in &ctor.params {
                occurrences(ty, Variance::Covariant, &mut |id, v| {
                    seen.entry(id).and_modify(|w| *w = w.join(v)).or_insert(v);
                });
            }
        }
        let variances = self
            .params
            .iter()
            .map(|p| seen.get(&p.id).copied().ok_or_else(|| p.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let defined = self.body.set(NominalBody { ctors, variances });
        assert!(
            defined.is_ok(),
            "nominal type `{}` defined twice",
            self.name
        );
        Ok(())
    }

    /// The constructors and variances.
    ///
    /// # Panics
    ///
    /// Before [`define`](Self::define): lowering defines every declaration before anything
    /// reads one.
    pub fn body(&self) -> &NominalBody {
        self.body.get().unwrap_or_else(|| {
            panic!(
                "nominal type `{}` read before its constructors were defined",
                self.name
            )
        })
    }

    /// The constructor named `name`.
    pub fn ctor(&self, name: &str) -> Option<&NominalCtor> {
        self.body().ctors.iter().find(|c| c.name == name)
    }

    /// `ty`, a type the declaration states, with each type parameter replaced by the
    /// matching one of `args`.
    pub fn instantiate(&self, ty: &Type, args: &[Type]) -> Type {
        assert_eq!(
            args.len(),
            self.params.len(),
            "`{}` applied to the wrong number of arguments",
            self.name
        );
        let map: HashMap<TypeParamId, &Type> = self.params.iter().map(|p| p.id).zip(args).collect();
        let mut out = ty.clone();
        replace_params(&mut out, &map);
        out
    }

    /// The representation of `self(args)`: the closed variant tagged by constructor name,
    /// each tag carrying its constructor's [`payload`](NominalCtor::payload). Tags are in
    /// name order, so the representation does not depend on the order of the
    /// declaration's lines.
    ///
    /// A payload carries no refinement of the declaration's. Each construction discharged
    /// them during inference, and the predicates the declaration holds were never typed:
    /// the constructor's function carries its own copy, which inference types
    /// (`lower::nominal`).
    pub fn representation(&self, args: &[Type]) -> Type {
        let mut arms: Vec<(FieldKey, Type)> = self
            .body()
            .ctors
            .iter()
            .map(|c| {
                let payload = strip_refinements(&self.instantiate(&c.payload(), args));
                (FieldKey::Name(c.name.clone()), payload)
            })
            .collect();
        arms.sort_by(|(a, _), (b, _)| a.cmp(b));
        Type::variant(arms)
    }

    /// The declarations the constructors' parameter types name directly.
    pub fn references(ctors: &[NominalCtor]) -> Vec<Rc<NominalDecl>> {
        let mut out: Vec<Rc<NominalDecl>> = Vec::new();
        for ctor in ctors {
            for (_, ty) in &ctor.params {
                collect_decls(ty, &mut out);
            }
        }
        out
    }
}

impl fmt::Debug for NominalDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.name, self.id.0)
    }
}

impl PartialEq for NominalDecl {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for NominalDecl {}
impl PartialOrd for NominalDecl {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for NominalDecl {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl std::hash::Hash for NominalDecl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Report each type parameter occurring in `ty`, with the variance of its position
/// relative to `at`, the variance of `ty`'s own position.
///
/// A compute function's domain is contravariant, a data function's is invariant
/// (`src/ccl/design/type-inference.md`, "Data domains are invariant"), and a codomain is
/// covariant. A `SubtypesOf` kind is ordered by its bound covariantly
/// (`constrain_type_kinds`), and a listed candidate is matched by equality, so it is
/// invariant. A history is invariant in both children ([`Type::History`]).
fn occurrences(ty: &Type, at: Variance, f: &mut dyn FnMut(TypeParamId, Variance)) {
    match ty {
        Type::Param(p) => f(p.id, at),
        Type::Fun {
            fun_kind,
            domain,
            codomain,
            ..
        } => {
            if let FunKind::Data(Some(witnesses)) = fun_kind {
                for w in witnesses.iter() {
                    match &w.type_kind() {
                        TypeKind::SubtypesOf(bound) => occurrences(bound, at, f),
                        TypeKind::Enumerated(candidates) => candidates
                            .iter()
                            .for_each(|c| occurrences(c, Variance::Invariant, f)),
                        TypeKind::UIntRanges | TypeKind::Type => {}
                    }
                }
            }
            let domain_variance = if fun_kind.resolved().is_data() {
                Variance::Invariant
            } else {
                Variance::Contravariant
            };
            occurrences(domain, at.compose(domain_variance), f);
            occurrences(codomain, at, f);
        }
        Type::History { value, domain, .. } => {
            occurrences(value, Variance::Invariant, f);
            occurrences(domain, Variance::Invariant, f);
        }
        Type::Nominal(decl, args) => {
            for (arg, v) in args.iter().zip(&decl.body().variances) {
                occurrences(arg, at.compose(*v), f);
            }
        }
        _ => ty.walk_children(|child| occurrences(child, at, f)),
    }
}

/// Replace each type parameter in `map` with its type, everywhere in `ty`.
fn replace_params(ty: &mut Type, map: &HashMap<TypeParamId, &Type>) {
    if let Type::Param(p) = ty
        && let Some(arg) = map.get(&p.id)
    {
        *ty = (*arg).clone();
        return;
    }
    ty.walk_children_mut(|child| replace_params(child, map));
}

fn collect_decls(ty: &Type, out: &mut Vec<Rc<NominalDecl>>) {
    if let Type::Nominal(decl, _) = ty
        && !out.contains(decl)
    {
        out.push(decl.clone());
    }
    ty.walk_children(|child| collect_decls(child, out));
}

#[cfg(test)]
mod tests {
    use super::*;
    use chl_parser::FileId;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// The variance `define` reads off one constructor whose single parameter has the type
    /// `shape` builds from the declaration's one type parameter.
    fn variance_of(shape: impl Fn(Type) -> Type) -> Result<Variance, String> {
        let t = TypeParam::declared("T");
        let decl = NominalDecl::declared(
            "N".into(),
            vec![t.clone()],
            Span::new(FileId::ROOT, 0, 0),
            false,
        );
        let ctor = NominalCtor {
            name: "c".into(),
            span: Span::new(FileId::ROOT, 0, 0),
            params: vec![(None, shape(Type::Param(t)))],
        };
        decl.define(vec![ctor])
            .map_err(|p| p.spelling.to_string())?;
        Ok(decl.body().variances[0])
    }

    #[test]
    fn a_payload_position_is_covariant() {
        assert_eq!(variance_of(|t| t), Ok(Variance::Covariant));
        assert_eq!(
            variance_of(|t| Type::Tuple(vec![int(), t])),
            Ok(Variance::Covariant)
        );
        assert_eq!(variance_of(Type::list_of), Ok(Variance::Covariant));
    }

    /// A compute function's domain flips, and flips back inside another domain.
    #[test]
    fn a_compute_domain_flips() {
        assert_eq!(
            variance_of(|t| Type::fun(t, int())),
            Ok(Variance::Contravariant)
        );
        assert_eq!(
            variance_of(|t| Type::fun(Type::fun(t, int()), int())),
            Ok(Variance::Covariant)
        );
    }

    /// A collection's domain is its data, so a parameter there is invariant, where a
    /// compute function's domain would make it contravariant.
    #[test]
    fn a_data_domain_is_invariant() {
        assert_eq!(
            variance_of(|t| Type::full_map_of(t, int())),
            Ok(Variance::Invariant)
        );
    }

    #[test]
    fn two_variances_join_to_invariant() {
        assert_eq!(
            variance_of(|t| Type::Tuple(vec![t.clone(), Type::fun(t, int())])),
            Ok(Variance::Invariant)
        );
    }

    /// A parameter inside another nominal type takes that type's parameter variance.
    #[test]
    fn a_nested_nominal_type_composes_its_variance() {
        let inner = |variance_shape: fn(Type) -> Type| {
            let u = TypeParam::declared("U");
            let decl = NominalDecl::declared(
                "In".into(),
                vec![u.clone()],
                Span::new(FileId::ROOT, 0, 0),
                false,
            );
            decl.define(vec![NominalCtor {
                name: "c".into(),
                span: Span::new(FileId::ROOT, 0, 0),
                params: vec![(None, variance_shape(Type::Param(u)))],
            }])
            .expect("U is used");
            decl
        };
        let contra = inner(|u| Type::fun(u, Type::Base(BaseType::Int)));
        assert_eq!(
            variance_of(|t| Type::fun(Type::Nominal(contra.clone(), vec![t]), int())),
            Ok(Variance::Covariant)
        );
    }

    #[test]
    fn an_unused_parameter_is_refused() {
        assert_eq!(variance_of(|_| int()), Err("T".to_string()));
    }
}
