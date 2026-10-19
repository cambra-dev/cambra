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

use chl_parser::ast::Span;
use smol_str::SmolStr;

use crate::ccl::ccl_utils::strip_refinements;
use crate::ccl::{BaseType, FieldKey, FunKind, Type, TypeKind, TypeParam, TypeParamId};

/// A declared nominal type, identified by the path of the module that declares it and its
/// name (`docs/chl-spec.md`, "Nominal type identity"). Equality, ordering and hashing are by
/// that pair, so the same source declares the same types in every compilation.
///
/// Two declarations a compilation holds never share a path: lowering refuses a second
/// declaration of a name. Two compilations can, and a declaration from one compares equal to
/// the same-named one from the other whatever their constructors, so whatever compares a
/// version's types with the next version's, as a reload does, compares the declarations'
/// bodies itself.
///
/// Lowering creates the declaration from its head before it lowers any type that names
/// it, and defines its constructors once every declaration of the module has a head
/// ([`NominalDecl::define`]). A [`Type::Nominal`] holds it by `Rc`, so the declarations
/// a program reaches form a graph through their constructors' parameter types. Lowering
/// refuses a cycle in that graph before defining any declaration on it, so no `Rc` cycle
/// forms.
pub struct NominalDecl {
    /// The path of the module that declares it: empty for the program's root module.
    pub module: Vec<SmolStr>,
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
///
/// A parameter is invariant in two ways, which relate differently at a join. One that
/// occurs at an **equality** position, a data function's domain, a history or a listed
/// candidate, is `Invariant`: both sides of a relation are one type there, so a join of
/// two applications whose arguments differ has no type, as one of two collections over
/// different domains has none. One that occurs at both polarities and at no equality
/// position is `Bipolar`: its argument has an input side, read by its negative
/// occurrences, and an output side, read by its positive ones ([`Type::Split`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Variance {
    Covariant,
    Contravariant,
    Bipolar,
    Invariant,
}

impl Variance {
    /// The variance of a position reached through `inner` from a position of variance
    /// `self`.
    pub fn compose(self, inner: Variance) -> Variance {
        match (self, inner) {
            (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
            (Variance::Bipolar, _) | (_, Variance::Bipolar) => Variance::Bipolar,
            (a, b) if a == b => Variance::Covariant,
            _ => Variance::Contravariant,
        }
    }

    /// The polarity a solver walk reads an argument of this variance at, inside a position
    /// of polarity `pol`: flipped for a contravariant argument, as a function's domain is,
    /// and kept for a covariant or an invariant one, as a history's children keep it. A
    /// bipolar argument is read at both, its output side at `pol` and its input side
    /// flipped ([`sides`]); this answers the output's.
    pub fn polarity(self, pol: bool) -> bool {
        match self {
            Variance::Contravariant => !pol,
            Variance::Covariant | Variance::Bipolar | Variance::Invariant => pol,
        }
    }

    /// The variance of a parameter that occurs at both `self` and `other`.
    fn join(self, other: Variance) -> Variance {
        match (self, other) {
            (a, b) if a == b => a,
            (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
            _ => Variance::Bipolar,
        }
    }
}

/// The input and output sides of an argument: a [`Type::Split`]'s two, and any other
/// type as both.
pub fn sides(arg: &Type) -> (&Type, &Type) {
    match arg {
        Type::Split { input, output } => (input, output),
        other => (other, other),
    }
}

/// The argument of a bipolar parameter whose sides are `input` and `output`: one type where
/// they agree, a [`Type::Split`] otherwise.
pub fn split(input: Type, output: Type) -> Type {
    if input == output {
        output
    } else {
        Type::Split {
            input: Box::new(input),
            output: Box::new(output),
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
        Self::declared_in(Vec::new(), name, params, span, declares_extract)
    }

    /// The declaration of `name` in the module at `module`, with no constructors yet.
    pub fn declared_in(
        module: Vec<SmolStr>,
        name: SmolStr,
        params: Vec<Rc<TypeParam>>,
        span: Span,
        declares_extract: bool,
    ) -> Rc<NominalDecl> {
        Rc::new(NominalDecl {
            module,
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

    /// The variance of each **side** of an application's arguments, positionally: a
    /// bipolar parameter's argument as its input side, contravariant, then its output side,
    /// covariant ([`sides`]), and every other parameter's as itself. The solver's
    /// compaction holds an application's arguments in this layout, so that a join merges
    /// each side at its own polarity.
    pub fn sided_variances(&self) -> Vec<Variance> {
        self.body()
            .variances
            .iter()
            .flat_map(|v| match v {
                Variance::Bipolar => vec![Variance::Contravariant, Variance::Covariant],
                other => vec![*other],
            })
            .collect()
    }

    /// The sides of an application's arguments, each with its variance, in the
    /// [`sided_variances`](Self::sided_variances) layout.
    pub fn sided_args<'a>(&self, args: &'a [Type]) -> Vec<(&'a Type, Variance)> {
        use Variance::{Bipolar, Contravariant, Covariant};
        let variances = &self.body().variances;
        debug_assert_eq!(args.len(), variances.len(), "one argument per parameter");
        let sided = |(t, v): (&'a Type, &Variance)| match v {
            Bipolar => vec![(sides(t).0, Contravariant), (sides(t).1, Covariant)],
            other => vec![(t, *other)],
        };
        args.iter().zip(variances).flat_map(sided).collect()
    }

    /// The constructor named `name`.
    pub fn ctor(&self, name: &str) -> Option<&NominalCtor> {
        self.body().ctors.iter().find(|c| c.name == name)
    }

    /// `ty`, a type the declaration states at a positive position, with each type parameter
    /// replaced by the matching one of `args`: a bipolar parameter by its argument's output
    /// side where it occurs positively and by its input side where it occurs negatively
    /// ([`sides`]).
    pub fn instantiate(&self, ty: &Type, args: &[Type]) -> Type {
        assert_eq!(
            args.len(),
            self.params.len(),
            "`{}` applied to the wrong number of arguments",
            self.name
        );
        let map: HashMap<TypeParamId, (&Type, &Type)> = self
            .params
            .iter()
            .map(|p| p.id)
            .zip(args.iter().map(sides))
            .collect();
        let mut out = ty.clone();
        replace_params(&mut out, true, &map);
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
    /// (`lower::nominal`). A refinement in `args` stays: the use that wrote it typed it.
    pub fn representation(&self, args: &[Type]) -> Type {
        let mut arms: Vec<(FieldKey, Type)> = self
            .body()
            .ctors
            .iter()
            .map(|c| {
                let payload = self.instantiate(&strip_refinements(&c.payload()), args);
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
        for segment in &self.module {
            write!(f, "{segment}::")?;
        }
        write!(f, "{}", self.name)
    }
}

impl NominalDecl {
    /// What identifies the declaration: its module's path, then its name.
    fn identity(&self) -> (&[SmolStr], &SmolStr) {
        (&self.module, &self.name)
    }
}

impl PartialEq for NominalDecl {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
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
        self.identity().cmp(&other.identity())
    }
}
impl std::hash::Hash for NominalDecl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
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

/// Replace each type parameter in `map` with its output side where it occurs at a positive
/// position and its input side at a negative one, `pol` being `ty`'s own.
///
/// The polarity follows [`occurrences`]: a compute function's domain flips it, and an
/// argument of a nominal type takes its parameter's variance. An equality position keeps
/// it; a parameter occurring there is not bipolar, so its two sides are one type.
fn replace_params(ty: &mut Type, pol: bool, map: &HashMap<TypeParamId, (&Type, &Type)>) {
    match ty {
        Type::Param(p) => {
            if let Some((input, output)) = map.get(&p.id) {
                *ty = if pol {
                    (*output).clone()
                } else {
                    (*input).clone()
                };
            }
        }
        Type::Fun {
            fun_kind,
            domain,
            codomain,
            ..
        } if !fun_kind.resolved().is_data() => {
            replace_params(domain, !pol, map);
            replace_params(codomain, pol, map);
        }
        Type::Nominal(decl, args) => {
            let variances = decl.body().variances.clone();
            for (arg, v) in args.iter_mut().zip(variances) {
                replace_params(arg, v.polarity(pol), map);
            }
        }
        Type::Split { input, output } => {
            replace_params(input, !pol, map);
            replace_params(output, pol, map);
        }
        _ => ty.walk_children_mut(|child| replace_params(child, pol, map)),
    }
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

    /// A parameter at both polarities is bipolar, and one at an equality position too is
    /// invariant.
    #[test]
    fn two_polarities_join_to_bipolar() {
        assert_eq!(
            variance_of(|t| Type::Tuple(vec![t.clone(), Type::fun(t, int())])),
            Ok(Variance::Bipolar)
        );
        assert_eq!(
            variance_of(|t| Type::Tuple(vec![t.clone(), Type::full_map_of(t, int())])),
            Ok(Variance::Invariant)
        );
    }

    /// Instantiating reads a bipolar parameter's output side at a positive occurrence and
    /// its input side at a negative one.
    #[test]
    fn instantiating_reads_each_side_where_it_occurs() {
        let t = TypeParam::declared("T");
        let decl = NominalDecl::declared(
            "Cell".into(),
            vec![t.clone()],
            Span::new(FileId::ROOT, 0, 0),
            false,
        );
        decl.define(vec![NominalCtor {
            name: "c".into(),
            span: Span::new(FileId::ROOT, 0, 0),
            params: vec![(None, Type::fun(Type::Param(t.clone()), Type::Param(t)))],
        }])
        .expect("`T` is used");
        let (input, output) = (Type::Base(BaseType::Bool), int());
        let arg = split(input.clone(), output.clone());
        assert_eq!(
            decl.instantiate(&decl.body().ctors[0].payload(), &[arg]),
            Type::fun(input, output)
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

    /// The representation drops the refinements the declaration's parameter types carry,
    /// which are untyped, and keeps those inside an argument, which the use typed.
    #[test]
    fn the_representation_keeps_only_its_arguments_refinements() {
        use crate::ccl::{Expr, Refinement, RefinementSet};
        let refine = |base: Type, by: &str| {
            let bool_ty = Type::Base(BaseType::Bool);
            Type::refined(
                base,
                RefinementSet::one(Refinement::born(Rc::new(Expr::var(by).with_ty(bool_ty)))),
            )
        };
        let span = Span::new(FileId::ROOT, 0, 0);
        let t = TypeParam::declared("T");
        let decl = NominalDecl::declared("N".into(), vec![t.clone()], span, false);
        decl.define(vec![NominalCtor {
            name: "c".into(),
            span,
            params: vec![(None, refine(int(), "declared")), (None, Type::Param(t))],
        }])
        .expect("`c` names `T`");
        let argument = refine(int(), "written");
        assert_eq!(
            decl.representation(std::slice::from_ref(&argument)),
            Type::variant(vec![(
                FieldKey::Name("c".into()),
                Type::Tuple(vec![int(), argument])
            )])
        );
    }

    #[test]
    fn an_unused_parameter_is_refused() {
        assert_eq!(variance_of(|_| int()), Err("T".to_string()));
    }
}
