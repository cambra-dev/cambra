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

use crate::ccl::ccl_utils::{free_names, strip_refinements};
use crate::ccl::constant::{ConstParam, ConstTerm, NoValue};
use crate::ccl::{
    BaseType, FieldKey, FunKind, Label, Name, Refinement, RefinementSet, Type, TypeKind, TypeParam,
    TypeParamId, V_NONE, V_SOME,
};

/// The name the compiler-provided `Option` declaration binds.
pub const OPTION: &str = "Option";

/// The path of the module the compiler-provided declarations belong to.
const STD: &str = "std";

thread_local! {
    /// `Option`, built once per thread. Its identity is its path, `std::Option`, so this
    /// is a cache: any two builds compare equal.
    static OPTION_DECL: Rc<NominalDecl> = option_declaration();
}

/// `type Option(T): none, some(T)` in `std`, with the constructor names [`V_NONE`] and
/// [`V_SOME`] that the runtime builds when it answers a checked lookup.
fn option_declaration() -> Rc<NominalDecl> {
    let span = Span::new(chl_parser::FileId::ROOT, 0, 0);
    let t = TypeParam::declared("T");
    let decl = NominalDecl::declared_in(
        vec![SmolStr::new_static(STD)],
        OPTION.into(),
        vec![Rc::clone(&t)],
        span,
        false,
    );
    decl.define(vec![
        NominalCtor::unwritten(V_NONE.name().into(), span, Vec::new()),
        NominalCtor::unwritten(V_SOME.name().into(), span, vec![(None, Type::Param(t))]),
    ])
    .expect("`some` names `T`");
    decl
}

/// The compiler-provided `Option(T)` (`docs/chl-spec.md`, "9.16 The std root"), which the
/// checked lookup answers and `Option(T)` in an annotation names.
///
/// It has no source, so its spans are empty, at the start of the root file. Lowering
/// refuses every program that would point a diagnostic at one: a declaration of the name
/// `Option`, and an associated function of it.
///
/// Its method `is_none` is built by lowering (`bind_is_none` in `src/ccl/lower/nominal.rs`).
/// The interpreter declares the same members (`collect_types` in `chl-interp/src/eval.rs`),
/// and `option_values` in `tests/it/differential_interp.rs` checks that the two agree.
pub fn option() -> Rc<NominalDecl> {
    OPTION_DECL.with(Rc::clone)
}

/// The names of the two types bounding the variables that stand for clauses: every effect is
/// below `Effect`, and every requirement below `Context` (`docs/chl-spec.md`, "6.9 Effects and
/// requirements \[Decided\]").
pub const EFFECT: &str = "Effect";
pub const CONTEXT: &str = "Context";

thread_local! {
    static EFFECT_DECL: Rc<NominalDecl> = clause_bound_declaration(EFFECT);
    static CONTEXT_DECL: Rc<NominalDecl> = clause_bound_declaration(CONTEXT);
}

/// `type name` in `std` with no constructor: no value has an effect or a requirement type.
fn clause_bound_declaration(name: &str) -> Rc<NominalDecl> {
    let decl = NominalDecl::declared_in(
        vec![SmolStr::new_static(STD)],
        name.into(),
        Vec::new(),
        Span::new(chl_parser::FileId::ROOT, 0, 0),
        false,
    );
    decl.define(Vec::new())
        .expect("a declaration with no constructor names no parameter");
    decl
}

/// The compiler-provided `Effect`, which a variable standing for a `causes` clause is bounded
/// by (`docs/chl-spec.md`, "Kinds and bounds").
pub fn effect() -> Rc<NominalDecl> {
    EFFECT_DECL.with(Rc::clone)
}

/// The compiler-provided `Context`, which a variable standing for a `requires` clause is
/// bounded by.
pub fn context() -> Rc<NominalDecl> {
    CONTEXT_DECL.with(Rc::clone)
}

/// The tag a value built by the constructor `ctor` carries once nominal types erase: the
/// constructor's name, as a label of the root's namespace whichever module declares the
/// type. Construction, patterns and erasure all build it here, so they agree, and the
/// runtime's checked lookup builds `Option`'s the same way ([`V_SOME`]).
pub fn ctor_tag(ctor: &str) -> Label {
    Label::new(ctor)
}

/// The compiler-provided declaration `name` names, if any.
pub fn builtin(name: &str) -> Option<Rc<NominalDecl>> {
    (name == OPTION).then(option)
}

/// A declared nominal type, identified by the path of the module that declares it, its name,
/// and the arguments of its implicit parameters (`docs/chl-spec.md`, "Nominal type
/// identity"). Equality and hashing are by those, so the same source declares the same types
/// in every compilation. A declaration has no order, since its arguments are types; a map
/// keyed by one is a [`DeclMap`].
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
    /// Shared with every instance of the declaration ([`NominalDecl::substituted`]).
    body: Rc<OnceCell<NominalBody>>,
    /// The type parameters of the declaring module that the type reaches, through its
    /// constructors and its associated functions, set once that module has lowered. With
    /// the module's path and the type's name, their arguments identify the type
    /// (`docs/chl-spec.md`, "Nominal type identity"). Shared with every instance.
    implicit: Rc<OnceCell<Vec<Rc<TypeParam>>>>,
    /// The argument each of [`Self::implicit`] takes in this instance, or `None` for the
    /// declaration as its own module names it, where each is the parameter itself.
    implicit_args: Option<Vec<Type>>,
    /// The `const` parameters of the declaring module that the type reaches, through its
    /// constructors' refinements and its associated functions, set once that module has
    /// lowered. They identify the type alongside [`Self::implicit`]. Shared with every
    /// instance.
    implicit_consts: Rc<OnceCell<Vec<ConstParam>>>,
    /// The argument each of [`Self::implicit_consts`] takes in this instance, as
    /// [`Self::implicit_args`] holds the type parameters'.
    const_args: Option<Vec<ConstTerm>>,
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
    /// Each parameter's order, as the declaration writes its type, positionally.
    pub orders: Vec<WrittenOrder>,
}

/// How a value of a type a declaration writes is ordered (`docs/chl-spec.md`, "Equality and
/// order"): each product by its fields in the order the declaration writes them.
///
/// A record type has no order of its own, so the order of a record in a constructor's
/// parameter types is the declaration's, kept here rather than read off [`Type::Record`],
/// whose fields no pass keeps in any order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WrittenOrder {
    /// By the type's own order: a base type, a type parameter or a nominal type. A type
    /// with no order, such as a function, is one too, and no `Orderable` instance accepts
    /// it, nor a record a type argument names in place of a type parameter.
    Whole,
    /// A product, by its fields in this order, each by its own order.
    Fields(Vec<(FieldKey, WrittenOrder)>),
    /// A record the declaration does not write, reached through an alias: it has no order.
    Unordered,
}

impl WrittenOrder {
    /// The order of `ty` where no declaration writes it: a tuple by position, and a record
    /// none.
    pub fn of_type(ty: &Type) -> WrittenOrder {
        match ty.peel_refinements() {
            Type::Tuple(elems) => WrittenOrder::Fields(
                elems
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (FieldKey::Index(i), WrittenOrder::of_type(t)))
                    .collect(),
            ),
            Type::Record(_) => WrittenOrder::Unordered,
            _ => WrittenOrder::Whole,
        }
    }

    /// Whether every product this order reaches has an order.
    pub fn is_ordered(&self) -> bool {
        match self {
            WrittenOrder::Whole => true,
            WrittenOrder::Fields(fields) => fields.iter().all(|(_, o)| o.is_ordered()),
            WrittenOrder::Unordered => false,
        }
    }
}

impl NominalCtor {
    /// A constructor whose parameter types no declaration writes, ordered as
    /// [`WrittenOrder::of_type`] reads them.
    pub fn unwritten(name: SmolStr, span: Span, params: Vec<(Option<SmolStr>, Type)>) -> Self {
        let orders = params
            .iter()
            .map(|(_, t)| WrittenOrder::of_type(t))
            .collect();
        NominalCtor {
            name,
            span,
            params,
            orders,
        }
    }

    /// The order of [`payload`](Self::payload): its one parameter's, or its parameters' by
    /// position.
    pub fn payload_order(&self) -> WrittenOrder {
        match self.orders.as_slice() {
            [] => WrittenOrder::Whole,
            [one] => one.clone(),
            several => WrittenOrder::Fields(
                several
                    .iter()
                    .enumerate()
                    .map(|(i, o)| (FieldKey::Index(i), o.clone()))
                    .collect(),
            ),
        }
    }

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

    /// The payload a pattern destructures: [`Self::payload`] without the refinements whose
    /// predicates read a name other than the refined value. Such a predicate reads a `const`
    /// parameter of the declaring module, which only the constructor's own function, bound
    /// where the name is in scope, can read. Each construction discharged it there.
    pub fn destructured(&self) -> Type {
        fn drop_named(ty: &mut Type) {
            if let Type::Refinement(base, refinements) = ty {
                let kept: Vec<Refinement> = refinements
                    .iter()
                    .filter(|r| free_names(&r.predicate).iter().all(Name::is_elem))
                    .cloned()
                    .collect();
                if kept.len() != refinements.len() {
                    let mut base = std::mem::replace(&mut **base, Type::Hole);
                    drop_named(&mut base);
                    *ty = if kept.is_empty() {
                        base
                    } else {
                        let mut set = RefinementSet::new();
                        set.extend(kept);
                        Type::refined(base, set)
                    };
                    return;
                }
            }
            ty.walk_children_mut(drop_named);
        }
        let mut ty = self.payload();
        drop_named(&mut ty);
        ty
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
            body: Rc::new(OnceCell::new()),
            implicit: Rc::new(OnceCell::new()),
            implicit_args: None,
            implicit_consts: Rc::new(OnceCell::new()),
            const_args: None,
        })
    }

    /// Record the declaring module's type parameters the type reaches ([`Self::implicit`]).
    ///
    /// # Panics
    ///
    /// When recorded twice.
    pub fn set_implicit(&self, params: Vec<Rc<TypeParam>>) {
        let set = self.implicit.set(params);
        assert!(
            set.is_ok(),
            "`{}`'s implicit parameters set twice",
            self.name
        );
    }

    /// The declaring module's type parameters the type reaches: empty until that module has
    /// lowered.
    pub fn implicit(&self) -> &[Rc<TypeParam>] {
        self.implicit.get().map_or(&[], Vec::as_slice)
    }

    /// The argument each implicit parameter takes: the parameter itself in the declaration
    /// as its module names it.
    pub fn implicit_args(&self) -> Vec<Type> {
        match &self.implicit_args {
            Some(args) => args.clone(),
            None => self
                .implicit()
                .iter()
                .map(|p| Type::Param(Rc::clone(p)))
                .collect(),
        }
    }

    /// The instance whose implicit arguments are this one's after `substitute`, or `None`
    /// when `substitute` leaves them unchanged. A run or an import reaches the type through
    /// it, so two imports or runs given different arguments reach two types.
    pub fn substituted(&self, substitute: &mut dyn FnMut(&mut Type)) -> Option<Rc<NominalDecl>> {
        let before = self.implicit_args();
        let mut after = before.clone();
        after.iter_mut().for_each(&mut *substitute);
        (after != before).then(|| {
            Rc::new(NominalDecl {
                implicit_args: Some(after),
                ..self.instance()
            })
        })
    }

    /// Record the declaring module's `const` parameters the type reaches
    /// ([`Self::implicit_consts`]).
    ///
    /// # Panics
    ///
    /// When recorded twice.
    pub fn set_implicit_consts(&self, params: Vec<ConstParam>) {
        let set = self.implicit_consts.set(params);
        assert!(
            set.is_ok(),
            "`{}`'s implicit `const` parameters set twice",
            self.name
        );
    }

    /// The declaring module's `const` parameters the type reaches: empty until that module
    /// has lowered.
    pub fn implicit_consts(&self) -> &[ConstParam] {
        self.implicit_consts.get().map_or(&[], Vec::as_slice)
    }

    /// The term each of [`Self::implicit_consts`] takes: the parameter itself in the
    /// declaration as its module names it.
    pub fn const_args(&self) -> Vec<ConstTerm> {
        match &self.const_args {
            Some(args) => args.clone(),
            None => self
                .implicit_consts()
                .iter()
                .cloned()
                .map(ConstTerm::Param)
                .collect(),
        }
    }

    /// The instance whose `const` arguments are this one's with each parameter `values`
    /// maps replaced by its term, or `None` when that changes none of them.
    ///
    /// # Errors
    ///
    /// An argument the substitution leaves with no value, such as one dividing by zero.
    pub fn substituted_consts(
        &self,
        values: &HashMap<TypeParamId, ConstTerm>,
    ) -> Result<Option<Rc<NominalDecl>>, NoValue> {
        let before = self.const_args();
        let after = before
            .iter()
            .map(|term| term.substituted(values))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((after != before).then(|| {
            Rc::new(NominalDecl {
                const_args: Some(after),
                ..self.instance()
            })
        }))
    }

    /// A copy of `self` sharing its body and its implicit parameters, for an instance to
    /// replace the arguments of.
    fn instance(&self) -> NominalDecl {
        NominalDecl {
            module: self.module.clone(),
            name: self.name.clone(),
            params: self.params.clone(),
            span: self.span,
            declares_extract: self.declares_extract,
            body: Rc::clone(&self.body),
            implicit: Rc::clone(&self.implicit),
            implicit_args: self.implicit_args.clone(),
            implicit_consts: Rc::clone(&self.implicit_consts),
            const_args: self.const_args.clone(),
        }
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

    /// The type's name as a diagnostic writes it: qualified by its module, `shop::Price`,
    /// unless the root or the compiler declares it, whose types a program names bare. An
    /// instance's module is written with its implicit arguments, as an import or a run
    /// passes them: `shop(Receipt=stripe::Receipt)::Order`. The root has one run, so its
    /// instances are written bare too.
    pub fn spelled(&self) -> String {
        if self.module.is_empty() || self.is_builtin() {
            return self.name.to_string();
        }
        let module = self.module.join("::");
        if self.is_instance() {
            format!("{module}({})::{}", self.implicit_spelling(), self.name)
        } else {
            format!("{module}::{}", self.name)
        }
    }

    /// Whether the compiler provides the declaration: one [`builtin`] names, or a bound of
    /// the variables standing for clauses, which no type annotation names ([`effect`],
    /// [`context`]).
    pub fn is_builtin(&self) -> bool {
        builtin(&self.name).is_some_and(|b| *b == *self)
            || *self == *effect()
            || *self == *context()
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
        let implicit_args = self.implicit_args();
        let map: HashMap<TypeParamId, (&Type, &Type)> = self
            .params
            .iter()
            .map(|p| p.id)
            .zip(args.iter().map(sides))
            .chain(
                self.implicit()
                    .iter()
                    .map(|p| p.id)
                    .zip(implicit_args.iter().map(|a| (a, a))),
            )
            .collect();
        let mut out = ty.clone();
        replace_params(&mut out, true, &map);
        // A type of the module that reaches the same `const` parameters names them as its
        // own module does, so it takes this instance's arguments too.
        let consts: HashMap<TypeParamId, ConstTerm> = self
            .implicit_consts()
            .iter()
            .map(|p| p.id)
            .zip(self.const_args())
            .collect();
        if self.const_args.is_some() {
            replace_consts(&mut out, &consts);
        }
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
                (FieldKey::Name(ctor_tag(&c.name)), payload)
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
        write!(f, "{}", self.name)?;
        if self.is_instance() {
            write!(f, "{}", self.implicit_spelling())?;
        }
        Ok(())
    }
}

impl NominalDecl {
    /// What identifies the declaration: its module's path, its name, and its implicit
    /// arguments, the types and then the `const` terms.
    fn identity(&self) -> (&[SmolStr], &SmolStr, Vec<Type>, Vec<ConstTerm>) {
        (
            &self.module,
            &self.name,
            self.implicit_args(),
            self.const_args(),
        )
    }

    /// Whether this is an instance, reached through a run or an import, rather than the
    /// declaration as its own module names it.
    fn is_instance(&self) -> bool {
        self.implicit_args.is_some() || self.const_args.is_some()
    }

    /// The implicit arguments of an instance, as a diagnostic writes them after its
    /// module: `Receipt=stripe::Receipt, max_rate=30`.
    fn implicit_spelling(&self) -> String {
        let types = self
            .implicit()
            .iter()
            .zip(self.implicit_args())
            .map(|(p, a)| format!("{}={a}", p.spelling));
        let consts = self
            .implicit_consts()
            .iter()
            .zip(self.const_args())
            .map(|(p, a)| format!("{}={a}", p.spelling));
        let args: Vec<String> = types.chain(consts).collect();
        args.join(", ")
    }
}

impl PartialEq for NominalDecl {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for NominalDecl {}
impl std::hash::Hash for NominalDecl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}

/// A map keyed by nominal type, in the order its entries were inserted. A type has no
/// order: two instances compare by their implicit arguments, which are types, and a type
/// has equality but no order. So the map finds a key by equality, and compares two maps
/// as sets of entries. A position of a type holds one type, or two when it has none, so the
/// linear search costs nothing.
#[derive(Debug, Clone)]
pub struct DeclMap<V>(Vec<(Rc<NominalDecl>, V)>);

impl<V> Default for DeclMap<V> {
    fn default() -> Self {
        DeclMap(Vec::new())
    }
}

impl<V> DeclMap<V> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get(&self, decl: &NominalDecl) -> Option<&V> {
        self.0.iter().find(|(d, _)| **d == *decl).map(|(_, v)| v)
    }

    pub fn get_mut(&mut self, decl: &NominalDecl) -> Option<&mut V> {
        self.0
            .iter_mut()
            .find(|(d, _)| **d == *decl)
            .map(|(_, v)| v)
    }

    /// Insert `value` under `decl`, replacing the value an equal key held in its place.
    pub fn insert(&mut self, decl: Rc<NominalDecl>, value: V) {
        match self.get_mut(&decl) {
            Some(held) => *held = value,
            None => self.0.push((decl, value)),
        }
    }

    pub fn remove(&mut self, decl: &NominalDecl) -> Option<V> {
        let at = self.0.iter().position(|(d, _)| **d == *decl)?;
        Some(self.0.remove(at).1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<NominalDecl>, &V)> {
        self.0.iter().map(|(d, v)| (d, v))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Rc<NominalDecl>, &mut V)> {
        self.0.iter_mut().map(|(d, v)| (&*d, v))
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.iter().map(|(_, v)| v)
    }
}

impl<V: PartialEq> PartialEq for DeclMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().all(|(d, v)| other.get(d) == Some(v))
    }
}

impl<V, const N: usize> From<[(Rc<NominalDecl>, V); N]> for DeclMap<V> {
    fn from(entries: [(Rc<NominalDecl>, V); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl<V> FromIterator<(Rc<NominalDecl>, V)> for DeclMap<V> {
    fn from_iter<I: IntoIterator<Item = (Rc<NominalDecl>, V)>>(entries: I) -> Self {
        let mut map = DeclMap::default();
        for (decl, value) in entries {
            map.insert(decl, value);
        }
        map
    }
}

impl<V> IntoIterator for DeclMap<V> {
    type Item = (Rc<NominalDecl>, V);
    type IntoIter = std::vec::IntoIter<(Rc<NominalDecl>, V)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, V> IntoIterator for &'a DeclMap<V> {
    type Item = (&'a Rc<NominalDecl>, &'a V);
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, (Rc<NominalDecl>, V)>,
        fn(&'a (Rc<NominalDecl>, V)) -> (&'a Rc<NominalDecl>, &'a V),
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(d, v)| (d, v))
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
        Type::History { .. } => {
            let (domain, value, _) = ty.history_parts().expect("matched a history");
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
            if let Some(instance) = decl.substituted(&mut |arg| replace_params(arg, pol, map)) {
                *decl = instance;
            }
        }
        Type::Split { input, output } => {
            replace_params(input, !pol, map);
            replace_params(output, pol, map);
        }
        _ => ty.walk_children_mut(|child| replace_params(child, pol, map)),
    }
}

/// `ty` with each nominal type it names, at any depth, the instance whose `const` arguments
/// read `consts`'s terms for the parameters `consts` maps. An argument left with no value
/// keeps its term, as `substitute_decl` keeps it, and is reported where its run is created.
fn replace_consts(ty: &mut Type, consts: &HashMap<TypeParamId, ConstTerm>) {
    if let Type::Nominal(decl, _) = ty
        && let Ok(Some(instance)) = decl.substituted_consts(consts)
    {
        *decl = instance;
    }
    ty.walk_children_mut(|child| replace_consts(child, consts));
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

    /// Two instances whose implicit arguments are equal types are one key of a [`DeclMap`],
    /// though each argument's refinement was built on its own, and so prints differently.
    #[test]
    fn a_decl_map_finds_an_equal_instance() {
        use crate::ccl::{BinOpKind, CompareKind, Expr, Lit, Name, Refinement};
        let receipt = TypeParam::declared("Receipt");
        let decl = NominalDecl::declared(
            "Order".into(),
            Vec::new(),
            Span::new(FileId::ROOT, 0, 0),
            false,
        );
        decl.set_implicit(vec![receipt.clone()]);
        let positive = || {
            let predicate = Expr::binop(
                Expr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Greater),
                Expr::lit(Lit::Int(0)),
            );
            Type::refined_one(int(), Refinement::born(Rc::new(predicate)))
        };
        let instance = |argument: Type| {
            decl.substituted(&mut |arg| {
                if *arg == Type::Param(receipt.clone()) {
                    *arg = argument.clone();
                }
            })
            .expect("the argument replaces the parameter")
        };
        let (a, b) = (instance(positive()), instance(positive()));
        assert_eq!(a, b);
        assert_ne!(
            format!("{:?}", a.implicit_args()),
            format!("{:?}", b.implicit_args())
        );
        let mut map = DeclMap::default();
        map.insert(a, 1);
        map.insert(Rc::clone(&b), 2);
        assert_eq!(map.len(), 1);
        assert_eq!(map.get(&b), Some(&2));
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
        let ctor = NominalCtor::unwritten(
            "c".into(),
            Span::new(FileId::ROOT, 0, 0),
            vec![(None, shape(Type::Param(t)))],
        );
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
        decl.define(vec![NominalCtor::unwritten(
            "c".into(),
            Span::new(FileId::ROOT, 0, 0),
            vec![(None, Type::fun(Type::Param(t.clone()), Type::Param(t)))],
        )])
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
            decl.define(vec![NominalCtor::unwritten(
                "c".into(),
                Span::new(FileId::ROOT, 0, 0),
                vec![(None, variance_shape(Type::Param(u)))],
            )])
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
        decl.define(vec![NominalCtor::unwritten(
            "c".into(),
            span,
            vec![(None, refine(int(), "declared")), (None, Type::Param(t))],
        )])
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
