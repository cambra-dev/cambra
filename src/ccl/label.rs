//! Record field labels and variant tags.

use crate::ccl::names::{RunPath, SharedImport};
use crate::chl_parser::ModulePath;
use smol_str::SmolStr;
use std::fmt;

/// A record field label or a variant tag: a spelling and the module it belongs
/// to (`docs/chl-spec.md`, "9.12 Field labels and tags belong to a module").
///
/// Two labels are one label when both the spelling and the module agree. The
/// module is `None` for a label of the root module, and the root shares that
/// namespace with two kinds of label no module writes:
///
/// - the labels the compiler builds for itself, such as the decision record's
///   `commit` and `writes`, which no source can name;
/// - the tags of a compiler-provided nominal type's constructors, `Option`'s `some` and
///   `none`, which the runtime builds too.
///
/// A declared nominal type's constructor tags belong to the declaration
/// ([`Label::in_decl`]), so a value names the declaration it was built under, which is
/// how it compares in that declaration's order at run time.
///
/// A run's top-level mutable variable is labeled in its run instead
/// ([`Label::in_run`]), and a shared import's in the shared import
/// ([`Label::in_import`]). That label is the variable's field in its store or its
/// loop's history, which no source writes, and it keeps the variables of two runs,
/// or two shared imports, of one module apart.
///
/// Labels order by spelling, then by module, so a record or variant written in
/// one module keeps the order of its spellings.
///
/// A constructor's tag carries its declaration ([`Label::in_decl`]), which is not part of the
/// tag's identity: a nominal value meets only its own type's constructors and patterns, so its
/// spelling and module already tell its tags apart. Equality, hashing and order leave it out,
/// and a comparison of the value reads it ([`Label::decl`]).
#[derive(Clone)]
pub struct Label {
    name: SmolStr,
    space: Option<Space>,
}

impl Label {
    /// The part of the label that is its identity: everything but a constructor's declaration.
    fn identity(&self) -> (&SmolStr, Option<&Space>) {
        let space = match &self.space {
            Some(Space::Decl(_)) | None => None,
            Some(space) => Some(space),
        };
        (&self.name, space)
    }
}

impl PartialEq for Label {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}

impl Eq for Label {}

impl std::hash::Hash for Label {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}

impl PartialOrd for Label {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Label {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

/// What a label belongs to, when not the root's namespace.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Space {
    Module(ModulePath),
    Run(RunPath),
    Import(std::sync::Arc<ImportSpace>),
    Decl(crate::ccl::nominal::DeclId),
}

/// The shared import a label belongs to: its spelling, which is its identity, and
/// the shared import itself for a label compilation built.
///
/// A store keys its variables by [`Label::runtime_key`], which a store resumed by
/// another version reads back ([`Label::from_runtime_key`]), and a type argument
/// has no identity across compilations but its spelling ([`SharedImport`]'s
/// arguments). So the spelling is what the label is, and a label read back from a
/// key has no shared import.
#[derive(Clone)]
struct ImportSpace {
    spelled: SmolStr,
    shared: Option<SharedImport>,
}

impl PartialEq for ImportSpace {
    fn eq(&self, other: &Self) -> bool {
        self.spelled == other.spelled
    }
}

impl Eq for ImportSpace {}

impl PartialOrd for ImportSpace {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ImportSpace {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.spelled.cmp(&other.spelled)
    }
}

impl std::hash::Hash for ImportSpace {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.spelled.hash(state);
    }
}

impl Label {
    /// The root module's label spelled `name`.
    pub fn new(name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        debug_assert_spelling(&name);
        Label { name, space: None }
    }

    /// [`Label::new`] for a spelling known at compile time, so a label the
    /// compiler builds for itself can be a constant.
    pub const fn fixed(name: &'static str) -> Self {
        Label {
            name: SmolStr::new_static(name),
            space: None,
        }
    }

    /// The label spelled `name` that belongs to `module`.
    pub fn in_module(module: ModulePath, name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        debug_assert_spelling(&name);
        Label {
            name,
            space: Some(Space::Module(module)),
        }
    }

    /// The tag of the constructor spelled `name` of the declaration `decl`
    /// ([`crate::ccl::nominal::NominalDecl::tag`]).
    pub fn in_decl(decl: crate::ccl::nominal::DeclId, name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        debug_assert_spelling(&name);
        Label {
            name,
            space: Some(Space::Decl(decl)),
        }
    }

    /// The declaration whose constructor's tag the label is, or `None` for any other label
    /// ([`Label::in_decl`]).
    pub fn decl(&self) -> Option<crate::ccl::nominal::DeclId> {
        match &self.space {
            Some(Space::Decl(decl)) => Some(*decl),
            _ => None,
        }
    }

    /// The label spelled `name` of a top-level mutable variable of the run at `run`
    /// ([`crate::ccl::Name::field_key`]).
    pub fn in_run(run: RunPath, name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        debug_assert_spelling(&name);
        Label {
            name,
            space: Some(Space::Run(run)),
        }
    }

    /// The label spelled `name` of a top-level induction variable of the shared import
    /// `shared` ([`crate::ccl::Name::field_key`]).
    pub fn in_import(shared: SharedImport, name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        debug_assert_spelling(&name);
        Label {
            name,
            space: Some(Space::Import(std::sync::Arc::new(ImportSpace {
                spelled: smol_str::format_smolstr!("{shared}"),
                shared: Some(shared),
            }))),
        }
    }

    /// The label whose [`runtime_key`](Self::runtime_key) is `key`. A spelling holds
    /// no `::`, so the key's last `::` separates the module, the run or the shared
    /// import from the spelling, a leading `@@` marks a shared import and a leading `@`
    /// a run, and a key without `::` is a root label's.
    pub fn from_runtime_key(key: &SmolStr) -> Self {
        match key.rsplit_once("::") {
            Some((space, name)) if space.starts_with("@@") => Label {
                name: SmolStr::from(name),
                space: Some(Space::Import(std::sync::Arc::new(ImportSpace {
                    spelled: SmolStr::from(&space[2..]),
                    shared: None,
                }))),
            },
            Some((space, name)) => match space.strip_prefix('@') {
                Some(run) => Label::in_run(
                    run.split("::")
                        .fold(RunPath::default(), |path, segment| path.child(segment)),
                    name,
                ),
                None => {
                    Label::in_module(ModulePath::new(space.split("::").map(SmolStr::from)), name)
                }
            },
            None => Label::new(key.clone()),
        }
    }

    /// The spelling, without the module.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The module the label belongs to, or `None` for the root's namespace and a
    /// run's.
    pub fn module(&self) -> Option<&ModulePath> {
        match &self.space {
            Some(Space::Module(module)) => Some(module),
            Some(Space::Run(_) | Space::Import(_) | Space::Decl(_)) | None => None,
        }
    }

    /// The run whose top-level mutable variable the label is the store field of, or
    /// `None` for a root or a module's label ([`Label::in_run`]).
    pub fn run(&self) -> Option<&RunPath> {
        match &self.space {
            Some(Space::Run(run)) => Some(run),
            Some(Space::Module(_) | Space::Import(_) | Space::Decl(_)) | None => None,
        }
    }

    /// The shared import whose top-level induction variable the label is the history
    /// field of, or `None` for any other label ([`Label::in_import`]). A label read
    /// back from a run-time key has none ([`ImportSpace`]), and nothing asks one.
    pub fn import(&self) -> Option<&SharedImport> {
        match &self.space {
            Some(Space::Import(space)) => Some(space.shared.as_ref().unwrap_or_else(|| {
                panic!("`{self}` was read back from a run-time key, which keeps no shared import")
            })),
            Some(Space::Module(_) | Space::Run(_) | Space::Decl(_)) | None => None,
        }
    }

    /// The label as run time keys records by: its [`Display`](fmt::Display)
    /// spelling for a root or a module's label, `@run::name` for a run's, and
    /// `@@shared::name` for a shared import's, since no module path or run path begins
    /// with `@`. A spelling holds no `::`, so no two labels
    /// share a key, and [`Label::from_runtime_key`] inverts it. A root label's key
    /// is its spelling, shared rather than copied. A constructor's tag keys by its spelling
    /// too: a tag is never a store's or a record's key, which is what the key is for.
    pub fn runtime_key(&self) -> SmolStr {
        match &self.space {
            Some(Space::Decl(_)) => self.name.clone(),
            Some(Space::Module(module)) => smol_str::format_smolstr!("{module}::{}", self.name),
            Some(Space::Run(run)) => smol_str::format_smolstr!("@{run}::{}", self.name),
            Some(Space::Import(space)) => {
                smol_str::format_smolstr!("@@{}::{}", space.spelled, self.name)
            }
            None => self.name.clone(),
        }
    }
}

/// Assert that `name` holds no `::`, which keeps two labels from sharing a run-time
/// key ([`Label::runtime_key`]).
fn debug_assert_spelling(name: &str) {
    debug_assert!(
        !name.contains("::"),
        "a label's spelling `{name}` holds no `::`; a module goes in the label's module"
    );
}

/// `name` for a label of the root's namespace, `module::name` for another
/// module's, `run::name` for a run's, as a source reads the run's member, and
/// `shared::name` for a shared import's. A run's label, a shared import's and a
/// module's can print alike; [`Label::runtime_key`] tells them apart.
impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.space {
            Some(Space::Module(module)) => write!(f, "{module}::{}", self.name),
            Some(Space::Run(run)) => write!(f, "{run}::{}", self.name),
            Some(Space::Import(space)) => write!(f, "{}::{}", space.spelled, self.name),
            Some(Space::Decl(_)) | None => f.write_str(&self.name),
        }
    }
}

/// The run-time key as a quoted string, which no two labels share.
impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.runtime_key().as_str(), f)
    }
}

/// So a borrowed label compares against a constant, as `&str` does against
/// `String`.
impl PartialEq<Label> for &Label {
    fn eq(&self, other: &Label) -> bool {
        **self == *other
    }
}

impl From<&Label> for Label {
    fn from(label: &Label) -> Self {
        label.clone()
    }
}

impl From<&str> for Label {
    fn from(name: &str) -> Self {
        Label::new(name)
    }
}

impl From<String> for Label {
    fn from(name: String) -> Self {
        Label::new(name)
    }
}

impl From<&String> for Label {
    fn from(name: &String) -> Self {
        Label::new(name.as_str())
    }
}

impl From<SmolStr> for Label {
    fn from(name: SmolStr) -> Self {
        Label::new(name)
    }
}

impl From<&SmolStr> for Label {
    fn from(name: &SmolStr) -> Self {
        Label::new(name.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(spelled: &str) -> ModulePath {
        ModulePath::new(spelled.split("::").map(SmolStr::from))
    }

    #[test]
    fn a_label_is_its_spelling_and_its_module() {
        let root = Label::new("price");
        let catalog = Label::in_module(module("catalog"), "price");
        let shop = Label::in_module(module("shop::cart"), "price");
        assert_ne!(root, catalog);
        assert_ne!(catalog, shop);
        assert_eq!(catalog, Label::in_module(module("catalog"), "price"));
        assert_eq!(root, Label::fixed("price"));
        assert_eq!(root.to_string(), "price");
        assert_eq!(catalog.to_string(), "catalog::price");
        assert_eq!(shop.to_string(), "shop::cart::price");
        assert_eq!(format!("{catalog:?}"), "\"catalog::price\"");
    }

    #[test]
    fn a_run_label_prints_as_its_member_reads_and_keys_apart_from_a_modules() {
        let run = Label::in_run(RunPath::default().child("eu"), "stock");
        let module = Label::in_module(module("eu"), "stock");
        assert_ne!(run, module);
        assert_eq!(run.to_string(), "eu::stock");
        assert_eq!(module.to_string(), "eu::stock");
        assert_eq!(run.runtime_key(), "@eu::stock");
        assert_eq!(module.runtime_key(), "eu::stock");
    }

    #[test]
    fn a_runtime_key_names_its_label() {
        for label in [
            Label::new("price"),
            Label::in_module(module("catalog"), "price"),
            Label::in_module(module("shop::cart"), "price"),
            Label::in_run(RunPath::default().child("eu"), "price"),
            Label::in_run(RunPath::default().child("t").child("a"), "price"),
            Label::in_import(SharedImport::of(module("shop::cart")), "price"),
            Label::in_import(scaled(), "price"),
        ] {
            assert_eq!(Label::from_runtime_key(&label.runtime_key()), label);
        }
    }

    /// `scaled(region="a::b")`, a shared import whose argument's spelling holds `::`.
    fn scaled() -> SharedImport {
        SharedImport {
            module: module("scaled"),
            arguments: std::sync::Arc::new([(
                SmolStr::from("region"),
                crate::ccl::names::KeyArgument::Lit(crate::ccl::Lit::String("a::b".into())),
            )]),
        }
    }

    #[test]
    fn a_shared_import_label_keys_apart_from_a_runs_and_a_modules() {
        let shared = Label::in_import(scaled(), "total");
        assert_eq!(shared.to_string(), "scaled(region=\"a::b\")::total");
        assert_eq!(shared.runtime_key(), "@@scaled(region=\"a::b\")::total");
        assert_ne!(shared, Label::in_module(module("scaled"), "total"));
        assert_ne!(
            shared,
            Label::in_run(RunPath::default().child("scaled"), "total")
        );
        // Read back, it is the same label, and keeps no shared import to mint a binder from.
        assert_eq!(
            Label::from_runtime_key(&shared.runtime_key()).runtime_key(),
            shared.runtime_key()
        );
        assert_eq!(shared.import(), Some(&scaled()));
    }

    #[test]
    fn labels_order_by_spelling_first() {
        let mut labels = [
            Label::in_module(module("a"), "z"),
            Label::new("y"),
            Label::in_module(module("b"), "y"),
        ];
        labels.sort();
        let spelled: Vec<String> = labels.iter().map(Label::to_string).collect();
        assert_eq!(spelled, ["y", "b::y", "a::z"]);
    }
}
