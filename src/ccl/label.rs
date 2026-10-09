//! Record field labels and variant tags.

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
/// - `Option`'s tags `some` and `none`, which belong to the std root. Sharing
///   the root's namespace, and so every module's unqualified `some` and
///   `none`, is temporary: it lasts until `Option` is a nominal variant whose
///   tags follow the type rather than a module.
///
/// Labels order by spelling, then by module, so a record or variant written in
/// one module keeps the order of its spellings.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label {
    name: SmolStr,
    module: Option<ModulePath>,
}

impl Label {
    /// The root module's label spelled `name`.
    pub fn new(name: impl Into<SmolStr>) -> Self {
        Label {
            name: name.into(),
            module: None,
        }
    }

    /// [`Label::new`] for a spelling known at compile time, so a label the
    /// compiler builds for itself can be a constant.
    pub const fn fixed(name: &'static str) -> Self {
        Label {
            name: SmolStr::new_static(name),
            module: None,
        }
    }

    /// The label spelled `name` that belongs to `module`.
    pub fn in_module(module: ModulePath, name: impl Into<SmolStr>) -> Self {
        Label {
            name: name.into(),
            module: Some(module),
        }
    }

    /// The spelling, without the module.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The module the label belongs to, or `None` for the root's namespace.
    pub fn module(&self) -> Option<&ModulePath> {
        self.module.as_ref()
    }
}

/// `name` for a label of the root's namespace and `module::name` for another
/// module's. This is also the label's spelling at run time, where records are
/// keyed by strings: a user identifier cannot contain `::`, so no two labels
/// share a spelling.
impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.module {
            Some(module) => write!(f, "{module}::{}", self.name),
            None => f.write_str(&self.name),
        }
    }
}

/// The spelling as a string literal, as a `String` label's `Debug` was.
impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string(), f)
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
