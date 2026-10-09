//! A module's identity: its path, `shop::cart` (`docs/chl-spec.md`, "9.1
//! Vocabulary").
//!
//! [`crate::ast::ModulePath`] is a path as written, each segment with its span.
//! [`ModulePath`] is the path itself, which names one module in every
//! compilation of a program.

use crate::lexer::Token;
use logos::Logos;
use smol_str::SmolStr;
use std::fmt;
use std::sync::Arc;

/// The first segment of every std module's path (`docs/chl-spec.md`, "9.16 The
/// std root").
pub const STD_ROOT: &str = "std";

/// A module path: one or more segments, each following [`segment_error`]'s rule.
///
/// Cloning copies a pointer. Two paths are equal when their segments are, and
/// order compares segments lexicographically, so the order is a function of the
/// spellings alone and agrees across compilations.
///
/// The pointer is thin, one word, because every record label and variant tag
/// holds an optional path.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModulePath(Arc<Vec<SmolStr>>);

impl ModulePath {
    /// The path of `segments`.
    ///
    /// Panics on no segments, and in debug builds on a segment that breaks
    /// [`segment_error`]'s rule: every caller builds a path from segments the
    /// parser or a file name check already accepted.
    pub fn new(segments: impl IntoIterator<Item = SmolStr>) -> Self {
        let segments: Arc<Vec<SmolStr>> = Arc::new(segments.into_iter().collect());
        assert!(!segments.is_empty(), "a module path has a segment");
        debug_assert!(
            segments.iter().all(|s| segment_error(s).is_none()),
            "every segment of {segments:?} is a module name"
        );
        ModulePath(segments)
    }

    pub fn segments(&self) -> &[SmolStr] {
        &self.0
    }

    /// Whether the path names a module under the std root rather than a file
    /// under the module root.
    pub fn is_std(&self) -> bool {
        self.0[0] == STD_ROOT
    }

    /// The file the path names, relative to its root: `a::b::c` is `a/b/c.cambra`
    /// (`docs/chl-spec.md`, "9.15 Module files").
    pub fn relative_file(&self) -> String {
        let mut file = self.0.join("/");
        file.push_str(".cambra");
        file
    }
}

impl fmt::Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0.join("::"))
    }
}

impl fmt::Debug for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ModulePath({self})")
    }
}

/// Why `name` cannot be a module path segment, or `None` when it can
/// (`docs/chl-spec.md`, "9.15 Module files").
///
/// A segment is an identifier, so not a keyword. It begins with a lowercase
/// letter, since a capitalized name is a type, and not with `__`, a namespace
/// user code cannot bind.
pub fn segment_error(name: &str) -> Option<String> {
    // The lexer skips whitespace, so one identifier token must also span the
    // whole name.
    let mut tokens = Token::lexer(name);
    let one_identifier = matches!(tokens.next(), Some(Ok(Token::Ident(_))))
        && tokens.span() == (0..name.len())
        && tokens.next().is_none();
    if !one_identifier {
        Some(format!("module name `{name}` is not an identifier"))
    } else if name.starts_with("__") {
        Some(format!(
            "module name `{name}` begins with `__`, a namespace user code cannot bind"
        ))
    } else if !name.starts_with(|c: char| c.is_ascii_lowercase()) {
        Some(format!(
            "module name `{name}` must begin with a lowercase letter; a capitalized name is a \
             type"
        ))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(spelled: &str) -> ModulePath {
        ModulePath::new(spelled.split("::").map(SmolStr::from))
    }

    #[test]
    fn a_path_spells_and_files_by_its_segments() {
        let p = path("shop::cart");
        assert_eq!(p.to_string(), "shop::cart");
        assert_eq!(p.relative_file(), "shop/cart.cambra");
        assert!(!p.is_std());
        assert!(path("std::http").is_std());
        assert!(!path("stdlib").is_std());
    }

    #[test]
    fn paths_order_by_segments() {
        assert!(path("a::z") < path("b"));
        assert!(path("a") < path("a::b"));
    }

    #[test]
    fn a_segment_is_a_lowercase_identifier() {
        assert_eq!(segment_error("cart"), None);
        assert_eq!(segment_error("cart_2"), None);
        for bad in [
            "Cart", "__cart", "my-app", "2nd", "import", "", "a b", " cart",
        ] {
            assert!(segment_error(bad).is_some(), "{bad:?} is refused");
        }
    }
}
