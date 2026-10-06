//! The names CHL source calls as builtins, with the arity and statement position each one takes.
//!
//! [`SURFACE_BUILTINS`] is the one list of these spellings. The compiler's lowering and the
//! differential interpreter both resolve a called name through [`SurfaceBuiltin::from_name`] and
//! then match on the variant, so a spelling appears in source text here and nowhere else. What a
//! builtin means stays with each consumer: this table names a builtin and the shape of its call,
//! not its semantics.
//!
//! A [`SurfaceBuiltin`] is a CHL-level name. It is distinct from the CCL IR's `Builtin`
//! (`src/ccl/ops.rs` in the `cambra` crate), whose display names reuse some of these spellings
//! for different operations: the IR's `map` is not the surface `map(kvs)` constructor, and its
//! `begin` is not the `with begin():` transaction marker.
//!
//! Recognition does not consult scope here. Whether a user binding of the same name shadows a
//! builtin is each consumer's decision.

/// A builtin CHL source calls by name. [`SURFACE_BUILTINS`] holds each one's spelling, arity,
/// and kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SurfaceBuiltin {
    Sum,
    Max,
    Groupby,
    Set,
    Map,
    Box,
    EmptyMap,
    AwaitFinal,
    Defer,
    Begin,
    HttpServe,
    TestSink,
    Stdin,
}

/// The number of arguments a [`SurfaceBuiltin`] call takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    Exact(usize),
    /// Any number of arguments.
    Any,
}

impl Arity {
    /// Whether a call with `n` arguments has this arity.
    pub fn accepts(self, n: usize) -> bool {
        match self {
            Arity::Exact(k) => n == k,
            Arity::Any => true,
        }
    }
}

/// Renders the argument count a diagnostic states: `Exact(1)` is "exactly one argument",
/// `Exact(0)` is "no arguments".
impl std::fmt::Display for Arity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Arity::Exact(0) => f.write_str("no arguments"),
            Arity::Exact(1) => f.write_str("exactly one argument"),
            Arity::Exact(2) => f.write_str("exactly two arguments"),
            Arity::Exact(3) => f.write_str("exactly three arguments"),
            Arity::Exact(n) => write!(f, "exactly {n} arguments"),
            Arity::Any => f.write_str("any number of arguments"),
        }
    }
}

/// Where lowering recognizes a [`SurfaceBuiltin`] call. The kind describes lowering's
/// recognizers only: the differential interpreter evaluates a subset of the `Function` rows and
/// treats the rest like the other kinds, as an unknown function. A lowering test in the
/// `cambra` crate (`src/ccl/lower/exprs.rs`, `only_function_rows_lower_in_their_own_arm`) holds
/// the column to what `lower_call` does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SurfaceBuiltinKind {
    /// A call in expression position, which denotes a value.
    Function,
    /// The context of a `with` statement, `with begin():`.
    TransactionMarker,
    /// The right-hand side of an assignment statement that declares a sink, bound to the
    /// assignment's target.
    SinkDeclaration,
    /// A data source. A host registers sources at runtime by name; the table lists the ones
    /// every host registers. A registered source resolves by its registration, so a source
    /// absent from the table still resolves and a listed one resolves only once registered.
    Source,
}

/// One row of [`SURFACE_BUILTINS`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SurfaceBuiltinEntry {
    pub spelling: &'static str,
    pub builtin: SurfaceBuiltin,
    pub arity: Arity,
    pub kind: SurfaceBuiltinKind,
}

const fn entry(
    spelling: &'static str,
    builtin: SurfaceBuiltin,
    arity: Arity,
    kind: SurfaceBuiltinKind,
) -> SurfaceBuiltinEntry {
    SurfaceBuiltinEntry {
        spelling,
        builtin,
        arity,
        kind,
    }
}

/// Every surface builtin, in [`SurfaceBuiltin`] declaration order, so that a variant's
/// discriminant indexes its row.
///
/// `docs/chl-spec.md`, "7. Built-in functions and sources" specifies most of these;
/// `chl-parser/design-chl-parser.md`, "Surface builtins" lists the rows it does not.
pub const SURFACE_BUILTINS: &[SurfaceBuiltinEntry] = {
    use Arity::{Any, Exact};
    use SurfaceBuiltin as B;
    use SurfaceBuiltinKind::{Function, SinkDeclaration, Source, TransactionMarker};
    &[
        entry("sum", B::Sum, Exact(1), Function),
        entry("max", B::Max, Exact(1), Function),
        entry("groupby", B::Groupby, Exact(2), Function),
        entry("set", B::Set, Exact(1), Function),
        entry("map", B::Map, Exact(1), Function),
        entry("box", B::Box, Exact(1), Function),
        entry("empty_map", B::EmptyMap, Exact(0), Function),
        entry("await_final", B::AwaitFinal, Exact(1), Function),
        entry("defer", B::Defer, Any, Function),
        entry("begin", B::Begin, Exact(0), TransactionMarker),
        entry("http_serve", B::HttpServe, Exact(3), SinkDeclaration),
        // Listed unconditionally. The `cambra` crate recognizes it only under `cfg(test)` or
        // its `test-helpers` feature, and the differential interpreter always does; each
        // consumer gates its own recognition.
        entry("test_sink", B::TestSink, Exact(0), SinkDeclaration),
        entry("stdin", B::Stdin, Exact(0), Source),
    ]
};

impl SurfaceBuiltin {
    /// The builtin `name` spells, if it spells one.
    pub fn from_name(name: &str) -> Option<Self> {
        SURFACE_BUILTINS
            .iter()
            .find(|e| e.spelling == name)
            .map(|e| e.builtin)
    }

    /// This builtin's row of [`SURFACE_BUILTINS`]. A `const fn`, like the accessors below, so a
    /// consumer can assert a row's arity at build time.
    pub const fn entry(self) -> &'static SurfaceBuiltinEntry {
        let row = &SURFACE_BUILTINS[self as usize];
        debug_assert!(
            row.builtin as usize == self as usize,
            "SURFACE_BUILTINS is in SurfaceBuiltin declaration order"
        );
        row
    }

    pub const fn spelling(self) -> &'static str {
        self.entry().spelling
    }

    pub const fn arity(self) -> Arity {
        self.entry().arity
    }

    pub const fn kind(self) -> SurfaceBuiltinKind {
        self.entry().kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every variant, by an exhaustive match: a new variant fails to compile here until it is
    /// listed.
    fn all_variants() -> Vec<SurfaceBuiltin> {
        use SurfaceBuiltin as B;
        let every = |b: B| match b {
            B::Sum
            | B::Max
            | B::Groupby
            | B::Set
            | B::Map
            | B::Box
            | B::EmptyMap
            | B::AwaitFinal
            | B::Defer
            | B::Begin
            | B::HttpServe
            | B::TestSink
            | B::Stdin => b,
        };
        [
            B::Sum,
            B::Max,
            B::Groupby,
            B::Set,
            B::Map,
            B::Box,
            B::EmptyMap,
            B::AwaitFinal,
            B::Defer,
            B::Begin,
            B::HttpServe,
            B::TestSink,
            B::Stdin,
        ]
        .into_iter()
        .map(every)
        .collect()
    }

    #[test]
    fn every_variant_has_exactly_one_row_at_its_discriminant() {
        let variants = all_variants();
        assert_eq!(variants.len(), SURFACE_BUILTINS.len());
        for (i, b) in variants.into_iter().enumerate() {
            assert_eq!(b as usize, i, "{b:?} is listed out of declaration order");
            assert_eq!(SURFACE_BUILTINS[i].builtin, b);
            assert_eq!(
                SURFACE_BUILTINS.iter().filter(|e| e.builtin == b).count(),
                1,
                "{b:?} has one row"
            );
        }
    }

    #[test]
    fn spellings_round_trip() {
        for e in SURFACE_BUILTINS {
            assert_eq!(SurfaceBuiltin::from_name(e.spelling), Some(e.builtin));
            assert_eq!(e.builtin.spelling(), e.spelling);
        }
        assert_eq!(SurfaceBuiltin::from_name("min"), None);
        assert_eq!(SurfaceBuiltin::from_name("Sum"), None);
    }

    #[test]
    fn arity_renders_its_count_in_words() {
        assert_eq!(Arity::Exact(0).to_string(), "no arguments");
        assert_eq!(Arity::Exact(1).to_string(), "exactly one argument");
        assert_eq!(Arity::Exact(2).to_string(), "exactly two arguments");
        assert_eq!(Arity::Exact(3).to_string(), "exactly three arguments");
        assert_eq!(Arity::Exact(7).to_string(), "exactly 7 arguments");
        assert_eq!(Arity::Any.to_string(), "any number of arguments");
    }

    #[test]
    fn spellings_are_term_names() {
        // `Caps` means type (`docs/chl-spec.md`, "6.1 Direction: term/type syntax split
        // [Decided]"), so a builtin called as a function is spelled lowercase.
        for e in SURFACE_BUILTINS {
            assert!(
                e.spelling.chars().next().is_some_and(char::is_lowercase),
                "{}",
                e.spelling
            );
        }
    }
}
