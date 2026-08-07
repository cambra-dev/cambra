//! General-purpose utilities shared across compiler and inference passes.

use std::collections::HashMap;

use log::{debug, trace};

use crate::interpreter::tuple_field;

/// Format a map of named fields as either a positional tuple or a named record.
///
/// If every key is a dense `_0`…`_n` sequence, emits `{v0, v1, …}`; otherwise
/// emits `{name: value, …}` with fields sorted alphabetically.
pub fn fmt_record<V: std::fmt::Display>(
    f: &mut std::fmt::Formatter<'_>,
    fields: &HashMap<String, V>,
) -> std::fmt::Result {
    let is_tuple = (0..fields.len()).all(|i| fields.contains_key(&tuple_field(i)));
    if is_tuple {
        let mut ordered: Vec<(usize, &V)> = fields
            .iter()
            .map(|(k, v)| (k[1..].parse::<usize>().unwrap(), v))
            .collect();
        ordered.sort_by_key(|(i, _)| *i);
        let strs: Vec<String> = ordered.iter().map(|(_, v)| format!("{v}")).collect();
        write!(f, "{{{}}}", strs.join(", "))
    } else {
        let mut field_strs: Vec<String> = fields
            .iter()
            .map(|(name, v)| format!("{name}: {v}"))
            .collect();
        field_strs.sort();
        write!(f, "{{{}}}", field_strs.join(", "))
    }
}

/// Format the arms of a tagged sum in CHL's surface syntax:
/// `` {`arm₀{P₀} | `arm₁{P₁}} ``.
///
/// `arms` supplies each tag with its payload **already rendered**, or `None`
/// when the arm stores nothing — the nullary constructor, whose payload type is
/// `Unit`. A nullary arm is written bare (`` `abort ``), matching the surface
/// spelling `` {`arm} `` rather than an explicit `` `abort{Unit} ``.
///
/// A payload that already renders brace-delimited — a record, or a nested sum —
/// **reuses those braces** instead of doubling them, which is the surface rule
/// that a nested type inside an arm omits its own: `` `arm{a: Int, b: Int} ``,
/// not `` `arm{{a: Int, b: Int}} ``. Nothing is lost to the collapse, because an
/// arm always begins with a backtick — so a brace body that does not is a
/// payload, never an arm list.
///
/// Shared by `Type` and `Extent`, which render the same sums either side of the
/// compile/runtime boundary and must agree: a tag spelled two ways reads as two
/// different things in a tiling-mismatch panic, which is where these strings are
/// most often compared.
/// `open` marks an arm set that commits only to the arms it lists — the demand a
/// `match` with a default arm makes. It renders a trailing `| …` so a demand
/// never reads as an exact sum. Only a *demand* is ever open; every producer of
/// a sum is closed, and the runtime `Extent` cannot be open at all.
pub fn fmt_variant_arms(
    f: &mut std::fmt::Formatter<'_>,
    arms: impl Iterator<Item = (String, Option<String>)>,
    open: bool,
) -> std::fmt::Result {
    let parts: Vec<String> = arms
        .map(|(tag, payload)| match payload {
            None => format!("`{tag}"),
            // Already `{…}` — a record or a nested sum — so the arm's braces and
            // the payload's are the same pair.
            Some(p) if p.starts_with('{') && p.ends_with('}') => format!("`{tag}{p}"),
            Some(p) => format!("`{tag}{{{p}}}"),
        })
        .collect();
    let ellipsis = if open { " | …" } else { "" };
    write!(f, "{{{}{ellipsis}}}", parts.join(" | "))
}

/// A stack of named-binding scopes supporting lexical shadowing.
///
/// Scopes are entered and exited exclusively through [`enter_scope`](Self::enter_scope),
/// which returns a [`ScopeGuard`] that pops the scope automatically on drop.
/// [`bind`](Self::bind) records a name→value mapping in the innermost scope;
/// [`lookup`](Self::lookup) searches from innermost to outermost, returning the first match.
///
/// This type is generic over the key `K` and the stored value `V`:
/// ```
/// use cambra::util::ScopeStack;
///
/// let mut stack: ScopeStack<String, i32> = ScopeStack::new();
///
/// {
///     let mut scope = stack.enter_scope();
///     scope.bind("x".to_string(), 1);
///     assert_eq!(scope.lookup("x"), Some(&1));
///
///     // Inner scope shadows "x".
///     let mut inner = scope.enter_scope();
///     inner.bind("x".to_string(), 2);
///     assert_eq!(inner.lookup("x"), Some(&2));
///     // `inner` drops here, popping the inner scope.
/// }
/// // `scope` drops here, popping the outer scope.
/// // The stack is now empty; `stack` can be dropped cleanly.
/// ```
pub struct ScopeStack<K, V> {
    /// Scope stack; innermost scope is last.
    scopes: Vec<HashMap<K, V>>,
}

/// An RAII guard that pops a scope from its [`ScopeStack`] when dropped.
///
/// This struct is created by the [`enter_scope`](ScopeStack::enter_scope) method
/// on [`ScopeStack`]. See its documentation for usage examples.
///
/// `&mut ScopeGuard<'_, V>` deref-coerces to `&mut ScopeStack<V>`, so a guard can
/// be passed wherever a mutable reference to the underlying stack is expected.
///
/// # Warning
///
/// Must be bound to a variable; if dropped immediately (e.g. used as a
/// temporary), the scope opens and closes before any bindings are added,
/// silently falling back to the outer scope.
#[must_use = "ScopeGuard pops the scope on drop; if unused, the scope closes immediately"]
pub struct ScopeGuard<'a, K: Eq + std::hash::Hash + std::fmt::Debug, V> {
    stack: &'a mut ScopeStack<K, V>,
}

impl<'a, K: Eq + std::hash::Hash + std::fmt::Debug, V> std::ops::Deref for ScopeGuard<'a, K, V> {
    type Target = ScopeStack<K, V>;
    fn deref(&self) -> &Self::Target {
        self.stack
    }
}

impl<'a, K: Eq + std::hash::Hash + std::fmt::Debug, V> std::ops::DerefMut for ScopeGuard<'a, K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.stack
    }
}

impl<'a, K: Eq + std::hash::Hash + std::fmt::Debug, V> Drop for ScopeGuard<'a, K, V> {
    fn drop(&mut self) {
        // Invariant: `enter_scope` always pushes before handing out this guard,
        // and `scopes` is private, so underflow is impossible in correct code.
        // Avoid double-panic during unwinding for the same reason as `ScopeStack::drop`.
        self.stack.pop_scope();
    }
}

impl<K: Eq + std::hash::Hash + std::fmt::Debug, V> ScopeStack<K, V> {
    /// Create a new, empty scope stack.
    pub fn new() -> Self {
        ScopeStack { scopes: Vec::new() }
    }

    /// Enter a fresh scope, returning a guard that pops it on drop.
    ///
    /// The scope is pushed immediately and popped when the returned [`ScopeGuard`]
    /// goes out of scope. `&mut guard` deref-coerces to `&mut ScopeStack<V>`, so
    /// the guard can be passed directly to functions expecting `&mut ScopeStack<V>`.
    pub fn enter_scope(&mut self) -> ScopeGuard<'_, K, V> {
        self.push_scope();
        ScopeGuard { stack: self }
    }

    /// Push a fresh scope without returning a guard.
    ///
    /// Prefer [`enter_scope`](Self::enter_scope) when possible; this is a lower-level
    /// escape hatch for wrapper types (e.g. [`CompileContext`](crate::interpreter::compile_ccl::CompileContext))
    /// that need to manage scopes on a field while the wrapper itself is borrowed.
    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pop the innermost scope.
    ///
    /// Panics on underflow (unless already panicking).  Prefer the drop of a
    /// [`ScopeGuard`] over calling this directly.
    pub(crate) fn pop_scope(&mut self) {
        if !std::thread::panicking() {
            let popped = self
                .scopes
                .pop()
                .expect("ScopeStack: scope underflow in pop_scope");
            trace!("ScopeStack: pop_scope; popped={:?}", popped.keys());
        } else {
            self.scopes.pop();
        }
    }

    /// Bind `name` to `value` in the innermost scope.
    ///
    /// # Panics
    ///
    /// Panics if called outside of an active scope (no scopes pushed).
    /// In debug builds, also panics if `name` is already bound in the current scope.
    pub fn bind(&mut self, name: impl Into<K>, value: V) {
        let name = name.into();
        debug!("Binding '{name:?}' in scope");
        let scope = self
            .scopes
            .last_mut()
            .expect("ScopeStack::bind called with no active scope");
        debug_assert!(
            !scope.contains_key(&name),
            "ScopeStack::bind: '{name:?}' already bound in the current scope"
        );
        scope.insert(name, value);
    }

    /// Look up `name` from innermost scope outward, returning the first match.
    pub fn lookup<Q>(&self, name: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Eq + std::hash::Hash + ?Sized,
    {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    pub fn fmt_scopes(&self) -> String
    where
        K: std::fmt::Display,
        V: std::fmt::Display,
    {
        self.scopes
            .iter()
            .rev()
            .map(|scope| {
                let bindings: Vec<String> = scope
                    .iter()
                    .map(|(name, value)| format!("{name}: {value}"))
                    .collect();
                format!("{{{}}}", bindings.join(", "))
            })
            .collect::<Vec<String>>()
            .join(" , ")
    }
}

impl<K, V> Drop for ScopeStack<K, V> {
    fn drop(&mut self) {
        // If we are already panicking, don't double-panic (which aborts).
        if !std::thread::panicking() && !self.scopes.is_empty() {
            panic!(
                "ScopeStack dropped with {} active scopes! This indicates a scope-management bug (missing pop/drop).",
                self.scopes.len()
            );
        }
    }
}

impl<K: Eq + std::hash::Hash + std::fmt::Debug, V> Default for ScopeStack<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
