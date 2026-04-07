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

/// A stack of named-binding scopes supporting lexical shadowing.
///
/// Scopes are entered and exited exclusively through [`enter_scope`](Self::enter_scope),
/// which returns a [`ScopeGuard`] that pops the scope automatically on drop.
/// [`bind`](Self::bind) records a name→value mapping in the innermost scope;
/// [`lookup`](Self::lookup) searches from innermost to outermost, returning the first match.
///
/// This type is generic over the stored value `V`:
///
/// | Type alias | `V` |
/// |---|---|
/// | [`TypeInferenceContext`](crate::ccl::infer::TypeInferenceContext) | [`Type`](crate::ccl::Type) |
/// | [`TileCompileContext`](crate::interpreter::compile_tile_operators::TileCompileContext) | `TileVarBinding` |
///
/// # Examples
///
/// ```
/// use cambra::util::ScopeStack;
///
/// let mut stack: ScopeStack<i32> = ScopeStack::new();
///
/// {
///     let mut scope = stack.enter_scope();
///     scope.bind("x", 1);
///     assert_eq!(scope.lookup("x"), Some(&1));
///
///     // Inner scope shadows "x".
///     let mut inner = scope.enter_scope();
///     inner.bind("x", 2);
///     assert_eq!(inner.lookup("x"), Some(&2));
///     // `inner` drops here, popping the inner scope.
/// }
/// // `scope` drops here, popping the outer scope.
/// // The stack is now empty; `stack` can be dropped cleanly.
/// ```
pub struct ScopeStack<V> {
    /// Scope stack; innermost scope is last.
    scopes: Vec<HashMap<String, V>>,
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
pub struct ScopeGuard<'a, V> {
    stack: &'a mut ScopeStack<V>,
}

impl<'a, V> std::ops::Deref for ScopeGuard<'a, V> {
    type Target = ScopeStack<V>;
    fn deref(&self) -> &Self::Target {
        self.stack
    }
}

impl<'a, V> std::ops::DerefMut for ScopeGuard<'a, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.stack
    }
}

impl<'a, V> Drop for ScopeGuard<'a, V> {
    fn drop(&mut self) {
        // Invariant: `enter_scope` always pushes before handing out this guard,
        // and `scopes` is private, so underflow is impossible in correct code.
        // Avoid double-panic during unwinding for the same reason as `ScopeStack::drop`.
        self.stack.pop_scope();
    }
}

impl<V> ScopeStack<V> {
    /// Create a new, empty scope stack.
    pub fn new() -> Self {
        ScopeStack { scopes: Vec::new() }
    }

    /// Enter a fresh scope, returning a guard that pops it on drop.
    ///
    /// The scope is pushed immediately and popped when the returned [`ScopeGuard`]
    /// goes out of scope. `&mut guard` deref-coerces to `&mut ScopeStack<V>`, so
    /// the guard can be passed directly to functions expecting `&mut ScopeStack<V>`.
    pub fn enter_scope(&mut self) -> ScopeGuard<'_, V> {
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
            trace!(
                "ScopeStack: pop_scope; popped={:?}",
                popped.keys().cloned().collect::<Vec<String>>()
            );
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
    pub fn bind(&mut self, name: &str, value: V) {
        debug!("Binding '{name}' in scope");
        let scope = self
            .scopes
            .last_mut()
            .expect("ScopeStack::bind called with no active scope");
        debug_assert!(
            !scope.contains_key(name),
            "ScopeStack::bind: '{name}' already bound in the current scope"
        );
        scope.insert(name.to_string(), value);
    }

    /// Look up `name` from innermost scope outward, returning the first match.
    pub fn lookup(&self, name: &str) -> Option<&V> {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    pub fn fmt_scopes(&self) -> String
    where
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

impl<V> Drop for ScopeStack<V> {
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

impl<V> Default for ScopeStack<V> {
    fn default() -> Self {
        Self::new()
    }
}
