//! General-purpose utilities shared across compiler and inference passes.

use std::collections::HashMap;

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
/// | [`CompileContext`](crate::interpreter::compile_ccl::CompileContext) | [`Extent`](crate::interpreter::Extent) |
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
        if !std::thread::panicking() {
            self.stack
                .scopes
                .pop()
                .expect("ScopeStack: scope underflow in ScopeGuard::drop");
        } else {
            self.stack.scopes.pop();
        }
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
    /// goes out of scope.
    pub fn enter_scope(&mut self) -> ScopeGuard<'_, V> {
        self.scopes.push(HashMap::new());
        ScopeGuard { stack: self }
    }

    /// Bind `name` to `value` in the innermost scope.
    ///
    /// # Panics
    ///
    /// Panics if called outside of an active scope (no scopes pushed).
    /// In debug builds, also panics if `name` is already bound in the current scope.
    pub fn bind(&mut self, name: &str, value: V) {
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
