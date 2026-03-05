//! General-purpose utilities shared across compiler and inference passes.

use std::collections::HashMap;

/// A stack of named-binding scopes supporting lexical shadowing.
///
/// Scopes are entered and exited exclusively through [`with_scope`](Self::with_scope).
/// [`bind`](Self::bind) records a name→value mapping in the innermost scope;
/// [`lookup`](Self::lookup) searches from innermost to outermost, returning the first match.
///
/// This type is generic over the stored value `V`:
///
/// | Type alias | `V` |
/// |---|---|
/// | [`TypeInferenceContext`](crate::ccl::infer::TypeInferenceContext) | [`Type`](crate::ccl::Type) |
/// | [`CompileContext`](crate::interpreter::compile_ccl::CompileContext) | [`Extent`](crate::interpreter::Extent) |
pub struct ScopeStack<V> {
    /// Scope stack; innermost scope is last.
    scopes: Vec<HashMap<String, V>>,
}

impl<V> ScopeStack<V> {
    /// Create a new, empty scope stack.
    pub fn new() -> Self {
        ScopeStack { scopes: Vec::new() }
    }

    /// Execute `f` inside a fresh scope, returning its result.
    ///
    /// The scope is pushed before `f` is called and popped after it returns.
    pub fn with_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(HashMap::new());
        let result = f(self);
        self.scopes
            .pop()
            .expect("ScopeStack: scope underflow in with_scope");
        result
    }

    /// Bind `name` to `value` in the innermost scope.
    ///
    /// # Panics
    ///
    /// Panics if called outside of [`with_scope`](Self::with_scope) (no active scope).
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

impl<V> Default for ScopeStack<V> {
    fn default() -> Self {
        Self::new()
    }
}
