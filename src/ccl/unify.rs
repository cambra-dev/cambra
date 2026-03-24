//! Union-Find unification table for CCL type inference.
//!
//! Provides [`UnificationTable`], a sparse union-find structure over [`InferVarId`]s.
//! Each inference variable starts unregistered; callers call [`UnificationTable::register`]
//! when they allocate a fresh variable, then optionally [`UnificationTable::set`] once its
//! type is solved or [`UnificationTable::unify`] to equate two variables.
//!
//! The table is used by [`crate::ccl::infer::TypeInferenceContext`] to track solved inference
//! variables across the typed-expression tree, and by a post-inference resolution pass to
//! replace any remaining [`crate::ccl::Type::Infer`] placeholders with their concrete types.

use crate::ccl::{InferVarId, Type};

// ---------------------------------------------------------------------------
// Internal entry type
// ---------------------------------------------------------------------------

/// A single slot in the union-find table.
///
/// Variables start as `Root(None)` (unresolved) and transition either to
/// `Root(Some(ty))` when solved or to `Link(id)` when unioned with another variable.
enum Entry {
    /// This variable is the canonical representative of its equivalence class.
    ///
    /// `None` = not yet resolved to a concrete type.
    /// `Some(ty)` = solved; `ty` is the concrete type for this class.
    Root(Option<Type>),
    /// This variable forwards to another variable in the table.
    ///
    /// Path compression in [`UnificationTable::find`] shortens these chains.
    Link(InferVarId),
}

// ---------------------------------------------------------------------------
// UnificationTable
// ---------------------------------------------------------------------------

/// Sparse union-find table over [`InferVarId`]s.
///
/// Indexed by `InferVarId.0`; entries that have never been registered are
/// treated as absent (looked up as `None`). Supports:
/// - [`register`](Self::register) — allocate a slot for a new variable
/// - [`find`](Self::find) — path-compressing canonical-representative lookup
/// - [`set`](Self::set) — solve a variable to a concrete type
/// - [`probe`](Self::probe) — query the solved type if known
/// - [`unify`](Self::unify) — equate two variables (union-by-root)
#[derive(Default)]
pub struct UnificationTable {
    /// Sparse storage: index `i` holds the entry for variable `InferVarId(i)`.
    ///
    /// `None` at an index means that variable has never been registered.
    entries: Vec<Option<Entry>>,
}

impl UnificationTable {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a fresh inference variable, allocating its slot.
    ///
    /// Must be called before any other method is used on `id`.
    /// Calling `register` twice for the same `id` is a no-op.
    pub fn register(&mut self, id: InferVarId) {
        let idx = id.0 as usize;
        // Grow the backing vec if needed.
        if idx >= self.entries.len() {
            self.entries.resize_with(idx + 1, || None);
        }
        // Only initialise if not already present.
        if self.entries[idx].is_none() {
            self.entries[idx] = Some(Entry::Root(None));
        }
    }

    /// Path-compressing find: returns the canonical representative for `id`.
    ///
    /// Traverses `Link` chains, then updates all traversed entries to point
    /// directly at the root (path compression), flattening future lookups.
    ///
    /// Returns `id` unchanged if it is not registered in the table.
    pub fn find(&mut self, id: InferVarId) -> InferVarId {
        // Collect the path of links from id to its root.
        let mut path: Vec<InferVarId> = Vec::new();
        let mut current = id;
        loop {
            let idx = current.0 as usize;
            match self.entries.get(idx).and_then(|e| e.as_ref()) {
                Some(Entry::Link(next)) => {
                    let next = *next;
                    path.push(current);
                    current = next;
                }
                // Root or unregistered — current is the representative.
                _ => break,
            }
        }
        // Path compression: point every node in the path directly at the root.
        for node in path {
            let idx = node.0 as usize;
            self.entries[idx] = Some(Entry::Link(current));
        }
        current
    }

    /// Solve inference variable `id` to concrete type `ty`.
    ///
    /// Finds the root of `id`'s equivalence class and sets its type.
    /// Panics if the root was already solved to a *different* type — double-solving
    /// a variable to the same type is a no-op and is allowed, but solving it to two
    /// distinct types is a logic error in the compiler and always panics, regardless
    /// of build profile.
    pub fn set(&mut self, id: InferVarId, ty: Type) {
        let root = self.find(id);
        assert!(
            self.probe(root).is_none_or(|existing| existing == ty),
            "UnificationTable::set: variable {:?} already solved to a different type",
            root
        );
        let idx = root.0 as usize;
        if idx < self.entries.len() {
            self.entries[idx] = Some(Entry::Root(Some(ty)));
        }
    }

    /// Return the solved type for `id`, if any.
    ///
    /// Returns `None` if `id` is unregistered or its equivalence class has no
    /// concrete type yet.
    pub fn probe(&mut self, id: InferVarId) -> Option<Type> {
        let root = self.find(id);
        let idx = root.0 as usize;
        match self.entries.get(idx).and_then(|e| e.as_ref()) {
            Some(Entry::Root(ty)) => ty.clone(),
            _ => None,
        }
    }

    /// Allocate a fresh [`InferVarId`] and immediately register it in this table.
    ///
    /// Combines allocation and registration into one step. Only available in
    /// tests — production code must go through
    /// [`crate::ccl::infer::TypeInferenceContext::fresh_infer_var`], which also
    /// registers variables here but does so via the inference context.
    #[cfg(test)]
    pub fn fresh_var(&mut self) -> InferVarId {
        let id = crate::ccl::fresh_infer_var_id();
        self.register(id);
        id
    }

    /// Union two inference variables into the same equivalence class.
    ///
    /// After this call, `find(a) == find(b)`. The current implementation
    /// makes `b`'s root link to `a`'s root (no union-by-rank). If `a`'s root
    /// is already solved and `b`'s is not (or vice versa), the solved type
    /// is preserved on the surviving root.
    ///
    /// Returns `Err((ty_a, ty_b))` if both variables are already solved to
    /// *different* types — this indicates a type conflict in the program being
    /// compiled.
    pub fn unify(&mut self, a: InferVarId, b: InferVarId) -> Result<(), (Type, Type)> {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a == root_b {
            return Ok(()); // already in the same class
        }
        // Prefer keeping a solved root as the root.
        let solved_a = self.probe(root_a);
        let solved_b = self.probe(root_b);
        match (solved_a, solved_b) {
            (None, Some(_)) => {
                // b's root is solved; make a link to b's root and store type there.
                let idx_a = root_a.0 as usize;
                if idx_a < self.entries.len() {
                    self.entries[idx_a] = Some(Entry::Link(root_b));
                }
            }
            (Some(ty_a), Some(ty_b)) => {
                if ty_a != ty_b {
                    return Err((ty_a, ty_b));
                }
                // Both solved to the same type — link b to a (idempotent).
                let idx_b = root_b.0 as usize;
                if idx_b < self.entries.len() {
                    self.entries[idx_b] = Some(Entry::Link(root_a));
                }
            }
            _ => {
                // Default: link b's root to a's root.
                let idx_b = root_b.0 as usize;
                if idx_b < self.entries.len() {
                    self.entries[idx_b] = Some(Entry::Link(root_a));
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Resolution pass
// ---------------------------------------------------------------------------

/// Walk `expr` and replace every [`Type::Infer(id)`](crate::ccl::Type::Infer)
/// with the solved type from `table`, if one exists.
///
/// Nodes whose inference variable has no solution are left as `Infer(id)`
/// — the caller can then report ambiguous-type errors for those nodes.
/// Nodes already typed with a concrete type are left unchanged.
pub fn resolve(expr: &mut crate::ccl::TypedExpr, table: &mut UnificationTable) {
    // TODO: this does not recurse into sub-types of a solved type
    // (e.g. Fun(Infer(3), Int) — the inner Infer(3) is not resolved).
    // Currently safe because no production path produces nested Infer in
    // solved types. Fix this when type-level substitution is added.

    // Hole must never survive inference; its presence here is a compiler bug.
    debug_assert!(
        !matches!(expr.ty, Type::Hole),
        "Type::Hole found in resolve() on expression node {:?}; inference failed to convert it",
        &expr.node
    );

    // Resolve this node's type slot.
    if let Type::Infer(id) = expr.ty {
        if let Some(ty) = table.probe(id) {
            expr.ty = ty;
        }
    }
    // Recurse into sub-expressions.
    use crate::ccl::TypedExprNode;
    match &mut expr.node {
        TypedExprNode::Apply { function, argument } => {
            resolve(function, table);
            resolve(argument, table);
        }
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            debug_assert!(
                !matches!(param.ty, Type::Hole),
                "Type::Hole found in resolve() on Lambda param '{}'; inference failed to convert it",
                param.name
            );
            if let Type::Infer(id) = param.ty {
                if let Some(ty) = table.probe(id) {
                    param.ty = ty;
                }
            }
            resolve(body, table);
            if let Some(r) = refinement {
                if let crate::ccl::RefinementKind::Predicate(def) = &r.kind {
                    resolve(&mut def.borrow_mut(), table);
                }
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            debug_assert!(
                !matches!(binding.ty, Type::Hole),
                "Type::Hole found in resolve() on Let binding '{}'; inference failed to convert it",
                binding.name
            );
            if let Type::Infer(id) = binding.ty {
                if let Some(ty) = table.probe(id) {
                    binding.ty = ty;
                }
            }
            resolve(bound_expr, table);
            resolve(body, table);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            resolve(left, table);
            resolve(right, table);
        }
        TypedExprNode::UnaryOp(_, inner) => resolve(inner, table),
        TypedExprNode::List(elts) | TypedExprNode::Tuple(elts) => {
            for e in elts {
                resolve(e, table);
            }
        }
        TypedExprNode::TupleIndex(tuple, _) => resolve(tuple, table),
        TypedExprNode::Aggregate { input, .. } => resolve(input, table),
        TypedExprNode::GroupBy { collection, key } => {
            resolve(collection, table);
            resolve(key, table);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            resolve(scrutinee, table);
            for (_, arm) in branches {
                resolve(arm, table);
            }
        }
        TypedExprNode::Join {
            params,
            loop_body,
            outer_body,
            ..
        } => {
            for p in params {
                if let Type::Infer(id) = p.ty {
                    if let Some(ty) = table.probe(id) {
                        p.ty = ty;
                    }
                }
            }
            resolve(loop_body, table);
            resolve(outer_body, table);
        }
        TypedExprNode::Jump { args, .. } => {
            for a in args {
                resolve(a, table);
            }
        }
        TypedExprNode::Record(fields) => {
            for (_, e) in fields {
                resolve(e, table);
            }
        }
        // Leaf nodes — no sub-expressions to recurse into.
        TypedExprNode::Lit(_) | TypedExprNode::Var(_) | TypedExprNode::Source(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;
    use crate::ccl::{Expr, Lit, Type};

    #[test]
    fn test_register_and_probe_unresolved() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        assert_eq!(table.probe(v), None);
    }

    #[test]
    fn test_set_and_probe() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        table.set(v, Type::Base(BaseType::Int));
        assert_eq!(table.probe(v), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_find_self() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        assert_eq!(table.find(v), v);
    }

    #[test]
    fn test_unify_and_find() {
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.unify(a, b).unwrap();
        assert_eq!(table.find(a), table.find(b));
    }

    #[test]
    fn test_unify_propagates_solution() {
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(a, Type::Base(BaseType::String));
        table.unify(a, b).unwrap();
        // b should now see a's solution
        assert_eq!(table.probe(b), Some(Type::Base(BaseType::String)));
    }

    #[test]
    fn test_unify_then_solve_propagates() {
        // Complement of test_unify_propagates_solution: union first, then solve.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.unify(a, b).unwrap();
        // Neither solved yet.
        assert_eq!(table.probe(a), None);
        assert_eq!(table.probe(b), None);
        // Solve a; b should see the solution via the union.
        table.set(a, Type::Base(BaseType::Int));
        assert_eq!(table.probe(b), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_unify_prefers_solved_root() {
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(b, Type::Base(BaseType::Bool));
        // b is solved, a is not; unify should keep b's solution
        table.unify(a, b).unwrap();
        assert_eq!(table.probe(a), Some(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_path_compression() {
        // Chain: c → b → a; after find(c) all should point to a.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        let c = table.fresh_var();
        table.unify(b, a).unwrap(); // b links to a
        table.unify(c, b).unwrap(); // c links to b (root of b is a)
        let root_c = table.find(c);
        let root_a = table.find(a);
        assert_eq!(root_c, root_a);
    }

    #[test]
    fn test_resolve_replaces_infer_with_solution() {
        let mut table = UnificationTable::new();
        let id = table.fresh_var();
        table.set(id, Type::Base(BaseType::Int));
        let mut expr = Expr::lit(Lit::Int(0));
        expr.ty = Type::Infer(id);
        resolve(&mut expr, &mut table);
        assert_eq!(expr.ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn test_resolve_leaves_unsolved_infer() {
        let mut table = UnificationTable::new();
        let id = table.fresh_var();
        // No set() call — variable is unresolved.
        let mut expr = Expr::lit(Lit::Int(0));
        expr.ty = Type::Infer(id);
        resolve(&mut expr, &mut table);
        assert_eq!(expr.ty, Type::Infer(id));
    }

    #[test]
    fn test_unify_conflict_returns_err() {
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(a, Type::Base(BaseType::Int));
        table.set(b, Type::Base(BaseType::String));
        let result = table.unify(a, b);
        assert!(result.is_err());
        let (ty_a, ty_b) = result.unwrap_err();
        assert_eq!(ty_a, Type::Base(BaseType::Int));
        assert_eq!(ty_b, Type::Base(BaseType::String));
    }
}
