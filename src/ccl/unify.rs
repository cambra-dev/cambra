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

use std::{collections::HashMap, fmt::Display};

use log::trace;

use crate::ccl::{infer::InferError, Branch, InferVarId, Type};

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

impl Display for Entry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Root(Some(ty)) => write!(f, "{ty}"),
            Self::Root(None) => write!(f, "?"),
            Self::Link(id) => write!(f, "#{id}"),
        }
    }
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

impl Display for UnificationTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements: Vec<_> = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(i, e)| e.as_ref().map(|e| format!("{i}: {e}")))
            .collect();
        write!(f, "{}", elements.join("\n"))
    }
}

impl UnificationTable {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self::default()
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
        let existing = self.probe(root);
        trace!(
            "Setting variable #{id} to type {ty} with root #{root} (existing: {})",
            existing.as_ref().map_or("?".to_string(), |t| t.to_string())
        );

        // For PartialTuple/PartialRecord, merge entries instead of overwriting.
        // This lets a variable constrained by multiple projections (e.g. `.0` and
        // `.1` on the same parameter) accumulate all known index/field types.
        let to_store = match (existing, ty) {
            // Merge two PartialTuples: validate overlapping indices, append new ones.
            (Some(Type::PartialTuple(mut existing_entries)), Type::PartialTuple(new_entries)) => {
                for (new_idx, new_ty) in new_entries {
                    if let Some(pos) = existing_entries.iter().position(|(i, _)| *i == new_idx) {
                        // Clone before the constrain_equal call to release the index borrow.
                        let existing_ty = existing_entries[pos].1.clone();
                        self.constrain_equal(&existing_ty, &new_ty)
                            .unwrap_or_else(|_| {
                                panic!(
                                    "UnificationTable::set: type conflict at index {new_idx} \
                                 merging PartialTuple: {existing_ty} vs {new_ty}"
                                )
                            });
                    } else {
                        existing_entries.push((new_idx, new_ty));
                    }
                }
                Type::PartialTuple(existing_entries)
            }
            // Merge two PartialRecords: validate overlapping fields, append new ones.
            (Some(Type::PartialRecord(mut existing_entries)), Type::PartialRecord(new_entries)) => {
                for (new_name, new_ty) in new_entries {
                    if let Some(pos) = existing_entries.iter().position(|(n, _)| *n == new_name) {
                        let existing_ty = existing_entries[pos].1.clone();
                        self.constrain_equal(&existing_ty, &new_ty)
                            .unwrap_or_else(|_| {
                                panic!(
                                    "UnificationTable::set: type conflict for field '{new_name}' \
                                 merging PartialRecord: {existing_ty} vs {new_ty}"
                                )
                            });
                    } else {
                        existing_entries.push((new_name, new_ty));
                    }
                }
                Type::PartialRecord(existing_entries)
            }
            // Default: assert compatible (for equal types or Infer unification).
            (Some(existing_ty), ty) => {
                trace!("UnificationTable::set: asserting equality of existing type {existing_ty} and new type {ty}");
                assert!(
                    self.constrain_equal(&existing_ty, &ty).is_ok(),
                    "UnificationTable::set: variable {root:?} already solved to a different type: \
                     {existing_ty} vs {ty}"
                );
                existing_ty
            }
            (None, ty) => ty,
        };

        let idx = root.0 as usize;
        if idx < self.entries.len() {
            trace!("Storing type {to_store} for root #{root}");
            self.entries[idx] = Some(Entry::Root(Some(to_store)));
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
    /// Combines allocation and registration into one step
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
    pub fn unify(&mut self, a: InferVarId, b: InferVarId) -> Result<(), InferError> {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a == root_b {
            return Ok(()); // already in the same class
        }
        // Prefer keeping a solved root as the root.
        let solved_a = self.probe(root_a);
        let solved_b = self.probe(root_b);
        trace!(
            "Unifying {a} and {b}; roots {root_a} and {root_b} with types {:?} and {:?}",
            solved_a,
            solved_b
        );
        match (solved_a, solved_b) {
            (None, Some(_)) => {
                // b's root is solved; make a link to b's root and store type there.
                let idx_a = root_a.0 as usize;
                if idx_a < self.entries.len() {
                    self.entries[idx_a] = Some(Entry::Link(root_b));
                }
            }
            (Some(Type::PartialTuple(mut a_elts)), Some(Type::PartialTuple(mut b_elts))) => {
                a_elts.sort_by(|(l, _), (r, _)| l.cmp(r));
                b_elts.sort_by(|(l, _), (r, _)| l.cmp(r));
                let idx_a = root_a.0 as usize;
                let idx_b = root_b.0 as usize;
                let mut i_a = a_elts.iter();
                let mut i_b = b_elts.iter();
                let mut elts = Vec::new();
                let mut a = i_a.next();
                let mut b = i_b.next();
                while a.is_some() || b.is_some() {
                    if b.is_none() || a.is_some() && a.unwrap().0 < b.unwrap().0 {
                        elts.push(a.unwrap().clone());
                        a = i_a.next();
                    } else if a.is_none() || b.is_some() && b.unwrap().0 < a.unwrap().0 {
                        elts.push(b.unwrap().clone());
                        b = i_b.next();
                    } else {
                        self.constrain_equal(&a.unwrap().1, &b.unwrap().1)?;
                        elts.push(a.unwrap().clone());
                        a = i_a.next();
                        b = i_b.next();
                    }
                }
                let result = Type::PartialTuple(elts);
                self.entries[idx_a] = Some(Entry::Root(Some(result)));
                self.entries[idx_b] = Some(Entry::Link(root_a));
            }
            // TODO implement the above logic for records too.
            (Some(ty_a), Some(ty_b)) => {
                if ty_a != ty_b {
                    return self.constrain_equal(&ty_a, &ty_b);
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

    /// Constrain two types to be equal, recording the solution in the [`UnificationTable`].
    ///
    /// - Both `Infer`: union the two variables.
    /// - One `Infer`, one concrete: set the variable to the concrete type.
    /// - Both concrete and equal: no-op.
    /// - Both concrete and different: returns [`InferError::TypeMismatch`].
    /// - Structured types: recurse element-wise
    pub fn constrain_equal(&mut self, a: &Type, b: &Type) -> Result<(), InferError> {
        trace!("Constraining {a} and {b}");
        match (a, b) {
            (Type::Infer(a_id), Type::Infer(b_id)) => {
                self.unify(*a_id, *b_id)?;
                Ok(())
            }
            (Type::Infer(id), concrete) | (concrete, Type::Infer(id)) => {
                // Ensure this is a actually a concrete type: guards against case reordering.
                debug_assert!(!matches!(concrete, Type::Infer(_)));
                // If already solved, recurse to check compatibility rather than
                // calling set() directly — set() panics on conflict, but a
                // conflict here is a user-level type error that should propagate.
                if let Some(existing) = self.probe(*id) {
                    self.constrain_equal(&existing, concrete)?;
                    // PartialTuple/PartialRecord accumulate index/field knowledge across
                    // multiple usage sites (e.g. `x[0]` and `x[1]` on the same param).
                    // constrain_equal only validates overlapping entries; set() is the only
                    // path that merges non-overlapping ones into the stored value.
                    if matches!(concrete, Type::PartialTuple(_) | Type::PartialRecord(_)) {
                        self.set(*id, concrete.clone());
                    }
                } else {
                    self.set(*id, concrete.clone());
                }
                Ok(())
            }
            (Type::Fun(a_domain, a_codomain), Type::Fun(b_domain, b_codomain)) => self
                .constrain_equal(a_domain, b_domain)
                .and(self.constrain_equal(a_codomain, b_codomain)),
            // Constrain tuples index-wise.
            (Type::Tuple(a), Type::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(InferError::TypeMismatch {
                        ctx: "unify".to_string(),
                        type_a: Type::Tuple(a.clone()),
                        type_b: Type::Tuple(b.clone()),
                    });
                };
                a.iter()
                    .zip(b.iter())
                    .try_for_each(|(a, b)| self.constrain_equal(a, b))
            }
            // Constrain records field-wise
            (Type::Record(a), Type::Record(b)) => {
                if a.len() != b.len() {
                    return Err(InferError::TypeMismatch {
                        ctx: "unify".to_string(),
                        type_a: Type::Record(a.clone()),
                        type_b: Type::Record(b.clone()),
                    });
                };
                let a_map: HashMap<_, _> = a.iter().cloned().collect();
                for (f, b_ty) in b.iter() {
                    if let Some(a_ty) = a_map.get(f) {
                        self.constrain_equal(a_ty, b_ty)?;
                    } else {
                        return Err(InferError::TypeMismatch {
                            ctx: "unify".to_string(),
                            type_a: Type::Record(a.clone()),
                            type_b: Type::Record(b.clone()),
                        });
                    }
                }
                Ok(())
            }
            // PartialTuple ↔ Tuple: constrain each indexed element.
            // An out-of-bounds index is a type error — projecting beyond the tuple length.
            (Type::PartialTuple(partial), Type::Tuple(full))
            | (Type::Tuple(full), Type::PartialTuple(partial)) => {
                for (idx, ty) in partial {
                    match full.get(*idx) {
                        Some(full_ty) => self.constrain_equal(ty, full_ty)?,
                        None => {
                            return Err(InferError::TypeMismatch {
                                ctx: "unify".to_string(),
                                type_a: a.clone(),
                                type_b: b.clone(),
                            })
                        }
                    }
                }
                Ok(())
            }

            // PartialTuple ↔ PartialTuple: validate that overlapping indices agree.
            // Non-overlapping indices are unconstrained here; accumulation of all
            // known indices into the table happens via the Infer arm above (set()).
            (Type::PartialTuple(a), Type::PartialTuple(b)) => {
                let a_map: HashMap<usize, &Type> = a.iter().map(|(i, t)| (*i, t)).collect();
                for (idx, b_ty) in b {
                    if let Some(a_ty) = a_map.get(idx) {
                        self.constrain_equal(a_ty, b_ty)?;
                    }
                }
                Ok(())
            }

            // PartialRecord ↔ Record: constrain each named field.
            // A field present in the partial type but absent from the full record is a type error.
            (Type::PartialRecord(partial), Type::Record(full))
            | (Type::Record(full), Type::PartialRecord(partial)) => {
                let full_map: HashMap<&str, &Type> =
                    full.iter().map(|(n, t)| (n.as_str(), t)).collect();
                for (name, ty) in partial {
                    match full_map.get(name.as_str()) {
                        Some(full_ty) => self.constrain_equal(ty, full_ty)?,
                        None => {
                            return Err(InferError::TypeMismatch {
                                ctx: "unify".to_string(),
                                type_a: a.clone(),
                                type_b: b.clone(),
                            })
                        }
                    }
                }
                Ok(())
            }

            // PartialRecord ↔ PartialRecord: validate that overlapping fields agree.
            // Non-overlapping fields are unconstrained here; accumulation happens
            // via the Infer arm above (set()).
            (Type::PartialRecord(a), Type::PartialRecord(b)) => {
                let a_map: HashMap<&str, &Type> = a.iter().map(|(n, t)| (n.as_str(), t)).collect();
                for (name, b_ty) in b {
                    if let Some(a_ty) = a_map.get(name.as_str()) {
                        self.constrain_equal(a_ty, b_ty)?;
                    }
                }
                Ok(())
            }

            // TODO: This is a short-term workaround that treats all refinements as
            // compatible with each other. To make this sound, we need to emit a
            // subtyping constraint on these refinements, the checking of which can
            // be delegated to an SMT solver.
            (Type::Refinement(inner, _), other) | (other, Type::Refinement(inner, _)) => {
                self.constrain_equal(inner, other)
            }

            (a, b) if a == b => Ok(()),
            (type_a, type_b) => Err(InferError::TypeMismatch {
                ctx: "unify".to_string(),
                type_a: type_a.clone(),
                type_b: type_b.clone(),
            }),
        }
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
}

// ---------------------------------------------------------------------------
// Resolution pass
// ---------------------------------------------------------------------------

/// Find any Infer placeholders inside the given type and replace them with
/// concrete types if possible.
fn resolve_type(ty: &mut Type, table: &mut UnificationTable) {
    match ty {
        Type::Infer(id) => {
            if let Some(mut new_ty) = table.probe(*id) {
                // Recurse into the resolved type in case it is a composite type with unknown elements
                resolve_type(&mut new_ty, table);
                *ty = new_ty;
            }
        }
        Type::Fun(domain, codomain) => {
            resolve_type(domain, table);
            resolve_type(codomain, table);
        }
        Type::Tuple(types) => types.iter_mut().for_each(|t| resolve_type(t, table)),
        Type::Record(types) => types.iter_mut().for_each(|(_, t)| resolve_type(t, table)),
        Type::PartialTuple(entries) => {
            entries.iter_mut().for_each(|(_, t)| resolve_type(t, table));
            // When body inference only constrains some indices of a tuple param
            // (e.g. `x[0]` and `x[1]`), the table accumulates a PartialTuple.
            // If the known indices form a complete range [0, N), the PartialTuple
            // carries the same information as Tuple([T0..Tn-1]) and must be
            // presented that way — the compiler cannot handle PartialTuple directly.
            // Reaching compilation with a non-promotable PartialTuple is a compiler
            // invariant violation (type inference should have rejected the program).
            entries.sort_by_key(|(i, _)| *i);
            let is_complete = !entries.is_empty()
                && entries
                    .iter()
                    .enumerate()
                    .all(|(pos, (idx, _))| pos == *idx);
            if is_complete {
                let types: Vec<Type> = entries.drain(..).map(|(_, t)| t).collect();
                *ty = Type::Tuple(types);
            }
        }
        Type::PartialRecord(entries) => {
            entries.iter_mut().for_each(|(_, t)| resolve_type(t, table))
        }
        Type::Union(variants) => variants.iter_mut().for_each(|t| resolve_type(t, table)),
        // Resolve the base type inside a refinement; the predicate is a separate expression
        // and is resolved via the expression-level resolve() pass.
        Type::Refinement(inner, _) => resolve_type(inner, table),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole => {}
    };
}

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

    // Resolve this node's type slot, recursing into composite types
    resolve_type(&mut expr.ty, table);
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
            resolve_type(&mut param.ty, table);
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
            resolve_type(&mut binding.ty, table);
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
        TypedExprNode::Proj(_) => {} // leaf: no sub-expressions to resolve
        TypedExprNode::Aggregate { input, .. } => resolve(input, table),
        TypedExprNode::GroupBy { collection, key } => {
            resolve(collection, table);
            resolve(key, table);
        }
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches {
                resolve(guard, table);
                resolve(body, table);
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
        TypedExprNode::Compose(elts) => {
            for e in elts {
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
        let InferError::TypeMismatch { type_a, type_b, .. } = result.unwrap_err() else {
            panic!("Expected error")
        };
        assert_eq!(type_a, Type::Base(BaseType::Int));
        assert_eq!(type_b, Type::Base(BaseType::String));
    }

    // ---------------------------------------------------------------------------
    // constrain_equal tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_constrain_equal_two_infer_vars_unions_them() {
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table
            .constrain_equal(&Type::Infer(a), &Type::Infer(b))
            .unwrap();
        // Setting one should be visible through the other.
        table.set(a, Type::Base(BaseType::Int));
        assert_eq!(table.probe(b), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_constrain_equal_infer_and_concrete_solves_var() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        table
            .constrain_equal(&Type::Infer(v), &Type::Base(BaseType::Bool))
            .unwrap();
        assert_eq!(table.probe(v), Some(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_constrain_equal_concrete_and_infer_solves_var() {
        // Same as above but arguments are swapped — both orders must work.
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        table
            .constrain_equal(&Type::Base(BaseType::UInt), &Type::Infer(v))
            .unwrap();
        assert_eq!(table.probe(v), Some(Type::Base(BaseType::UInt)));
    }

    #[test]
    fn test_constrain_equal_same_concrete_types_is_ok() {
        let mut table = UnificationTable::new();
        let result =
            table.constrain_equal(&Type::Base(BaseType::String), &Type::Base(BaseType::String));
        assert!(result.is_ok());
    }

    #[test]
    fn test_constrain_equal_different_concrete_types_is_err() {
        let mut table = UnificationTable::new();
        let result = table.constrain_equal(&Type::Base(BaseType::Int), &Type::Base(BaseType::Bool));
        assert!(matches!(result, Err(InferError::TypeMismatch { .. })));
    }

    #[test]
    fn test_constrain_equal_fun_types_compatible() {
        // (Int → Bool) == (Int → Bool) should succeed and leave no unsolved vars.
        let mut table = UnificationTable::new();
        let a = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Bool)),
        );
        let b = a.clone();
        assert!(table.constrain_equal(&a, &b).is_ok());
    }

    #[test]
    fn test_constrain_equal_fun_types_solves_infer_components() {
        // (Infer(d) → Bool) == (Int → Bool) should solve d = Int.
        let mut table = UnificationTable::new();
        let d = table.fresh_var();
        let lhs = Type::Fun(
            Box::new(Type::Infer(d)),
            Box::new(Type::Base(BaseType::Bool)),
        );
        let rhs = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Bool)),
        );
        table.constrain_equal(&lhs, &rhs).unwrap();
        assert_eq!(table.probe(d), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_constrain_equal_fun_types_domain_mismatch_is_err() {
        let mut table = UnificationTable::new();
        let lhs = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Bool)),
        );
        let rhs = Type::Fun(
            Box::new(Type::Base(BaseType::String)),
            Box::new(Type::Base(BaseType::Bool)),
        );
        assert!(matches!(
            table.constrain_equal(&lhs, &rhs),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_constrain_equal_tuple_types_compatible() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        let lhs = Type::Tuple(vec![Type::Infer(v), Type::Base(BaseType::Bool)]);
        let rhs = Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Bool)]);
        table.constrain_equal(&lhs, &rhs).unwrap();
        assert_eq!(table.probe(v), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_constrain_equal_tuple_types_mismatch_is_err() {
        let mut table = UnificationTable::new();
        let lhs = Type::Tuple(vec![Type::Base(BaseType::Int)]);
        let rhs = Type::Tuple(vec![Type::Base(BaseType::Bool)]);
        assert!(matches!(
            table.constrain_equal(&lhs, &rhs),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_constrain_equal_record_types_field_wise() {
        let mut table = UnificationTable::new();
        let v = table.fresh_var();
        let lhs = Type::Record(vec![
            ("x".to_string(), Type::Infer(v)),
            ("y".to_string(), Type::Base(BaseType::Bool)),
        ]);
        let rhs = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::Bool)),
        ]);
        table.constrain_equal(&lhs, &rhs).unwrap();
        assert_eq!(table.probe(v), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_constrain_equal_record_types_field_mismatch_is_err() {
        let mut table = UnificationTable::new();
        let lhs = Type::Record(vec![("x".to_string(), Type::Base(BaseType::Int))]);
        let rhs = Type::Record(vec![("x".to_string(), Type::Base(BaseType::Bool))]);
        assert!(matches!(
            table.constrain_equal(&lhs, &rhs),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    // ---------------------------------------------------------------------------
    // resolve tests — composite and chained cases
    // ---------------------------------------------------------------------------

    #[test]
    fn test_resolve_fun_type_with_infer_components() {
        // An expression typed Fun(Infer(d), Infer(c)) should have both vars resolved.
        let mut table = UnificationTable::new();
        let d = table.fresh_var();
        let c = table.fresh_var();
        table.set(d, Type::Base(BaseType::Int));
        table.set(c, Type::Base(BaseType::Bool));

        let mut expr = Expr::lit(Lit::Int(0)).with_ty(Type::Fun(
            Box::new(Type::Infer(d)),
            Box::new(Type::Infer(c)),
        ));
        resolve(&mut expr, &mut table);
        assert_eq!(
            expr.ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Bool))
            )
        );
    }

    #[test]
    fn test_resolve_chained_infer_variables() {
        // Infer(a) → Infer(b) → Int: resolving a should eventually yield Int.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(b, Type::Base(BaseType::Int));
        // Union a and b so a resolves through b.
        table.unify(a, b).unwrap();

        let mut expr = Expr::lit(Lit::Int(0)).with_ty(Type::Infer(a));
        resolve(&mut expr, &mut table);
        assert_eq!(expr.ty, Type::Base(BaseType::Int));
    }

    // ---------------------------------------------------------------------------
    // PartialTuple / PartialRecord constrain_equal tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_partial_tuple_vs_tuple_constrains_indexed_field() {
        // PartialTuple({0 => ?a}) ↔ Tuple([Int, String]) should solve ?a = Int.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let partial = Type::PartialTuple(vec![(0, Type::Infer(a))]);
        let full = Type::Tuple(vec![
            Type::Base(BaseType::Int),
            Type::Base(BaseType::String),
        ]);
        table.constrain_equal(&partial, &full).unwrap();
        assert_eq!(table.probe(a), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_partial_tuple_vs_tuple_out_of_bounds_is_err() {
        // PartialTuple({2 => ?a}) ↔ Tuple([Int, String]) — index 2 is out of bounds.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let partial = Type::PartialTuple(vec![(2, Type::Infer(a))]);
        let full = Type::Tuple(vec![
            Type::Base(BaseType::Int),
            Type::Base(BaseType::String),
        ]);
        assert!(matches!(
            table.constrain_equal(&partial, &full),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_partial_tuple_vs_partial_tuple_overlapping_index_is_compatible() {
        // PartialTuple({0 => Int}) ↔ PartialTuple({0 => Int}) — same index, same type.
        let mut table = UnificationTable::new();
        let lhs = Type::PartialTuple(vec![(0, Type::Base(BaseType::Int))]);
        let rhs = Type::PartialTuple(vec![(0, Type::Base(BaseType::Int))]);
        assert!(table.constrain_equal(&lhs, &rhs).is_ok());
    }

    #[test]
    fn test_partial_tuple_vs_partial_tuple_overlapping_index_conflict_is_err() {
        // PartialTuple({0 => Int}) ↔ PartialTuple({0 => String}) — type conflict at index 0.
        let mut table = UnificationTable::new();
        let lhs = Type::PartialTuple(vec![(0, Type::Base(BaseType::Int))]);
        let rhs = Type::PartialTuple(vec![(0, Type::Base(BaseType::String))]);
        assert!(matches!(
            table.constrain_equal(&lhs, &rhs),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_partial_record_vs_record_constrains_matching_field() {
        // PartialRecord({x => ?a}) ↔ Record([x: Int, y: Bool]) should solve ?a = Int.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let partial = Type::PartialRecord(vec![("x".to_string(), Type::Infer(a))]);
        let full = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::Bool)),
        ]);
        table.constrain_equal(&partial, &full).unwrap();
        assert_eq!(table.probe(a), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_partial_record_vs_record_missing_field_is_err() {
        // PartialRecord({z => ?a}) ↔ Record([x: Int, y: Bool]) — field z is absent.
        let mut table = UnificationTable::new();
        let a = table.fresh_var();
        let partial = Type::PartialRecord(vec![("z".to_string(), Type::Infer(a))]);
        let full = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::Bool)),
        ]);
        assert!(matches!(
            table.constrain_equal(&partial, &full),
            Err(InferError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_partial_record_vs_partial_record_overlapping_field_compatible() {
        // PartialRecord({x => Int}) ↔ PartialRecord({x => Int}) — same field, same type.
        let mut table = UnificationTable::new();
        let lhs = Type::PartialRecord(vec![("x".to_string(), Type::Base(BaseType::Int))]);
        let rhs = Type::PartialRecord(vec![("x".to_string(), Type::Base(BaseType::Int))]);
        assert!(table.constrain_equal(&lhs, &rhs).is_ok());
    }

    #[test]
    fn test_partial_tuple_merge_via_set() {
        // ?p constrained by both .0 (Int) and .1 (String) — set should accumulate both.
        let mut table = UnificationTable::new();
        let p = table.fresh_var();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(a, Type::Base(BaseType::Int));
        table.set(b, Type::Base(BaseType::String));
        table.set(p, Type::PartialTuple(vec![(0, Type::Infer(a))]));
        table.set(p, Type::PartialTuple(vec![(1, Type::Infer(b))]));
        // After merge, p should see both index 0 and index 1.
        let ty = table.probe(p).expect("p should be solved");
        assert!(
            matches!(&ty, Type::PartialTuple(entries) if entries.len() == 2),
            "expected merged PartialTuple with 2 entries, got {ty}"
        );
    }

    #[test]
    fn test_partial_record_merge_via_set() {
        // ?r constrained by both .x (Int) and .y (Bool) — set should accumulate both.
        let mut table = UnificationTable::new();
        let r = table.fresh_var();
        let a = table.fresh_var();
        let b = table.fresh_var();
        table.set(a, Type::Base(BaseType::Int));
        table.set(b, Type::Base(BaseType::Bool));
        table.set(
            r,
            Type::PartialRecord(vec![("x".to_string(), Type::Infer(a))]),
        );
        table.set(
            r,
            Type::PartialRecord(vec![("y".to_string(), Type::Infer(b))]),
        );
        let ty = table.probe(r).expect("r should be solved");
        assert!(
            matches!(&ty, Type::PartialRecord(entries) if entries.len() == 2),
            "expected merged PartialRecord with 2 entries, got {ty}"
        );
    }

    #[test]
    fn test_resolve_apply_recurses_into_subexprs() {
        let mut table = UnificationTable::new();
        let fn_var = table.fresh_var();
        let arg_var = table.fresh_var();
        table.set(fn_var, Type::Base(BaseType::Int));
        table.set(arg_var, Type::Base(BaseType::Bool));

        let mut expr = Expr::new(crate::ccl::TypedExprNode::Apply {
            function: Box::new(Expr::lit(Lit::Int(0)).with_ty(Type::Infer(fn_var))),
            argument: Box::new(Expr::lit(Lit::Int(1)).with_ty(Type::Infer(arg_var))),
        })
        .with_ty(Type::Base(BaseType::Unit));

        resolve(&mut expr, &mut table);

        let crate::ccl::TypedExprNode::Apply { function, argument } = &expr.node else {
            panic!("expected Apply");
        };
        assert_eq!(function.ty, Type::Base(BaseType::Int));
        assert_eq!(argument.ty, Type::Base(BaseType::Bool));
    }
}
