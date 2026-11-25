//! Places hold values; reading a place and borrowing it are distinct operations.

use crate::ccl::provenance::NodeId;
use crate::ccl::{ProjKey, Type};

/// How a source parameter receives its argument. Lowering infers a borrow from a parameter
/// the body writes, feeds or passes on with `&`, or from a place annotation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ParameterMode {
    /// The parameter receives a value; a place passed to it is read.
    #[default]
    Value,
    /// The parameter borrows a place for the call, passed with `&`.
    Borrow,
}

/// What a place holds, which decides how it may be borrowed and captured.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PlaceKind {
    /// An induction `Mut(V)`.
    Mutable,
    /// A transactional `Mut(V, Txn)`.
    Transactional,
    /// A `Feed(T)`.
    Deferred,
}

impl PlaceKind {
    /// Whether one call may hold this place at most once: its writes overwrite.
    pub fn is_exclusive(self) -> bool {
        matches!(self, Self::Mutable | Self::Transactional)
    }

    /// Whether a function may write this place through a capture: commit time orders
    /// transactional writes, and contributions to a Feed need no order. An induction
    /// variable's writes need their position in its history.
    pub fn allows_captured_writes(self) -> bool {
        matches!(self, Self::Transactional | Self::Deferred)
    }
}

/// The type of a place and the ordinary value obtained by reading it.
pub struct PlaceType<'a> {
    pub kind: PlaceKind,
    /// The type a value read of the place has: a `Mut`'s value, a `Feed`'s collection.
    pub value: &'a Type,
}

/// Declaration identity and projections identify a place independently of local names.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: NodeId,
    pub path: Vec<ProjKey>,
}

impl Place {
    pub fn overlaps(&self, other: &Self) -> bool {
        self.root == other.root
            && (self.path.starts_with(&other.path) || other.path.starts_with(&self.path))
    }
}

/// Visit every place type in `ty`, with whether it stands where a place may: the whole type of a
/// declaration or a parameter (`at_top`), or a parameter of a function type, whose product
/// domain is its parameter list. Anywhere else a place would be part of another type, a tuple,
/// a record, a collection's or a feed's values, a `Mut`'s value or a function's result, and a
/// place type nests in nothing (`docs/chl-spec.md`, "Places and values"). Lowering refuses a
/// written type by this rule, and the check after inference applies it to every inferred one.
pub fn visit_places<'a>(ty: &'a Type, at_top: bool, visit: &mut impl FnMut(&'a Type, bool)) {
    match ty {
        Type::History { .. } => {
            visit(ty, at_top);
            let (domain, value, _) = ty.history_parts().expect("matched a history");
            visit_places(value, false, visit);
            visit_places(domain, false, visit);
        }
        Type::Fun {
            binder,
            domain,
            codomain,
            ..
        } => {
            // Which parts are places does not depend on the type `let`s around them.
            match domain.former() {
                Type::Tuple(ts) if binder.parameter_count().is_some() => {
                    ts.iter().for_each(|t| visit_places(t, true, visit))
                }
                Type::DepTuple(cs) if binder.parameter_count().is_some() => {
                    cs.iter().for_each(|(_, t)| visit_places(t, true, visit))
                }
                _ => visit_places(domain, true, visit),
            }
            visit_places(codomain, false, visit);
        }
        Type::Refinement(base, _) => visit_places(base, at_top, visit),
        _ => ty.walk_children(|c| visit_places(c, false, visit)),
    }
}

/// The first place type in `ty` that stands where no place may ([`visit_places`]).
pub fn misplaced(ty: &Type, at_top: bool) -> Option<&Type> {
    let mut found = None;
    visit_places(ty, at_top, &mut |place, allowed| {
        if !allowed && found.is_none() {
            found = Some(place);
        }
    });
    found
}

/// The refusal of a place type `ty` standing inside another type.
pub fn nested_place_message(ty: &str) -> String {
    format!(
        "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, \
         a feed's values or a function's result: {ty}"
    )
}

/// Compiler bindings of borrowed places retain their annotation check, while every use
/// names the lent place's declaration before read naming and capability inference.
pub(crate) fn resolve_borrow_bindings(expr: &mut crate::ccl::Expr) {
    use crate::ccl::TypedExprNode;
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
        && binding.parameter_mode == ParameterMode::Borrow
        && binding.annotation_ty().unwrap_or(&binding.ty).is_place()
    {
        let place = match &bound_expr.node {
            TypedExprNode::Borrow(place) => &**place,
            _ => &**bound_expr,
        };
        if let TypedExprNode::Var(root) = &place.node {
            crate::ccl::subst::Subst::rename(binding.name.clone(), root.clone()).rewrite_expr(body);
        }
    }
    expr.walk_children_mut(resolve_borrow_bindings);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_a_parameter_list_can_contain_several_place_parameters() {
        let feed = Type::feed(Type::Hole, Type::Base(crate::ccl::BaseType::Int));
        let unit = Type::Base(crate::ccl::BaseType::Unit);
        let tuple_argument = Type::fun(Type::tuple(vec![feed.clone(), unit.clone()]), unit.clone());
        assert!(misplaced(&tuple_argument, false).is_some());
        let parameters = Type::fun_of_params(
            vec![("out".into(), feed), ("value".into(), unit.clone())],
            unit,
            crate::ccl::FunKind::Compute,
        );
        assert!(misplaced(&parameters, false).is_none());
    }
}
