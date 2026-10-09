//! A module's parameters, and a `run` statement's arguments for them, as the module
//! lowers (`docs/chl-spec.md`, "9.4 Parameters").

use super::*;

impl LoweringContext {
    /// The rest of the module, `body`, below the `run` statement at `statement`
    /// that declares the run `name` of `module` with `arguments`: a
    /// [`TypedExprNode::Run`] over a `let` per value its `use` clause binds,
    /// below a `let` per argument. The `use` name's `let` keeps a generic member
    /// generic (`src/ccl/design/type-inference.md`, "A name of a generalized
    /// binding").
    ///
    /// Each argument is bound under the name its parameter reads
    /// ([`argument_name`]), at the parameter's type spelled through the run name
    /// ([`reroot`]), so a mismatch is the argument's error.
    pub(in crate::ccl::lower) fn take_run(
        &mut self,
        name: &str,
        module: ModulePath,
        statement: Span,
        arguments: Vec<(SmolStr, Span, Expr)>,
        body: Expr,
    ) -> Expr {
        let mut used: Vec<(SmolStr, QualifiedName, Span)> = self
            .module
            .uses
            .iter()
            .filter(|(_, used)| used.run.as_deref() == Some(name))
            .filter_map(|(bound, used)| match &used.reached {
                Reached::Value(Some(reference)) => {
                    Some((bound.clone(), reference.name.clone(), used.item))
                }
                Reached::Value(None) | Reached::Type(_) => None,
            })
            .collect();
        used.sort_by(|l, r| l.0.cmp(&r.0));
        // Each `let` and its member reference image the `use` item that binds
        // the name.
        let body = used
            .into_iter()
            .rev()
            .fold(body, |body, (bound, member, item)| {
                let member = self.tag_image(Expr::var(member.raw()), item);
                let bound = Expr::let_bind(bound.as_str(), member, body);
                self.tag_image(bound, item)
            });
        let run = Expr::new(TypedExprNode::Run {
            name: name.into(),
            module,
            statement,
            arguments: arguments
                .iter()
                .map(|(parameter, ..)| parameter.clone())
                .collect(),
            body: Box::new(body),
        });
        let run = self.tag_image(run, statement);
        let parameters: HashMap<SmolStr, Option<Type>> = self
            .module
            .qualifiers
            .get(name)
            .and_then(|qualifier| qualifier.interface.as_ref())
            .map(|interface| {
                interface
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let ty = parameter.annotation.as_ref().map(|ty| reroot(ty, name));
                        (parameter.name.clone(), ty)
                    })
                    .collect()
            })
            .unwrap_or_default();
        arguments
            .into_iter()
            .rev()
            .fold(run, |body, (parameter, span, value)| {
                let bound = argument_name(name, &parameter);
                let bound = match parameters.get(&parameter).cloned().flatten() {
                    Some(ty) => Expr::let_bind_annotated(bound, value, body, ty),
                    None => Expr::let_bind(bound, value, body),
                };
                self.tag_image(bound, span)
            })
    }
}

/// The name the argument for the parameter `parameter` of the run `run` is
/// bound under, above the run, and read under by the parameter's `let`. No user
/// binder takes a double-underscore name, run names are unique in their module,
/// and `::` separates the run name from the parameter, so no two arguments in
/// one module share one.
pub(super) fn argument_name(run: &str, parameter: &str) -> Name {
    QualifiedName::new("__run")
        .child(run)
        .child(parameter)
        .raw()
}

/// The `let` of the parameter `parameter` in `chain`, a copy of a module's
/// chain, which its parameters' `let`s head.
pub(super) fn parameter_let<'a>(chain: &'a mut Expr, parameter: &str) -> &'a mut Expr {
    let mut at = chain;
    loop {
        let TypedExprNode::Let { binding, .. } = &at.node else {
            unreachable!("a module's parameters head its chain, and `{parameter}` is one");
        };
        if matches!(&binding.name, Name::Raw(spelling) if spelling == parameter) {
            return at;
        }
        let TypedExprNode::Let { body, .. } = &mut at.node else {
            unreachable!("matched a `let` above");
        };
        at = body;
    }
}

/// `chain`, a copy of a module's chain, with the `let` of its parameter
/// `parameter`, which heads it, bound to `argument` in place of its default.
pub(super) fn read_argument(chain: &mut Expr, parameter: &str, argument: Expr) {
    let TypedExprNode::Let { bound_expr, .. } = &mut parameter_let(chain, parameter).node else {
        unreachable!("a parameter's `let` is a `let`");
    };
    **bound_expr = argument;
}
