//! A module's parameters, and a `run` statement's arguments for them, as the module
//! lowers (`docs/chl-spec.md`, "9.4 Parameters").

use super::*;

impl LoweringContext {
    /// The rest of the module, `body`, below the `run` statement at `statement`
    /// that declares the run `name` of `module`: a [`TypedExprNode::Run`] over a
    /// `let` per value its `use` clause binds. The `let` keeps a generic member
    /// generic (`src/ccl/design/type-inference.md`, "A name of a generalized
    /// binding").
    pub(in crate::ccl::lower) fn take_run(
        &mut self,
        name: &str,
        module: ModulePath,
        statement: Span,
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
            body: Box::new(body),
        });
        self.tag_image(run, statement)
    }
}
