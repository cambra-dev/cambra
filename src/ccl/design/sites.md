# Sites

A site names where a feed or a call stands in a running program: the place it is written, the calls
that reached that place, and the run that evaluates them. A channel fed from several sites tags each
contribution with its site, so an edit to the program moves the tag of no feed it does not touch,
apart from the cases [Stability](#stability) lists.

## Places

A place (`chl_parser::places::Place`) is a feed, a `yield` or a named call as written. It holds:

- the path of the module whose source holds it, empty for the root;
- the bindings the author wrote around it, outermost first;
- its kind (`Feed`, `Yield`, `Call`) and its spelling: a feed's target, `yield`, or the callee's
  name (`f`, `m::f`, a method's name, a called field's name);
- its index among the places that share all of the above, counted in source order.

The bindings that enclose a place are the names an assignment to a single name binds (`x = …`,
`x: T = …`, `x := …`, `x <<= …`), each `def`'s name, a `def`'s owner type before it, and an
`impl` block's head name (a type's or a trait's) before each of its `def`s.

`chl_parser::places::places` is the one numbering. It walks a module's syntax once, in source order,
and answers each place by a span: a feed's target's, a `yield`'s own, a call's callee's, a method
call's method name's, a field callee's field name's. Lowering numbers each module as it starts it
(`Naming::add_module`) and looks each feed's and each named call's place up by that span
(`Naming::site`). A feed or a named call with no place there is a lowering bug, and the lookup
panics.

## Sites

A site (`crate::ccl::site::Site`) is a place, the places of the calls that reached it outermost
first, and the run's path (`RunPath`). Each IR form carries its site in one slot:

- a feed carries it in `TypedExprNode::Feed`'s `site`;
- a call carries it on the callee's `Var`, in `TypedExpr::site`;
- a call of an intrinsic, a reading, carries it in `Reading::site`, which keys the values the run
  reads for it (`src/ccl/design/ir.md`, "Readings").

Three passes change a site:

- Lowering creates it, with no calls and the root's run.
- Linking puts it under the run that evaluates the module's copy (`Site::in_run`).
- Inlining extends each site in a copied body with the call that copied it (`Site::through`, in
  `inline.rs`): the call's run and calls, then the call's place, then the copied site's own calls.

A function bound by a `let` is copied once per call the same way (`substitute_function`). A copy
that is not a call takes no call's place.

A field callee, `(r.f)(x)`, is the place of a call spelled by the field. Lowering puts its site on
the projection `r ▷ .f`. Splitting a product binding moves that site onto the variable that replaces
the projection, so the component is copied through it as a `let`-bound function is
(`split_product_let`). Folding a projection of a product written in place reaches the component
through it (`fold_product_projection`).

Every other pass keeps a node's site wherever it keeps the node, a clone included. A pass that
rebuilds a `Feed` passes its `site` on.

## Channel tags

A channel fed from one site keeps its keys. A channel fed from several is the copairing of its
contributions (`channelize`, `combine_feed_values`), and arm 𝑖 is tagged by its site's tag,
`FieldKey::Name`:

```text
run/call/call/place
```

`chl_parser::places::site_tag` spells it. The run's path comes first, then each call's place and
the feed's place, separated by `/`. A label's `::` names its module, so the tag spells each `::` as
`.`.

`channelize` sorts the contributions by tag, so a channel's arms are in canonical `TagMap` order
whatever order the passes before it left the feeds in. Two contributions with one tag panic
(`site_tags`).

Three consumers take the tags from the channel's type. Inference and `Check` re-emit a recorded
copairing with its recorded tags (`emit_copair`). Operator conversion reads them off the type
(`copair_tags`), and `UnionOperator` keys each arm by its operand's tag. A `++` copairing keeps
positional `FieldKey::Index` tags.

## Stability

A site moves only when one of its places moves. A place moves only when the program gains or loses
a place before it that shares its module, bindings, kind and spelling, or when a binding around it
is renamed. A call of another function, a feed of another target, or a change to another binding's
definition moves nothing.

A run's path names the runs from the root to it, so renaming a run moves the sites under it.

## The reference interpreter

`chl-interp` takes its places from `chl_parser::places::places` as well, by span start. A
contribution's tag spells every named call running when the feed fires, outermost first, then the
feed's place (`Interp::feed_site`). Those are the calls inlining copies the feed through. The
interpreter runs one module, so a tag has no run path.
