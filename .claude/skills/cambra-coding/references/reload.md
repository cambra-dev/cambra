# Hot reload

A running program takes a new version of its source without losing its state. The spec owns the
surface ([8.8 `@LoadFrom`](../../../../docs/chl-spec.md#88-loadfrom)); the mechanism, the control
port and every refusal are in
[program-evolution.md](../../../../src/ccl/design/program-evolution.md).

## Driving a reload

```bash
cargo run --release -- --control prog.cambra          # control port DEFAULT_CONTROL_PORT, 8081
curl -X POST --data-binary @v2.cambra localhost:8081/diff     # preview what changes
curl -X POST --data-binary @v2.cambra localhost:8081/reload   # swap; 200, or 400 naming the refusal
```

A posted version is one file, so a program of several modules cannot be reloaded. The routes,
branches included, are the table in `src/control_port.rs`'s module comment. A branch is
a second version running beside the first
([`/branch`](../../../../src/ccl/design/program-evolution.md#branch)).

## What carries over

- A mutable variable keeps its value when the new version declares it under the same name, at a type
  its value fits. Logic, routes and loops may change freely around it.
- A reload never runs an iteration again for an input consumed before it. A statement the new version
  adds to a loop runs only for inputs that arrive after the reload. A variable the new version adds
  starts at its initializer, with nothing written to it for earlier inputs.
- A rename loads the old value into a plain binding, and the new variable starts from it:

  ```python
  @LoadFrom(qty)
  held: String
  items: Mut(String, Txn) := "[" + held + "]"
  ```

  `held`'s annotation is the value type, not `Mut(…)`. `@LoadFrom`'s argument is a name, never a
  field or an expression. A source containing `@LoadFrom` is valid only as a reload of a program that
  holds that variable. The source cannot be compiled from nothing, and reloading it a second time is
  refused, so the decorator comes out in the next version.

## What is refused

[Six refusals](../../../../src/ccl/design/program-evolution.md#six-refusals) lists them all. The
ones an author meets:

- A version that drops a variable holding state: ``` `x` is no longer declared```. `@Discard` is
  `[Decided]` and unimplemented, so retire a variable by loading it into a name nothing reads.
- A variable kept at a type its value does not fit.
- Any state whose type mentions a nominal type (`type Bill = …`), an unchanged declaration included.
