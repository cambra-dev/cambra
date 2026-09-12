Here is the original program.

```
x := 10
y := 5
begin():
    x := x + 1
    x := x + y
    y := y + y
    y := 2
    z := y
    y := y + z
await_final(y)
```

It is flattened into the following program.

```
x := 10
y := 5
begin():
    # Initialization, import mutable values
    x0 = x
    y0 = y

    # Local immutable manipulation
    x1 = x0 + 1
    x2 = x1 + y0
    y1 = y0 + y0
    y2 = 2
    z0 = y2
    y3 = y2 + z0
    
    # Use mutation only to export results
    x := x2
    y := y3
await_final(y)
```

Note that though `z` was mutable, since its declaration is local to
the transaction body, it is replaced by immutable bindings, and is not
exported.

Mutation within the body is restricted to the initialization
statements at the begininning and the export statements at the end.

The export statements must not reference mutable variables on the rhs: only local immutable variables.
