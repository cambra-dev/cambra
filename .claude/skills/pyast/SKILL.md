---
name: pyast
description: >
  Reference for rustpython_parser v0.2.0 AST types. Use when working with
  Python AST lowering, ExprKind, StmtKind, Operator, Constant, Comprehension,
  or any rustpython_parser type.
user-invocable: true
---

# rustpython_parser v0.2.0 — Quick Reference

**Crate**: `rustpython-parser = "0.2.0"` (re-exports `rustpython-ast`)

## Parser API

```rust
use rustpython_parser::{parser, ast};

parser::parse(source, Mode::Expression, "<path>") -> Result<ast::Mod, ParseError>
parser::parse_expression(source, "<path>")        -> Result<ast::Expr, ParseError>
parser::parse_program(source, "<path>")           -> Result<ast::Suite, ParseError>
```

**Mode**: `Module` | `Interactive` | `Expression`

**Mod**: `Module { body, type_ignores }` | `Interactive { body }` | `Expression { body: Box<Expr> }` | `FunctionType { argtypes, returns }`

## Located<T> Wrapper

```rust
pub struct Located<T, U = ()> {
    pub location: Location,
    pub end_location: Option<Location>,
    pub custom: U,
    pub node: T,       // <-- access the AST node here
}
```

**Type aliases**: `Expr = Located<ExprKind>`, `Stmt = Located<StmtKind>`, `Arg = Located<ArgData>`, `Keyword = Located<KeywordData>`, `Alias = Located<AliasData>`

## ExprKind — All Variants

| Variant | Fields |
|---------|--------|
| `BoolOp` | `op: Boolop, values: Vec<Expr>` |
| `NamedExpr` | `target: Box<Expr>, value: Box<Expr>` |
| `BinOp` | `left: Box<Expr>, op: Operator, right: Box<Expr>` |
| `UnaryOp` | `op: Unaryop, operand: Box<Expr>` |
| `Lambda` | `args: Box<Arguments>, body: Box<Expr>` |
| `IfExp` | `test: Box<Expr>, body: Box<Expr>, orelse: Box<Expr>` |
| `Dict` | `keys: Vec<Expr>, values: Vec<Expr>` |
| `Set` | `elts: Vec<Expr>` |
| `ListComp` | `elt: Box<Expr>, generators: Vec<Comprehension>` |
| `SetComp` | `elt: Box<Expr>, generators: Vec<Comprehension>` |
| `DictComp` | `key: Box<Expr>, value: Box<Expr>, generators: Vec<Comprehension>` |
| `GeneratorExp` | `elt: Box<Expr>, generators: Vec<Comprehension>` |
| `Await` | `value: Box<Expr>` |
| `Yield` | `value: Option<Box<Expr>>` |
| `YieldFrom` | `value: Box<Expr>` |
| `Compare` | `left: Box<Expr>, ops: Vec<Cmpop>, comparators: Vec<Expr>` |
| `Call` | `func: Box<Expr>, args: Vec<Expr>, keywords: Vec<Keyword>` |
| `FormattedValue` | `value: Box<Expr>, conversion: usize, format_spec: Option<Box<Expr>>` |
| `JoinedStr` | `values: Vec<Expr>` |
| `Constant` | `value: Constant, kind: Option<String>` |
| `Attribute` | `value: Box<Expr>, attr: Ident, ctx: ExprContext` |
| `Subscript` | `value: Box<Expr>, slice: Box<Expr>, ctx: ExprContext` |
| `Starred` | `value: Box<Expr>, ctx: ExprContext` |
| `Name` | `id: Ident, ctx: ExprContext` |
| `List` | `elts: Vec<Expr>, ctx: ExprContext` |
| `Tuple` | `elts: Vec<Expr>, ctx: ExprContext` |
| `Slice` | `lower: Option<Box<Expr>>, upper: Option<Box<Expr>>, step: Option<Box<Expr>>` |

## Operator (binary arithmetic/bitwise)

`Add` | `Sub` | `Mult` | `MatMult` | `Div` | `Mod` | `Pow` | `LShift` | `RShift` | `BitOr` | `BitXor` | `BitAnd` | `FloorDiv`

## Constant

`None` | `Bool(bool)` | `Str(String)` | `Bytes(Vec<u8>)` | `Int(BigInt)` | `Float(f64)` | `Complex { real: f64, imag: f64 }` | `Tuple(Vec<Constant>)` | `Ellipsis`

## Comprehension

```rust
pub struct Comprehension<U = ()> {
    pub target: Expr<U>,   // loop variable (usually Name with Store ctx)
    pub iter: Expr<U>,     // iterable expression
    pub ifs: Vec<Expr<U>>, // filter conditions
    pub is_async: usize,   // 0 = sync, 1 = async
}
```

## ExprContext

`Load` | `Store` | `Del`

## Boolop / Unaryop / Cmpop

- **Boolop**: `And` | `Or`
- **Unaryop**: `Invert` | `Not` | `UAdd` | `USub`
- **Cmpop**: `Eq` | `NotEq` | `Lt` | `LtE` | `Gt` | `GtE` | `Is` | `IsNot` | `In` | `NotIn`

## Cambra Usage Patterns (from `src/lowering.rs`)

```rust
use rustpython_parser::ast as pyast;

// Parse expression → match on .node
fn lower_expr(expr: &pyast::Located<pyast::ExprKind>) -> Result<...> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => ...,
        pyast::ExprKind::Name { id, .. }        => ...,
        pyast::ExprKind::BinOp { left, op, right } => ...,
        pyast::ExprKind::List { elts, .. }      => ...,
        pyast::ExprKind::Subscript { value, slice, .. } => ...,
        pyast::ExprKind::ListComp { elt, generators } => ...,
    }
}

// Parse in tests
let result = parser::parse(code, parser::Mode::Expression, "<test>");
match result {
    pyast::Mod::Expression { body } => *body,  // body is Box<Expr>
    _ => ...
}
```

## Full Reference

See [reference.md](reference.md) for StmtKind, Arguments, ArgData, KeywordData, ExcepthandlerKind, Withitem, MatchCase, PatternKind, and parser convenience functions.

Crate source: `~/.cargo/registry/src/index.crates.io-*/rustpython-parser-0.2.0/`
