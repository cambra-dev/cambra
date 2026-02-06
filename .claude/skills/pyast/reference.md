# rustpython_parser v0.2.0 — Full Reference

Extended reference for less commonly needed types. See [SKILL.md](SKILL.md) for the quick-reference (ExprKind, Operator, Constant, Comprehension).

## Crate Source

```
~/.cargo/registry/src/index.crates.io-*/rustpython-parser-0.2.0/
~/.cargo/registry/src/index.crates.io-*/rustpython-ast-0.2.0/      # AST types live here
```

Key source files:
- `rustpython-ast-0.2.0/src/ast_gen.rs` — ExprKind, StmtKind, and all AST node types
- `rustpython-ast-0.2.0/src/constant.rs` — Constant enum
- `rustpython-ast-0.2.0/src/lib.rs` — Located, type aliases, re-exports
- `rustpython-parser-0.2.0/src/parser.rs` — parse functions
- `rustpython-parser-0.2.0/src/mode.rs` — Mode enum

## StmtKind — All Variants

```rust
pub enum StmtKind<U = ()> {
    FunctionDef {
        name: Ident,
        args: Box<Arguments<U>>,
        body: Vec<Stmt<U>>,
        decorator_list: Vec<Expr<U>>,
        returns: Option<Box<Expr<U>>>,
        type_comment: Option<String>,
    },
    AsyncFunctionDef {
        name: Ident,
        args: Box<Arguments<U>>,
        body: Vec<Stmt<U>>,
        decorator_list: Vec<Expr<U>>,
        returns: Option<Box<Expr<U>>>,
        type_comment: Option<String>,
    },
    ClassDef {
        name: Ident,
        bases: Vec<Expr<U>>,
        keywords: Vec<Keyword<U>>,
        body: Vec<Stmt<U>>,
        decorator_list: Vec<Expr<U>>,
    },
    Return {
        value: Option<Box<Expr<U>>>,
    },
    Delete {
        targets: Vec<Expr<U>>,
    },
    Assign {
        targets: Vec<Expr<U>>,
        value: Box<Expr<U>>,
        type_comment: Option<String>,
    },
    AugAssign {
        target: Box<Expr<U>>,
        op: Operator,
        value: Box<Expr<U>>,
    },
    AnnAssign {
        target: Box<Expr<U>>,
        annotation: Box<Expr<U>>,
        value: Option<Box<Expr<U>>>,
        simple: usize,
    },
    For {
        target: Box<Expr<U>>,
        iter: Box<Expr<U>>,
        body: Vec<Stmt<U>>,
        orelse: Vec<Stmt<U>>,
        type_comment: Option<String>,
    },
    AsyncFor {
        target: Box<Expr<U>>,
        iter: Box<Expr<U>>,
        body: Vec<Stmt<U>>,
        orelse: Vec<Stmt<U>>,
        type_comment: Option<String>,
    },
    While {
        test: Box<Expr<U>>,
        body: Vec<Stmt<U>>,
        orelse: Vec<Stmt<U>>,
    },
    If {
        test: Box<Expr<U>>,
        body: Vec<Stmt<U>>,
        orelse: Vec<Stmt<U>>,
    },
    With {
        items: Vec<Withitem<U>>,
        body: Vec<Stmt<U>>,
        type_comment: Option<String>,
    },
    AsyncWith {
        items: Vec<Withitem<U>>,
        body: Vec<Stmt<U>>,
        type_comment: Option<String>,
    },
    Match {
        subject: Box<Expr<U>>,
        cases: Vec<MatchCase<U>>,
    },
    Raise {
        exc: Option<Box<Expr<U>>>,
        cause: Option<Box<Expr<U>>>,
    },
    Try {
        body: Vec<Stmt<U>>,
        handlers: Vec<Excepthandler<U>>,
        orelse: Vec<Stmt<U>>,
        finalbody: Vec<Stmt<U>>,
    },
    Assert {
        test: Box<Expr<U>>,
        msg: Option<Box<Expr<U>>>,
    },
    Import {
        names: Vec<Alias<U>>,
    },
    ImportFrom {
        module: Option<Ident>,
        names: Vec<Alias<U>>,
        level: Option<usize>,
    },
    Global {
        names: Vec<Ident>,
    },
    Nonlocal {
        names: Vec<Ident>,
    },
    Expr {
        value: Box<Expr<U>>,
    },
    Pass,
    Break,
    Continue,
}
```

## Arguments

```rust
pub struct Arguments<U = ()> {
    pub posonlyargs: Vec<Arg<U>>,
    pub args: Vec<Arg<U>>,
    pub vararg: Option<Box<Arg<U>>>,      // *args
    pub kwonlyargs: Vec<Arg<U>>,
    pub kw_defaults: Vec<Expr<U>>,
    pub kwarg: Option<Box<Arg<U>>>,       // **kwargs
    pub defaults: Vec<Expr<U>>,
}
```

## ArgData

```rust
pub struct ArgData<U = ()> {
    pub arg: Ident,
    pub annotation: Option<Box<Expr<U>>>,
    pub type_comment: Option<String>,
}
```

`Arg<U>` is `Located<ArgData<U>, U>` — access fields via `.node.arg`, `.node.annotation`.

## KeywordData

```rust
pub struct KeywordData<U = ()> {
    pub arg: Option<Ident>,   // None for **kwargs expansion
    pub value: Expr<U>,
}
```

`Keyword<U>` is `Located<KeywordData<U>, U>`.

## AliasData

```rust
pub struct AliasData {
    pub name: Ident,
    pub asname: Option<Ident>,
}
```

`Alias<U>` is `Located<AliasData, U>`.

## ExcepthandlerKind

```rust
pub enum ExcepthandlerKind<U = ()> {
    ExceptHandler {
        type_: Option<Box<Expr<U>>>,
        name: Option<Ident>,
        body: Vec<Stmt<U>>,
    },
}
```

`Excepthandler<U>` is `Located<ExcepthandlerKind<U>, U>`.

## Withitem

```rust
pub struct Withitem<U = ()> {
    pub context_expr: Expr<U>,
    pub optional_vars: Option<Box<Expr<U>>>,
}
```

## MatchCase

```rust
pub struct MatchCase<U = ()> {
    pub pattern: Pattern<U>,
    pub guard: Option<Box<Expr<U>>>,
    pub body: Vec<Stmt<U>>,
}
```

## PatternKind

```rust
pub enum PatternKind<U = ()> {
    MatchValue { value: Box<Expr<U>> },
    MatchSingleton { value: Constant },
    MatchSequence { patterns: Vec<Pattern<U>> },
    MatchMapping {
        keys: Vec<Expr<U>>,
        patterns: Vec<Pattern<U>>,
        rest: Option<Ident>,
    },
    MatchClass {
        cls: Box<Expr<U>>,
        patterns: Vec<Pattern<U>>,
        kwd_attrs: Vec<Ident>,
        kwd_patterns: Vec<Pattern<U>>,
    },
    MatchStar { name: Option<Ident> },
    MatchAs {
        pattern: Option<Box<Pattern<U>>>,
        name: Option<Ident>,
    },
    MatchOr { patterns: Vec<Pattern<U>> },
}
```

`Pattern<U>` is `Located<PatternKind<U>, U>`.

## TypeIgnore

```rust
pub enum TypeIgnore {
    TypeIgnore { lineno: usize, tag: String },
}
```

## Mod Enum (full)

```rust
pub enum Mod<U = ()> {
    Module {
        body: Vec<Stmt<U>>,
        type_ignores: Vec<TypeIgnore>,
    },
    Interactive {
        body: Vec<Stmt<U>>,
    },
    Expression {
        body: Box<Expr<U>>,
    },
    FunctionType {
        argtypes: Vec<Expr<U>>,
        returns: Box<Expr<U>>,
    },
}
```

## Type Aliases (complete list)

```rust
type Ident = String;
pub type Suite<U = ()> = Vec<Stmt<U>>;
pub type Expr<U = ()> = Located<ExprKind<U>, U>;
pub type Stmt<U = ()> = Located<StmtKind<U>, U>;
pub type Arg<U = ()> = Located<ArgData<U>, U>;
pub type Keyword<U = ()> = Located<KeywordData<U>, U>;
pub type Alias<U = ()> = Located<AliasData, U>;
pub type Excepthandler<U = ()> = Located<ExcepthandlerKind<U>, U>;
pub type Pattern<U = ()> = Located<PatternKind<U>, U>;
```

## Parser Convenience Functions

```rust
// Full parser — returns Mod enum, caller picks variant
pub fn parse(source: &str, mode: Mode, source_path: &str) -> Result<ast::Mod, ParseError>

// Parse with custom start location
pub fn parse_located(source: &str, mode: Mode, source_path: &str, location: Location) -> Result<ast::Mod, ParseError>

// Shorthand: parse as Module, return body directly
pub fn parse_program(source: &str, source_path: &str) -> Result<ast::Suite, ParseError>

// Shorthand: parse as Expression, return Expr directly
pub fn parse_expression(source: &str, path: &str) -> Result<ast::Expr, ParseError>

// Parse with custom start location
pub fn parse_expression_located(source: &str, path: &str, location: Location) -> Result<ast::Expr, ParseError>

// Parse from token stream
pub fn parse_tokens(lxr: impl IntoIterator<Item = LexResult>, mode: Mode, source_path: &str) -> Result<ast::Mod, ParseError>
```

## Location

```rust
// From rustpython_compiler_core
pub struct Location { row: u32, column: u32 }

impl Location {
    pub fn new(row: usize, column: usize) -> Self
    pub fn row(&self) -> usize
    pub fn column(&self) -> usize
}
// Default: row=1, column=0
```

## ConversionFlag

Used for `FormattedValue::conversion` (f-string conversions):

```rust
pub enum ConversionFlag {
    None = 0,
    Str = b's',     // !s
    Ascii = b'a',   // !a
    Repr = b'r',    // !r
}
```
