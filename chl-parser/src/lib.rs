//! Cambra High-Level Language (CHL) parser.
//!
//! CHL has Python-like indentation-significant syntax but diverges from Python
//! where convenient for Cambra's data-flow domain (e.g. `<<` / `<<=` feed
//! operators, `++` for collection union).
//!
//! Pipeline:
//!
//! ```text
//!  source ──logos──▶ raw tokens ──layout──▶ NEWLINE/INDENT/DEDENT-aware token stream
//!         ──chumsky──▶ CHL AST (this crate's [`ast`])
//! ```
//!
//! The lexer ([`lexer`]) tokenises with logos and then runs a post-pass that
//! tracks indentation depth and bracket depth, emitting `NEWLINE`, `INDENT`,
//! and `DEDENT` tokens where Python would. The parser ([`parser`]) consumes
//! those tokens with chumsky combinators and produces the AST defined in
//! [`ast`].
//!
//! See `chl-parser/design-chl-parser.md` for the design rationale and for picking
//! chumsky 1.0-alpha + logos over alternatives.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use ast::{Expr, Module, Stmt};
pub use parser::{ParseError, parse_expression, parse_module};
