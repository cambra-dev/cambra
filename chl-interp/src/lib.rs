//! A reference interpreter for CHL.
//!
//! It states what a program means directly, so that what the compiler produces can be
//! checked against something other than a hand-written expected value. It depends on the
//! parser and on nothing else: sharing the compiler's code would make the two agree for
//! reasons other than both being right.
//!
//! It does no type checking. A program reaching it has already compiled, and the
//! distinctions the type system draws are ones the surface syntax already states — a
//! comprehension's filter is an `if` in the source, whatever refinement it becomes.

pub mod eval;
pub mod value;

pub use eval::{Error, Observations, run};
pub use value::{Collection, Value};
