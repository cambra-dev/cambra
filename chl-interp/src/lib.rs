//! A differential interpreter for CHL.
//!
//! It states what a program means directly, so that what the compiler produces can be
//! checked against something other than a hand-written expected value. It depends on the
//! parser and on nothing else: sharing the compiler's code would make the two agree for
//! reasons other than both being right.
//!
//! Where `docs/chl-spec.md` leaves a value undefined or arbitrary, [`run`] answers an [`Error`]
//! rather than choosing one, so a compiler that chooses differently is not reported as wrong.
//! Each refusal cites the section it rests on.
//!
//! It does no type checking, and its answer is defined only for a program the type system
//! accepts: on an ill-formed one it may answer where the spec refuses, such as a `:=` to an
//! immutable name, which declares a new mutable variable here. The distinctions the type
//! system draws that the answer depends on are ones the surface syntax already states: a
//! comprehension's filter is an `if` in the source, whatever refinement it becomes. The one
//! it cannot read off the syntax is which `except` catches an exception, which the raised
//! expression's type decides: the interpreter decides it from the value for a primitive or a
//! nominal type, where the two agree, and refuses any other.

pub mod eval;
pub mod value;

pub use eval::{Error, Observations, run};
pub use value::{Collection, Value};
