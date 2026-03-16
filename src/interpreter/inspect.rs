//! Compact formatting helpers for interpreter types used in visualization.
//!
//! Provides [`fmt_guard`] and [`fmt_value_compact`] for rendering [`Guard`]
//! and [`Value`] concisely in node labels and annotations.

use super::{Guard, Value};

/// Format a Guard compactly for display (e.g. `*`, `∅`, `x=42`).
pub fn fmt_guard(guard: &Guard) -> String {
    match guard {
        Guard::Universal => "*".to_string(),
        Guard::Empty => "∅".to_string(),
        Guard::Equality { variable, value } => {
            format!("{}={}", variable, fmt_value_compact(value))
        }
        Guard::Membership { variable, values } => {
            let vals: Vec<String> = values.iter().map(fmt_value_compact).collect();
            format!("{}∈{{{}}}", variable, vals.join(", "))
        }
        Guard::Disequality(value) => {
            format!("≠{}", fmt_value_compact(value))
        }
        Guard::LessThanOrEq(value) => {
            format!("<={}", fmt_value_compact(value))
        }
        Guard::And(guards) => {
            let parts: Vec<String> = guards.iter().map(fmt_guard).collect();
            format!("({})", parts.join(" ∧ "))
        }
        Guard::Or(guards) => {
            let parts: Vec<String> = guards.iter().map(fmt_guard).collect();
            format!("({})", parts.join(" ∨ "))
        }
        Guard::Function { domain, codomain } => {
            format!("{} → {}", fmt_guard(domain), fmt_guard(codomain))
        }
        Guard::Domain(inner) => {
            format!("dom({})", fmt_guard(inner))
        }
        Guard::Record(fields) => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(name, guard)| format!("{}: {}", name, fmt_guard(guard)))
                .collect();
            parts.sort();
            format!("{{{}}}", parts.join(", "))
        }
    }
}

/// Format a Value compactly (for use in labels and guard annotations).
pub fn fmt_value_compact(value: &Value) -> String {
    match value {
        Value::Int(n) => n.to_string(),
        Value::UInt(n) => n.to_string(),
        Value::String(s) => format!("\"{}\"", s),
        Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Value::Unit => "()".to_string(),
        Value::Function(bindings) => format!("<fn({} bindings)>", bindings.len()),
        Value::Record(fields) => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(name, val)| format!("{}: {}", name, fmt_value_compact(val)))
                .collect();
            parts.sort();
            format!("{{{}}}", parts.join(", "))
        }
        Value::ComputableFunction(fun) => format!("{fun:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fmt_guard() {
        use crate::interpreter::{Guard, Value};
        use std::collections::HashMap;

        assert_eq!(fmt_guard(&Guard::Universal), "*");
        assert_eq!(fmt_guard(&Guard::Empty), "∅");

        assert_eq!(
            fmt_guard(&Guard::Equality {
                variable: "x".to_string(),
                value: Value::Int(42),
            }),
            "x=42"
        );

        assert_eq!(
            fmt_guard(&Guard::Membership {
                variable: "x".to_string(),
                values: vec![Value::Int(1), Value::Int(2), Value::Int(3)],
            }),
            "x∈{1, 2, 3}"
        );

        assert_eq!(fmt_guard(&Guard::Disequality(Value::Int(5))), "≠5");
        assert_eq!(fmt_guard(&Guard::LessThanOrEq(Value::Int(10))), "<=10");

        assert_eq!(
            fmt_guard(&Guard::Domain(Box::new(Guard::Universal))),
            "dom(*)"
        );
        assert_eq!(fmt_guard(&Guard::Domain(Box::new(Guard::Empty))), "dom(∅)");

        assert_eq!(
            fmt_guard(&Guard::And(vec![Guard::Universal, Guard::Empty])),
            "(* ∧ ∅)"
        );

        assert_eq!(
            fmt_guard(&Guard::Or(vec![Guard::Empty, Guard::Universal])),
            "(∅ ∨ *)"
        );

        assert_eq!(
            fmt_guard(&Guard::Function {
                domain: Box::new(Guard::Universal),
                codomain: Box::new(Guard::Empty),
            }),
            "* → ∅"
        );

        assert_eq!(fmt_guard(&Guard::Record(HashMap::new())), "{}");
    }
}
