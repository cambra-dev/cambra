//! Structured inspection of producer state for the web dashboard.

use super::Guard;

/// A structured node representing a producer's current state for web inspection.
pub struct InspectNode {
    /// The type name of the producer (e.g., "LiteralProducer", "LambdaProducer")
    pub type_name: String,
    /// Human-readable label (e.g., the literal value, variable name, or op kind)
    pub label: String,
    /// Current yield guard summary
    pub yield_guard: String,
    /// Current data summary (e.g., value preview or column length)
    pub data_summary: String,
    /// Child nodes (sub-producers this producer depends on)
    pub children: Vec<InspectNode>,
}

impl InspectNode {
    /// Serialize to a JSON string without serde.
    pub fn to_json(&self) -> String {
        let children_json: Vec<String> = self.children.iter().map(|c| c.to_json()).collect();
        format!(
            r#"{{"type":"{}","label":"{}","yield_guard":"{}","data_summary":"{}","children":[{}]}}"#,
            escape_json(&self.type_name),
            escape_json(&self.label),
            escape_json(&self.yield_guard),
            escape_json(&self.data_summary),
            children_json.join(",")
        )
    }
}

/// Escape special characters for JSON string embedding.
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Produce a short human-readable summary of a Guard.
pub fn guard_summary(guard: &Guard) -> String {
    match guard {
        Guard::Universal => "Universal".to_string(),
        Guard::Empty => "Empty".to_string(),
        Guard::Equality { value, .. } => format!("== {:?}", value),
        Guard::Membership { values, .. } => {
            format!("in [{}]", values.len())
        }
        Guard::Disequality(v) => format!("!= {:?}", v),
        Guard::LessThanOrEq(v) => format!("<= {:?}", v),
        Guard::Domain(d) => format!("Domain({})", guard_summary(d)),
        Guard::And(gs) => format!(
            "And({})",
            gs.iter()
                .map(guard_summary)
                .collect::<Vec<String>>()
                .join(", ")
        ),
        Guard::Or(gs) => format!(
            "Or({})",
            gs.iter()
                .map(guard_summary)
                .collect::<Vec<String>>()
                .join(", ")
        ),
        Guard::Function { domain, codomain } => format!(
            "Function({} -> {})",
            guard_summary(domain),
            guard_summary(codomain)
        ),
        Guard::Record(_) => "Record{..}".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inspect_node_to_json() {
        let node = InspectNode {
            type_name: "LiteralProducer".to_string(),
            label: "42".to_string(),
            yield_guard: "Universal".to_string(),
            data_summary: "42".to_string(),

            children: vec![],
        };
        let json = node.to_json();
        assert!(json.contains(r#""type":"LiteralProducer""#));
        assert!(json.contains(r#""children":[]"#));
    }

    #[test]
    fn test_inspect_node_to_json_with_children() {
        let child = InspectNode {
            type_name: "Child".to_string(),
            label: "x".to_string(),
            yield_guard: "Empty".to_string(),
            data_summary: String::new(),

            children: vec![],
        };
        let parent = InspectNode {
            type_name: "Parent".to_string(),
            label: String::new(),
            yield_guard: "Universal".to_string(),
            data_summary: String::new(),

            children: vec![child],
        };
        let json = parent.to_json();
        assert!(json.contains(r#""type":"Parent""#));
        assert!(json.contains(r#""type":"Child""#));
    }

    #[test]
    fn test_escape_json() {
        assert_eq!(escape_json(r#"he said "hi""#), r#"he said \"hi\""#);
        assert_eq!(escape_json("line\nnew"), "line\\nnew");
    }

    #[test]
    fn test_guard_summary() {
        use crate::interpreter::{Guard, Value};
        use std::collections::HashMap;

        assert_eq!(guard_summary(&Guard::Universal), "Universal");
        assert_eq!(guard_summary(&Guard::Empty), "Empty");

        assert_eq!(
            guard_summary(&Guard::Equality {
                variable: "x".to_string(),
                value: Value::Int(42),
            }),
            "== 42"
        );

        assert_eq!(
            guard_summary(&Guard::Membership {
                variable: "x".to_string(),
                values: vec![Value::Int(1), Value::Int(2), Value::Int(3)],
            }),
            "in [3]"
        );

        assert_eq!(guard_summary(&Guard::Disequality(Value::Int(5))), "!= 5");

        assert_eq!(guard_summary(&Guard::LessThanOrEq(Value::Int(10))), "<= 10");

        assert_eq!(
            guard_summary(&Guard::Domain(Box::new(Guard::Universal))),
            "Domain(Universal)"
        );
        assert_eq!(
            guard_summary(&Guard::Domain(Box::new(Guard::Empty))),
            "Domain(Empty)"
        );

        assert_eq!(
            guard_summary(&Guard::And(vec![Guard::Universal, Guard::Empty])),
            "And(Universal, Empty)"
        );

        assert_eq!(
            guard_summary(&Guard::Or(vec![Guard::Empty, Guard::Universal])),
            "Or(Empty, Universal)"
        );

        assert_eq!(
            guard_summary(&Guard::Function {
                domain: Box::new(Guard::Universal),
                codomain: Box::new(Guard::Empty),
            }),
            "Function(Universal -> Empty)"
        );

        assert_eq!(guard_summary(&Guard::Record(HashMap::new())), "Record{..}");
    }
}
