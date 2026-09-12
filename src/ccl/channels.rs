//! Host channels: the typed named ports an embedding host wires a program to.
//!
//! A channel is a name, a direction and a row type written in CHL. The host
//! declares its channels before compiling; a **source** becomes a call the
//! program makes (`price_updates()`), a **sink** becomes a feed the program
//! writes (`cart_view << …`). Rows cross in both directions as values, so
//! nothing is rendered to a string on the way through.
//!
//! Design: `src/interpreter/design-host-channels.md`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

use crate::ccl::Type;
use crate::ccl::context::GlobalContext;
use crate::ccl::lower::{LoweringContext, lower_type_expr};
use crate::ccl::provenance::NodeId;
use crate::chl_parser;
use crate::interpreter::{
    BaseType, Extent, HostSink, HostSource, Value,
    operator_conversion::ground_extent_of,
    operator_graph::{OperatorGraph, sink_nodes, source_nodes},
    value_recorder::SharedRecorder,
};

/// Which way rows cross a channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ChannelKind {
    /// The host pushes rows in; the program calls the name.
    Source,
    /// The program feeds rows out; the host drains the name.
    Sink,
}

/// One channel a host declares.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChannelDecl {
    /// The name the program uses.
    pub name: String,
    /// Which way rows cross.
    pub kind: ChannelKind,
    /// The type of one row, as a CHL type expression (`{ticker: String, price: Int}`).
    #[serde(rename = "type")]
    pub row_type: String,
}

/// A channel declaration file: what a program needs wired to it, beside the
/// program.
///
/// A program calling `price_updates()` does not say what that is, because a
/// source is registered by the host rather than written in the program. The
/// file is how a driver — the `cambra` binary, or the golden sweep — knows what
/// to register before compiling, so a program that reads host channels can be
/// compiled from a path like any other.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChannelFile {
    /// The channels to register.
    pub channels: Vec<ChannelDecl>,
}

impl ChannelFile {
    /// Read declarations from JSON.
    pub fn from_json(text: &str) -> Result<Self, String> {
        serde_json::from_str(text).map_err(|e| e.to_string())
    }

    /// The declarations a program at `program` expects, from `channels.json`
    /// beside it, or `None` where the program declares no channels.
    pub fn beside(program: &Path) -> Result<Option<Self>, String> {
        let path = match program.parent() {
            Some(dir) => dir.join("channels.json"),
            None => return Ok(None),
        };
        if !path.exists() {
            return Ok(None);
        }
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::from_json(&text)
            .map(Some)
            .map_err(|e| format!("{}: {e}", path.display()))
    }
}

impl ChannelDecl {
    /// A source named `name` carrying rows of `row_type`.
    pub fn source(name: impl Into<String>, row_type: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: ChannelKind::Source,
            row_type: row_type.into(),
        }
    }

    /// A sink named `name` carrying rows of `row_type`.
    pub fn sink(name: impl Into<String>, row_type: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: ChannelKind::Sink,
            row_type: row_type.into(),
        }
    }
}

/// Why a set of channel declarations was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChannelError {
    /// A row type did not parse as CHL.
    TypeSyntax { channel: String, message: String },
    /// A row type parsed but is not a type CHL can express.
    TypeUnsupported { channel: String, message: String },
    /// A row type has no runtime representation.
    NoExtent { channel: String, message: String },
    /// Two channels claim the same name.
    DuplicateName(String),
}

impl std::fmt::Display for ChannelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChannelError::TypeSyntax { channel, message } => {
                write!(f, "channel '{channel}': row type does not parse: {message}")
            }
            ChannelError::TypeUnsupported { channel, message } => {
                write!(f, "channel '{channel}': unsupported row type: {message}")
            }
            ChannelError::NoExtent { channel, message } => {
                write!(f, "channel '{channel}': row type has no extent: {message}")
            }
            ChannelError::DuplicateName(name) => {
                write!(f, "channel '{name}' is declared twice")
            }
        }
    }
}

impl std::error::Error for ChannelError {}

/// Parse a CHL type expression into a CCL [`Type`].
///
/// The type half of [`chl_parser::parse_module`]: a type is an ordinary CHL
/// expression until lowering reads it as a type, so this pairs the expression
/// parser with that reading. A host declaring a channel writes the row type the
/// way the program would write it in an annotation, rather than assembling a
/// `Type` by hand.
///
/// The lowering context is scratch. Every recognised type form is structural;
/// the context carries the machinery for holes and variants and is not consulted
/// for anything a declaration can name.
pub fn parse_type(source: &str) -> Result<Type, String> {
    let parsed = chl_parser::parse_expression(source);
    if !parsed.errors.is_empty() {
        return Err(parsed
            .errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; "));
    }
    let parsed = parsed
        .value
        .ok_or_else(|| "the type expression is empty".to_string())?;
    let mut ctx = LoweringContext::default();
    lower_type_expr(&parsed, &mut ctx).map_err(|e| e.to_string())
}

/// The largest integer a JSON number carries exactly.
///
/// A row crosses as JSON, and a JavaScript host's numbers are `f64`. An `Int`
/// outside this range would arrive at the program as a different number than
/// the host sent, so it is rejected at the boundary rather than silently
/// rounded. Scaled prices — dollars × 10⁸ — stay inside it for any plausible
/// price.
const JSON_SAFE_INT: i64 = 9_007_199_254_740_991;

/// Decode one JSON row against the channel's declared row type.
///
/// A missing field, an extra field, or a field of the wrong type is an error.
/// Filling a missing field with a default would put a value in the program that
/// the host never sent, and ignoring an extra one would hide a host that
/// believes it is sending something the program cannot see.
pub fn row_from_json(json: &serde_json::Value, ty: &Type) -> Result<Value, String> {
    match ty {
        Type::Base(BaseType::Int) => integer(json).map(Value::Int),
        Type::Base(BaseType::UInt) => {
            let n = integer(json)?;
            usize::try_from(n)
                .map(Value::UInt)
                .map_err(|_| format!("expected a non-negative integer, got {n}"))
        }
        Type::Base(BaseType::String) => json
            .as_str()
            .map(|s| Value::String(s.into()))
            .ok_or_else(|| format!("expected a string, got {json}")),
        Type::Base(BaseType::Bool) => json
            .as_bool()
            .map(Value::Bool)
            .ok_or_else(|| format!("expected a boolean, got {json}")),
        Type::Base(BaseType::Unit) => Ok(Value::Unit),
        Type::Record(fields) => {
            let object = json
                .as_object()
                .ok_or_else(|| format!("expected an object, got {json}"))?;
            let mut row = HashMap::with_capacity(fields.len());
            for (name, field_type) in fields {
                let field = object
                    .get(name)
                    .ok_or_else(|| format!("missing field '{name}'"))?;
                let decoded =
                    row_from_json(field, field_type).map_err(|e| format!("field '{name}': {e}"))?;
                row.insert(name.clone(), decoded);
            }
            if let Some(extra) = object.keys().find(|k| !row.contains_key(*k)) {
                return Err(format!("unknown field '{extra}'"));
            }
            Ok(Value::Record(row))
        }
        other => Err(format!("no JSON encoding for the row type {other}")),
    }
}

/// The integer `json` carries, if it carries one exactly.
fn integer(json: &serde_json::Value) -> Result<i64, String> {
    let n = json
        .as_i64()
        .ok_or_else(|| format!("expected an integer, got {json}"))?;
    if n.abs() > JSON_SAFE_INT {
        return Err(format!(
            "{n} is outside the range a JSON number carries exactly (±{JSON_SAFE_INT})"
        ));
    }
    Ok(n)
}

/// Encode one row a sink produced as JSON.
///
/// The inverse of [`row_from_json`] over the types a channel can declare. A
/// value of any other shape is a program the sink's declared type did not
/// describe, and says so rather than encoding something the host cannot read.
pub fn row_to_json(value: &Value) -> Result<serde_json::Value, String> {
    match value {
        Value::Int(n) => Ok(serde_json::Value::from(*n)),
        Value::UInt(n) => Ok(serde_json::Value::from(*n)),
        Value::String(s) => Ok(serde_json::Value::from(s.as_str())),
        Value::Bool(b) => Ok(serde_json::Value::from(*b)),
        Value::Unit => Ok(serde_json::Value::Object(serde_json::Map::new())),
        Value::Record(fields) => {
            let mut object = serde_json::Map::with_capacity(fields.len());
            for (name, field) in fields {
                object.insert(name.clone(), row_to_json(field)?);
            }
            Ok(serde_json::Value::Object(object))
        }
        other => Err(format!("no JSON encoding for the value {other:?}")),
    }
}

/// A channel's row type, as both halves the runtime needs.
fn row_type_of(decl: &ChannelDecl) -> Result<(Type, Extent), ChannelError> {
    let ty = parse_type(&decl.row_type).map_err(|message| ChannelError::TypeSyntax {
        channel: decl.name.clone(),
        message,
    })?;
    let extent = ground_extent_of(&ty).map_err(|e| ChannelError::NoExtent {
        channel: decl.name.clone(),
        message: format!("{e:?}"),
    })?;
    Ok((ty, extent))
}

/// The channels a host registered, by name, so it can push and drain them.
#[derive(Default)]
pub struct Channels {
    sources: HashMap<String, Rc<RefCell<HostSource>>>,
    sinks: HashMap<String, Rc<HostSink>>,
    /// Where to record what leaves through a sink, and the node to record it
    /// under, installed by [`observe`](Channels::observe).
    ///
    /// Here rather than on [`HostSink`] because a sink is held as a bare `Rc`:
    /// giving it an observer would mean new interior mutability on a participant
    /// in the operator graph, where `Channels` is already the host's own handle
    /// and already the place rows are drained. A source needs none of this — it
    /// is held as `Rc<RefCell<HostSource>>`, so its observer rides the cell the
    /// host already goes through to push.
    sink_observer: RefCell<Option<(SharedRecorder, HashMap<String, NodeId>)>>,
}

impl Channels {
    /// The source named `name`, for pushing rows in.
    pub fn source(&self, name: &str) -> Option<&Rc<RefCell<HostSource>>> {
        self.sources.get(name)
    }

    /// The sink named `name`, for draining rows out.
    pub fn sink(&self, name: &str) -> Option<&Rc<HostSink>> {
        self.sinks.get(name)
    }

    /// Take what the sink named `name` has served, recording it on the way out.
    ///
    /// The recording happens here rather than where a row arrives because a
    /// drain is what takes the rows away: a host that drains every tick would
    /// otherwise leave nothing for a frame to show. Every host drains through
    /// this, so none of them has to remember to record.
    pub fn drain_sink(&self, name: &str) -> Vec<Value> {
        let Some(sink) = self.sinks.get(name) else {
            return Vec::new();
        };
        let rows = sink.drain();
        if let Some((recorder, nodes)) = self.sink_observer.borrow().as_ref() {
            recorder.borrow_mut().record_channel(
                nodes.get(name).copied(),
                name,
                "Sink",
                None,
                &rows,
            );
        }
        rows
    }

    /// Every sink, in declaration order of name.
    pub fn sinks(&self) -> impl Iterator<Item = (&str, &Rc<HostSink>)> {
        self.sinks.iter().map(|(n, s)| (n.as_str(), s))
    }

    /// Every source.
    pub fn sources(&self) -> impl Iterator<Item = (&str, &Rc<RefCell<HostSource>>)> {
        self.sources.iter().map(|(n, s)| (n.as_str(), s))
    }

    /// Record what crosses every channel into `recorder`, under the nodes
    /// `graph` minted for them.
    ///
    /// Called after each compile, including a reload's: the channels outlive a
    /// version while the nodes naming them do not, so a version's ids have to be
    /// installed against the same handles the previous version's were.
    ///
    /// A channel the compiled program does not mention gets `None` for its node,
    /// which records its rows under no node rather than under another version's.
    pub fn observe(&self, recorder: &SharedRecorder, graph: &OperatorGraph) {
        let sources = source_nodes(graph);
        for (name, source) in self.sources() {
            source
                .borrow_mut()
                .observe(recorder.clone(), sources.get(name).copied());
        }
        *self.sink_observer.borrow_mut() = Some((recorder.clone(), sink_nodes(graph)));
    }
}

impl GlobalContext {
    /// Register `decls` and return handles to what was built.
    ///
    /// Call before [`compile_program`](crate::ccl::context::compile_program): a
    /// source has to exist for `name()` to resolve during lowering, and a sink
    /// for its channel to be bound.
    pub fn register_channels(&mut self, decls: &[ChannelDecl]) -> Result<Channels, ChannelError> {
        let mut channels = Channels::default();
        let mut seen: HashMap<&str, ()> = HashMap::new();
        for decl in decls {
            if seen.insert(decl.name.as_str(), ()).is_some() {
                return Err(ChannelError::DuplicateName(decl.name.clone()));
            }
            let (ty, extent) = row_type_of(decl)?;
            match decl.kind {
                ChannelKind::Source => {
                    let source = Rc::new(RefCell::new(HostSource::new(&decl.name, ty, extent)));
                    self.register_source(source.clone());
                    channels.sources.insert(decl.name.clone(), source);
                }
                ChannelKind::Sink => {
                    let sink = Rc::new(HostSink::new(&decl.name));
                    self.declare_host_sink(sink.clone());
                    channels.sinks.insert(decl.name.clone(), sink);
                }
            }
        }
        Ok(channels)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::BaseType;
    use test_log::test;

    #[test]
    fn a_base_type_parses() {
        assert_eq!(parse_type("Int"), Ok(Type::Base(BaseType::Int)));
        assert_eq!(parse_type("String"), Ok(Type::Base(BaseType::String)));
        assert_eq!(parse_type("Bool"), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn a_record_type_parses_to_its_fields() {
        let ty = parse_type("{ticker: String, price: Int}").expect("a record type parses");
        let Type::Record(fields) = &ty else {
            panic!("expected a record type, got {ty}");
        };
        assert_eq!(
            fields,
            &vec![
                ("ticker".to_string(), Type::Base(BaseType::String)),
                ("price".to_string(), Type::Base(BaseType::Int)),
            ],
            "a record type's fields keep the order the declaration wrote them"
        );
    }

    /// The extent derivation runs with no source registry, which is the state a
    /// host declares channels in.
    #[test]
    fn a_record_row_type_derives_its_extent() {
        let ty = parse_type("{ticker: String, price: Int}").expect("a record type parses");
        let extent = ground_extent_of(&ty).expect("a record of base types has an extent");
        let Extent::Record(fields) = &extent else {
            panic!("expected a record extent, got {extent:?}");
        };
        assert_eq!(fields["ticker"], Extent::Base(BaseType::String));
        assert_eq!(fields["price"], Extent::Base(BaseType::Int));
    }

    #[test]
    fn a_row_type_that_does_not_parse_names_its_channel() {
        let err = row_type_of(&ChannelDecl::source("price_updates", "{ticker: }"))
            .expect_err("a malformed row type is rejected");
        assert!(
            format!("{err}").contains("price_updates"),
            "the rejection names the channel; got: {err}"
        );
    }

    fn price_row_type() -> Type {
        parse_type("{ticker: String, price: Int}").expect("a record type parses")
    }

    #[test]
    fn a_row_round_trips_through_json() {
        let ty = price_row_type();
        let json = serde_json::json!({"ticker": "BTC-USD", "price": 8_169_291_000_000i64});
        let row = row_from_json(&json, &ty).expect("a well-formed row decodes");
        assert_eq!(row_to_json(&row).expect("a decoded row encodes"), json);
    }

    /// A missing field is an error rather than a default, so a program never
    /// sees a value its host did not send.
    #[test]
    fn a_missing_field_is_rejected() {
        let err = row_from_json(&serde_json::json!({"ticker": "BTC-USD"}), &price_row_type())
            .expect_err("a row missing a declared field is rejected");
        assert!(
            err.contains("price"),
            "the rejection names the field: {err}"
        );
    }

    /// An extra field is an error rather than ignored, so a host that believes
    /// it is sending something finds out that nothing reads it.
    #[test]
    fn an_unknown_field_is_rejected() {
        let json = serde_json::json!({"ticker": "BTC-USD", "price": 1, "volume": 2});
        let err = row_from_json(&json, &price_row_type())
            .expect_err("a row with an undeclared field is rejected");
        assert!(
            err.contains("volume"),
            "the rejection names the field: {err}"
        );
    }

    #[test]
    fn a_field_of_the_wrong_type_is_rejected() {
        let json = serde_json::json!({"ticker": "BTC-USD", "price": "cheap"});
        let err = row_from_json(&json, &price_row_type())
            .expect_err("a string where an Int is declared is rejected");
        assert!(
            err.contains("price"),
            "the rejection names the field: {err}"
        );
    }

    /// An integer a JSON number cannot carry exactly is rejected at the
    /// boundary rather than arriving rounded.
    #[test]
    fn an_integer_beyond_json_precision_is_rejected() {
        let ty = Type::Base(BaseType::Int);
        assert_eq!(
            row_from_json(&serde_json::json!(JSON_SAFE_INT), &ty),
            Ok(Value::Int(JSON_SAFE_INT))
        );
        assert!(
            row_from_json(&serde_json::json!(JSON_SAFE_INT + 1), &ty).is_err(),
            "an integer past 2^53 - 1 does not survive a JSON round trip"
        );
    }

    #[test]
    fn two_channels_may_not_share_a_name() {
        let mut ctx = GlobalContext::default();
        let err = ctx
            .register_channels(&[
                ChannelDecl::source("prices", "Int"),
                ChannelDecl::sink("prices", "Int"),
            ])
            .err()
            .expect("a repeated name is rejected");
        assert_eq!(err, ChannelError::DuplicateName("prices".to_string()));
    }
}
