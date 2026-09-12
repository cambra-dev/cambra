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
use crate::ccl::lower::{LoweringContext, lower_type_expr, wasm_route_name};
use crate::ccl::provenance::NodeId;
use crate::chl_parser;
use crate::interpreter::{
    BaseType, Extent, FuncBinding, HostSink, HostSource, Value, bindings_are_list,
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
    /// The ingress half of a route: the host pushes one row per call, and the
    /// program reads it through the `wasm_serve` that names the route.
    Request,
    /// The egress half of a route: the program feeds one reply per call, and the
    /// host drains it to answer the call the request came from.
    Response,
}

impl ChannelKind {
    /// Whether this kind is half of a route rather than a standalone channel.
    fn is_route_half(self) -> bool {
        matches!(self, ChannelKind::Request | ChannelKind::Response)
    }

    /// Whether rows cross this channel into the program.
    fn is_ingress(self) -> bool {
        matches!(self, ChannelKind::Source | ChannelKind::Request)
    }
}

/// One channel a host declares.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChannelDecl {
    /// The name the program uses, or — for a route's `request` and `response` —
    /// the route the program's `wasm_serve` names, spelled as a request line:
    /// `PATCH /cart` ([`wasm_route_name`]).
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

    /// The declarations a program at `program` expects, from
    /// `<program>.channels.json` or `channels.json` beside it, or `None` where
    /// the program declares no channels.
    ///
    /// The program-qualified name is read first so that two versions of one
    /// program can sit in a directory with different wiring: a version that
    /// replaces three sources with three routes is a different set of
    /// declarations, and the alternative — one file that is the union of both —
    /// gives each version sinks it never feeds, which lowering rejects.
    pub fn beside(program: &Path) -> Result<Option<Self>, String> {
        let Some(dir) = program.parent() else {
            return Ok(None);
        };
        let qualified = program
            .file_stem()
            .map(|stem| dir.join(format!("{}.channels.json", stem.to_string_lossy())));
        let path = match qualified {
            Some(qualified) if qualified.exists() => qualified,
            _ => dir.join("channels.json"),
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

    /// The request half of the route `method path`, carrying rows of `row_type`.
    pub fn request(method: &str, path: &str, row_type: impl Into<String>) -> Self {
        Self {
            name: wasm_route_name(method, path),
            kind: ChannelKind::Request,
            row_type: row_type.into(),
        }
    }

    /// The reply half of the route `method path`, carrying rows of `row_type`.
    pub fn response(method: &str, path: &str, row_type: impl Into<String>) -> Self {
        Self {
            name: wasm_route_name(method, path),
            kind: ChannelKind::Response,
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
    /// A route was declared with one half only.
    HalfRoute {
        /// The route both halves name.
        route: String,
        /// The kind that is missing, as it is spelled in a declaration.
        missing: &'static str,
    },
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
            ChannelError::HalfRoute { route, missing } => {
                write!(
                    f,
                    "route '{route}' declares no {missing}: a route is a \
                     request and a response under one name"
                )
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
        // A `List(T)` crosses as a JSON array and arrives as the run of positions
        // the runtime represents a list by: a function whose domain is `0..n`
        // ([`bindings_are_list`]). Order is the array's, and it is the whole
        // content of a list — `[a, b]` and `[b, a]` are different rows, where two
        // field orders in an object are one row.
        other => {
            let Some(element) = other.list_element() else {
                return Err(format!("no JSON encoding for the row type {other}"));
            };
            let items = json
                .as_array()
                .ok_or_else(|| format!("expected an array, got {json}"))?;
            let mut bindings = Vec::with_capacity(items.len());
            for (position, item) in items.iter().enumerate() {
                let decoded =
                    row_from_json(item, element).map_err(|e| format!("item {position}: {e}"))?;
                bindings.push(FuncBinding {
                    input: Value::UInt(position),
                    output: decoded,
                });
            }
            Ok(Value::Function(bindings))
        }
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
        // The runtime holds a list as a function over `0..n`, so this is the one
        // encoding decided by the *value* rather than by the declared type: a
        // function keyed by anything else is a map, and a map has no JSON array
        // to be. Saying which it was is worth the longer message, because the two
        // are one Rust variant and a host reading "no JSON encoding for a
        // Function" learns nothing about which of its rows was wrong.
        Value::Function(bindings) if bindings_are_list(bindings) => bindings
            .iter()
            .map(|binding| row_to_json(&binding.output))
            .collect::<Result<Vec<_>, _>>()
            .map(serde_json::Value::Array),
        Value::Function(_) => Err(
            "a collection keyed by anything but its positions is a map, and no JSON \
             encoding carries one"
                .to_string(),
        ),
        other => Err(format!("no JSON encoding for the value {other:?}")),
    }
}

/// A channel's declared row type.
fn row_type_of(decl: &ChannelDecl) -> Result<Type, ChannelError> {
    parse_type(&decl.row_type).map_err(|message| ChannelError::TypeSyntax {
        channel: decl.name.clone(),
        message,
    })
}

/// The extent of an ingress channel's row, which is what tiles what arrives.
///
/// Asked for a `source` and a `request` and of nothing else. [`HostSource`]
/// builds a column of arriving rows against it, so a row with no extent is a row
/// the buffer cannot hold; [`HostSink`] takes a name and decodes the tiles the
/// program hands it, so the declared type on the way out is a contract nothing
/// grounds. Deriving one there would reject every row type the runtime can
/// produce but a declaration cannot ground — a list, whose extent names a length
/// that is data.
fn row_extent_of(decl: &ChannelDecl, ty: &Type) -> Result<Extent, ChannelError> {
    ground_extent_of(ty).map_err(|e| ChannelError::NoExtent {
        channel: decl.name.clone(),
        message: format!("{e:?}"),
    })
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

    /// Both halves of the route `method path`: the source a call's request goes
    /// into, and the sink its reply comes out of.
    ///
    /// A route's halves live in the same maps every other channel does, keyed by
    /// the route rather than by a name the program spells, so a host that drives
    /// a route by name through [`source`](Self::source) and
    /// [`drain_sink`](Self::drain_sink) drives it the same way. This is the
    /// lookup that spares a caller from spelling the route itself.
    pub fn route(
        &self,
        method: &str,
        path: &str,
    ) -> Option<(&Rc<RefCell<HostSource>>, &Rc<HostSink>)> {
        let route = wasm_route_name(method, path);
        Some((self.sources.get(&route)?, self.sinks.get(&route)?))
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
        // One claim per name per direction. A name carrying two claims is a
        // route and nothing else: the request and the response are one address,
        // bound together by one `wasm_serve`, so they are the one case where
        // "the same name" means "the same thing". A `source` and a `sink`
        // sharing a name are two channels a host believes are one.
        let mut ingress: HashMap<&str, ChannelKind> = HashMap::new();
        let mut egress: HashMap<&str, ChannelKind> = HashMap::new();
        for decl in decls {
            let name = decl.name.as_str();
            let (claimed, opposite) = if decl.kind.is_ingress() {
                (&mut ingress, &egress)
            } else {
                (&mut egress, &ingress)
            };
            let crosses_directions = opposite
                .get(name)
                .is_some_and(|k| !(k.is_route_half() && decl.kind.is_route_half()));
            if claimed.insert(name, decl.kind).is_some() || crosses_directions {
                return Err(ChannelError::DuplicateName(decl.name.clone()));
            }
            let ty = row_type_of(decl)?;
            match decl.kind {
                ChannelKind::Source | ChannelKind::Request => {
                    let extent = row_extent_of(decl, &ty)?;
                    let source = Rc::new(RefCell::new(HostSource::new(&decl.name, ty, extent)));
                    self.register_source(source.clone());
                    channels.sources.insert(decl.name.clone(), source);
                }
                ChannelKind::Sink => {
                    let sink = Rc::new(HostSink::new(&decl.name));
                    self.declare_host_sink(sink.clone());
                    channels.sinks.insert(decl.name.clone(), sink);
                }
                ChannelKind::Response => {
                    let sink = Rc::new(HostSink::new(&decl.name));
                    self.declare_route_sink(sink.clone());
                    channels.sinks.insert(decl.name.clone(), sink);
                }
            }
        }
        // A half-declared route is rejected here rather than at the `wasm_serve`
        // that binds it, because the missing half is the host's to supply and
        // the program naming the route is evidence that it meant to: a request
        // with no response is an address whose callers never hear back, and a
        // response with no request is a reply channel nothing can trigger.
        for decl in decls.iter().filter(|d| d.kind.is_route_half()) {
            let (other_half, missing) = if decl.kind.is_ingress() {
                (&egress, "response")
            } else {
                (&ingress, "request")
            };
            if !other_half.contains_key(decl.name.as_str()) {
                return Err(ChannelError::HalfRoute {
                    route: decl.name.clone(),
                    missing,
                });
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

    /// A list crosses as a JSON array, in both directions.
    ///
    /// The runtime holds one as a function over `0..n`, so the decoder mints the
    /// positions and the encoder reads them back off the bindings.
    #[test]
    fn a_list_row_round_trips_through_json() {
        let ty = parse_type("List(Int)").expect("a list type parses");
        let json = serde_json::json!([10, 20, 30]);
        let row = row_from_json(&json, &ty).expect("an array decodes");
        assert_eq!(
            row,
            Value::Function(vec![
                FuncBinding {
                    input: Value::UInt(0),
                    output: Value::Int(10)
                },
                FuncBinding {
                    input: Value::UInt(1),
                    output: Value::Int(20)
                },
                FuncBinding {
                    input: Value::UInt(2),
                    output: Value::Int(30)
                },
            ]),
            "positions are the list's own, minted in arrival order"
        );
        assert_eq!(row_to_json(&row).expect("a list encodes"), json);
    }

    /// The demo's view reply: a record carrying two lists of records.
    ///
    /// This is the row the page reads a cart off, so nothing about it may be
    /// approximated on the way across.
    #[test]
    fn a_record_of_lists_round_trips_through_json() {
        let ty = parse_type(
            "{cash: Int, lines: List({ticker: String, qty: Int}), positions: List(Int)}",
        )
        .expect("a record of lists parses");
        let json = serde_json::json!({
            "cash": 50_000_000_000i64,
            "lines": [{"ticker": "BTC", "qty": 2}, {"ticker": "ETH", "qty": 3}],
            "positions": [],
        });
        let row = row_from_json(&json, &ty).expect("the view reply decodes");
        assert_eq!(row_to_json(&row).expect("the view reply encodes"), json);
    }

    /// A collection keyed by anything but its positions is a map, and says so.
    ///
    /// Both are `Value::Function`, so the encoder decides by the keys. A host
    /// told only "no JSON encoding for a Function" learns nothing about which of
    /// its rows was wrong.
    #[test]
    fn a_map_value_is_refused_as_a_list() {
        let map = Value::Function(vec![FuncBinding {
            input: Value::String("BTC".into()),
            output: Value::Int(2),
        }]);
        let err = row_to_json(&map).expect_err("a keyed collection has no JSON array");
        assert!(
            err.contains("map"),
            "the rejection says which it was: {err}"
        );
    }

    /// An egress channel's row type needs no extent, which is what lets a reply
    /// carry a list.
    ///
    /// The extent tiles what arrives, and nothing arrives on a sink. A list's
    /// extent names a length, and a length is data — so requiring one on the way
    /// out would reject exactly the rows the runtime can produce and a
    /// declaration cannot ground.
    #[test]
    fn an_egress_row_type_carries_a_list() {
        let view_reply = "{cash: Int, lines: List({ticker: String, qty: Int})}";
        for decl in [
            ChannelDecl::sink("cart_view", view_reply),
            ChannelDecl::response("GET", "/cart", view_reply),
        ] {
            let mut ctx = GlobalContext::default();
            let paired = decl.kind == ChannelKind::Response;
            let mut decls = vec![decl];
            if paired {
                decls.insert(0, ChannelDecl::request("GET", "/cart", "{account: Int}"));
            }
            ctx.register_channels(&decls)
                .expect("a reply carrying a list is declarable");
        }
    }

    /// An ingress channel's row type needs one, and a list has none.
    ///
    /// [`HostSource`] builds a column of arriving rows against the extent, so a
    /// row type that cannot be grounded is a row the buffer cannot hold. The
    /// rejection names the channel.
    #[test]
    fn an_ingress_row_type_may_not_carry_a_list() {
        let err = GlobalContext::default()
            .register_channels(&[ChannelDecl::source("quotes", "List(Int)")])
            .err()
            .expect("a list has no ground extent");
        assert!(
            matches!(&err, ChannelError::NoExtent { channel, .. } if channel == "quotes"),
            "the rejection names the channel; got: {err}"
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
