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
use crate::chl_parser;
use crate::interpreter::{Extent, HostSink, HostSource, operator_conversion::ground_extent_of};

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

    /// Every sink, in declaration order of name.
    pub fn sinks(&self) -> impl Iterator<Item = (&str, &Rc<HostSink>)> {
        self.sinks.iter().map(|(n, s)| (n.as_str(), s))
    }

    /// Every source.
    pub fn sources(&self) -> impl Iterator<Item = (&str, &Rc<RefCell<HostSource>>)> {
        self.sources.iter().map(|(n, s)| (n.as_str(), s))
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
