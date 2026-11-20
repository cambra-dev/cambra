//! The encoding of a breaker's checkpoint: [`encode`] writes what
//! [`BreakingProducer::checkpoint`](super::BreakingProducer::checkpoint) copies out as bytes, and
//! [`decode`] reads it back for
//! [`BreakingProducer::restore`](super::BreakingProducer::restore). The durable run writes them
//! to its store (`crate::interpreter::durability`).

use serde::{Serialize, de::DeserializeOwned};

/// The version of the encoding [`encode`] writes, its first byte. A change to a checkpointed
/// type's serialized shape changes it, and [`decode`] refuses any other. Its high bit marks a
/// build with debug assertions, whose checkpoints hold fields a release build's do not.
const FORMAT: u8 = 1 | if cfg!(debug_assertions) { 0x80 } else { 0 };

/// Encode `state`, which the breaker `breaker` copies out, as its checkpoint's bytes: the
/// [`FORMAT`] byte, then `state` in postcard.
///
/// # Panics
///
/// Where `state` holds a value with no encoding, such as a compiled scalar function.
pub(crate) fn encode<T: Serialize + ?Sized>(breaker: &str, state: &T) -> Vec<u8> {
    postcard::to_extend(state, vec![FORMAT])
        .unwrap_or_else(|error| panic!("{breaker} encodes its state: {error}"))
}

/// Decode the state [`encode`] wrote for `breaker`.
///
/// # Panics
///
/// Where `bytes` begins with another [`FORMAT`], or does not hold a `T`.
pub(crate) fn decode<T: DeserializeOwned>(breaker: &str, bytes: &[u8]) -> T {
    let Some((&format, state)) = bytes.split_first() else {
        panic!("{breaker} restores from an empty checkpoint");
    };
    assert_eq!(
        format, FORMAT,
        "{breaker} restores a checkpoint of format {format}, not {FORMAT}"
    );
    postcard::from_bytes(state)
        .unwrap_or_else(|error| panic!("{breaker} restores the state it encoded: {error}"))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::fmt::Debug;

    use bit_set::BitSet;
    use intervalsets::{Interval, IntervalSet};
    use serde::{Serialize, de::DeserializeOwned};

    use super::{decode, encode};
    use crate::ccl::{FieldKey, Label, TagMap};
    use crate::interpreter::tile_operators::test_helpers::two_levels_of_ints;
    use crate::interpreter::{ColumnValue, FunctionDef, Predicate, Tile, Value};

    const PINNED: [u8; 22] = [
        8, 1, 4, 115, 111, 109, 101, 0, 0, 5, 2, 0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4,
    ];

    fn decodes_to_itself<T: Serialize + DeserializeOwned + PartialEq + Debug>(state: T) {
        assert_eq!(decode::<T>("a test", &encode("a test", &state)), state);
    }

    fn tag(name: &str) -> FieldKey {
        FieldKey::Name(Label::new(name))
    }

    #[test]
    fn a_predicate_decodes_to_the_one_encoded() {
        let intervals = Predicate::Intervals(IntervalSet::new(vec![
            Interval::unbound_open(Value::Int(-4)),
            Interval::open_closed(Value::Int(3), Value::Int(9)),
            Interval::closed_unbound(Value::Int(20)),
        ]));
        decodes_to_itself(intervals.clone());
        decodes_to_itself(Predicate::Intervals(IntervalSet::new(vec![
            Interval::unbounded(),
        ])));
        decodes_to_itself(Predicate::qualified(
            Predicate::point(Value::UInt(1)),
            intervals.clone(),
        ));
        decodes_to_itself(Predicate::tagged(
            TagMap::from_arms(vec![
                (tag("commit"), intervals),
                (tag("retry"), Predicate::True),
            ]),
            false,
        ));
        decodes_to_itself(Predicate::Record(HashMap::from([
            ("a".into(), Predicate::point(Value::String("x".into()))),
            ("b".into(), Predicate::False),
        ])));
    }

    #[test]
    fn a_tile_decodes_to_the_one_encoded() {
        decodes_to_itself(two_levels_of_ints().0);
        let union = Value::Union {
            tag: tag("some"),
            inner: Box::new(Value::Record(HashMap::from([
                ("at".into(), Value::UInt(7)),
                ("ok".into(), Value::Bool(true)),
            ]))),
        };
        decodes_to_itself(Tile::data_function(
            ColumnValue::Variants(vec![union, Value::Unit]),
            Box::new(Tile::Scalar(ColumnValue::Strings(vec![
                "a".into(),
                "b".into(),
            ]))),
            Predicate::False,
            BitSet::from_bytes(&[0b0100_0000]),
        ));
    }

    #[test]
    // postcard reports a custom error without its message.
    #[should_panic(expected = "a test encodes its state")]
    fn a_compiled_function_has_no_encoding() {
        encode("a test", &Value::ComputableFunction(FunctionDef::Insert));
    }

    /// The bytes of one value of each shape a checkpoint holds most. A change to the order of a
    /// variant or a field moves them, and then [`super::FORMAT`] changes too.
    #[test]
    fn the_encoding_is_pinned() {
        let value = Value::Union {
            tag: tag("some"),
            inner: Box::new(Value::Int(-3)),
        };
        let guard = crate::interpreter::TileGuard::Function(
            crate::interpreter::FunctionGuard::Domain(Predicate::Intervals(IntervalSet::new(
                vec![Interval::closed(Value::UInt(1), Value::UInt(4))],
            ))),
        );
        assert_eq!(
            encode("a test", &(value, guard))[1..],
            PINNED,
            "the encoding after the format byte"
        );
    }

    #[test]
    #[should_panic(expected = "restores a checkpoint of format 0, not")]
    fn a_checkpoint_of_another_format_is_refused() {
        let mut bytes = encode("a test", &Value::UInt(1));
        bytes[0] = 0;
        decode::<Value>("a test", &bytes);
    }
}
