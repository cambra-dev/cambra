//! `std::time` as a program imports it: durations, instants, their operators, and the clock
//! reading (`docs/chl-spec.md`, "7.5 Time [Decided]").

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::check_scalar;

/// The operators `std::time` declares on `Instant` and `Duration` compute on the nanosecond
/// counts, and the conversions read the counts back.
#[rstest]
#[case::durations_add("time::as_seconds(time::minutes(2) + time::seconds(30))", 150)]
#[case::durations_subtract(
    "time::as_milliseconds(time::seconds(2) - time::milliseconds(1))",
    1999
)]
#[case::a_duration_scales("time::as_seconds(time::hours(1) * 2)", 7200)]
#[case::durations_divide("time::days(1) // time::hours(1)", 24)]
#[case::an_instant_advances(
    "time::unix_seconds(time::from_unix_seconds(10) + time::seconds(5))",
    15
)]
#[case::an_instant_recedes(
    "time::unix_seconds(time::from_unix_seconds(10) - time::seconds(15))",
    -5
)]
#[case::two_instants_differ(
    "time::as_seconds(time::from_unix_seconds(20) - time::from_unix_seconds(5))",
    15
)]
#[case::rounding_is_toward_negative_infinity("time::as_seconds(time::milliseconds(-1))", -1)]
#[timeout(Duration::from_secs(10))]
fn time_arithmetic_computes_on_nanosecond_counts(#[case] expr: &str, #[case] expected: i64) {
    check_scalar(&format!("import std::time\n{expr}"), Value::Int(expected));
}

/// `Instant` and `Duration` compare and order by their counts.
#[rstest]
#[case::instants_order("time::from_unix_seconds(1) < time::from_unix_seconds(2)")]
#[case::durations_order("time::minutes(1) >= time::seconds(60)")]
#[case::equal_durations("time::seconds(1) == time::milliseconds(1000)")]
#[case::unequal_instants("time::from_unix_seconds(1) != time::from_unix_nanoseconds(1)")]
#[case::a_reading_is_an_instant(indoc! {"
    t = time::now()
    t == t and t + time::seconds(1) > t
"})]
#[case::a_reading_is_after_2020("time::now() > time::from_unix_seconds(1_577_836_800)")]
#[timeout(Duration::from_secs(10))]
fn time_values_compare_by_count(#[case] expr: &str) {
    check_scalar(&format!("import std::time\n{expr}"), Value::Bool(true));
}
