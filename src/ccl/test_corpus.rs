//! The pipeline corpus: the programs every whole-compile measurement runs over.
//!
//! Shared so that a claim measured over "the corpus" in one module means the same
//! set of programs as the same claim in another. `panes.rs` folds pane pairs over
//! it and `provenance.rs` counts predicate-sweep skips over it; a program added
//! here moves both.

/// The pane-measurement corpus: every demo-gallery program that compiles
/// today, plus four inline programs covering the phases the gallery does not
/// reach (a `with begin():` transaction, a group-by, a UDF chain, and a
/// nested comprehension).
///
/// The gallery's remaining programs are excluded for reasons unrelated to
/// provenance: most are deliberate *failure* fixtures (`while`, record-term
/// syntax, `Feed(_)` types) that pin errors and so have no panes to fold,
/// and the three HTTP demos bind a real listening socket during lowering,
/// which collides with itself under a parallel test runner.
pub(crate) fn pipeline_corpus() -> Vec<(&'static str, String)> {
    vec![
        (
            "arithmetic",
            include_str!("../../tests/programs/arithmetic/program.cambra").to_string(),
        ),
        (
            "filter_and_aggregate",
            include_str!("../../tests/programs/filter_and_aggregate/program.cambra").to_string(),
        ),
        (
            "for_accumulator",
            include_str!("../../tests/programs/for_accumulator/program.cambra").to_string(),
        ),
        (
            "generator_pipeline",
            include_str!("../../tests/programs/generator_pipeline/program.cambra").to_string(),
        ),
        (
            "inner_join",
            include_str!("../../tests/programs/inner_join/program.cambra").to_string(),
        ),
        (
            "join_then_groupby",
            include_str!("../../tests/programs/join_then_groupby/program.cambra").to_string(),
        ),
        (
            "prefix_lines",
            include_str!("../../tests/programs/prefix_lines/program.cambra").to_string(),
        ),
        (
            "streaming_echo",
            include_str!("../../tests/programs/streaming_echo/program.cambra").to_string(),
        ),
        (
            "transaction",
            "out = defer()\n\
             pool: Mut(Int, Txn) := 100\n\
             for r in [10, 20, 30]:\n\
             \x20   with begin():\n\
             \x20       pool := pool - r\n\
             with begin():\n\
             \x20   out << pool\n\
             out\n"
                .to_string(),
        ),
        (
            "group_by",
            "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], \\x -> x // 2)]\n"
                .to_string(),
        ),
        (
            "udf_chain",
            "def double(x):\n    x * 2\ndef bump(x):\n    double(x) + 1\n\
             xs = [1, 2, 3]\n[bump(x) for x in xs]\n"
                .to_string(),
        ),
        (
            "feed_loop",
            "out = defer()\nfor x in [1, 2, 3]:\n    out << x * 2\nout\n".to_string(),
        ),
    ]
}
