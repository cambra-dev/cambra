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
///
/// Inside [`with_caret_operators`] each program is spelled with `^` operators
/// ([`caret_operators`]).
pub(crate) fn pipeline_corpus() -> Vec<(&'static str, String)> {
    let corpus = vec![
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
            indoc::indoc! {r#"
                out: Feed(_)
                pool: Mut(Int, Txn) := 100
                for r in [10, 20, 30]:
                    with begin():
                        pool := pool - r
                with begin():
                    out << pool
                out
                "#}
            .to_string(),
        ),
        (
            "group_by",
            "[sum(x) for _ -> x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], \\x -> x // 2)]\n"
                .to_string(),
        ),
        (
            "udf_chain",
            indoc::indoc! {r#"
                def double(x):
                    x * 2
                def bump(x):
                    double(x) + 1
                xs = [1, 2, 3]
                [bump(x) for x in xs]
                "#}
            .to_string(),
        ),
        (
            "feed_loop",
            indoc::indoc! {r#"
                out: Feed(_)
                for x in [1, 2, 3]:
                    out << x * 2
                out
                "#}
            .to_string(),
        ),
    ];
    corpus
        .into_iter()
        .map(|(name, code)| (name, spelled(&code)))
        .collect()
}

thread_local! {
    /// Whether [`spelled`] rewrites programs to `^` operators: set for the duration of
    /// [`with_caret_operators`].
    static CARET_OPERATORS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `test` with every program [`spelled`] passes spelled with `^` operators.
///
/// This is how a test pinned on a `^` operator's refinement duplicates a test of the
/// unrefined operators without restating its body: the test helpers that compile a
/// program (the corpora, `compile_ok` in `panes.rs`, `compile` in
/// `inspector_model/wire.rs`) pass it through [`spelled`]. The setting is per thread, so
/// tests running in parallel do not see each other's.
pub(crate) fn with_caret_operators(test: impl FnOnce()) {
    CARET_OPERATORS.with(|c| c.set(true));
    test();
    CARET_OPERATORS.with(|c| c.set(false));
}

/// Whether the running test is inside [`with_caret_operators`].
pub(crate) fn spells_caret_operators() -> bool {
    CARET_OPERATORS.with(|c| c.get())
}

/// `src` as the running test spells its programs: [`caret_operators`] inside
/// [`with_caret_operators`], unchanged otherwise.
pub(crate) fn spelled(src: &str) -> String {
    if spells_caret_operators() {
        caret_operators(src)
    } else {
        src.to_string()
    }
}

/// `src` with every operator that has a `^` sibling replaced by it: `+`, binary `-`, `*`,
/// `==`, `<`, `<=`, `>`, `>=`, `and`, `or` and `not`. Every other byte is kept, so the
/// layout, the comments and every other operator are unchanged.
///
/// A refinement's predicate, from `where` to the brace closing its refinement, is kept as
/// written: a predicate states the operation an operator's refinement records, which is the
/// unrefined operator's (`RefinementTemplate::predicate`).
///
/// A `-` is binary when the token before it ends an operand: a name, a literal or a
/// closing bracket. Any other `-` negates. A `+` beside a string literal concatenates, and
/// `^+` has no `String` row, so it is kept.
pub(crate) fn caret_operators(src: &str) -> String {
    use chl_parser::lexer::{Token, tokenize};
    let lexed = tokenize(chl_parser::FileId::ROOT, src);
    assert!(
        lexed.errors.is_empty(),
        "a corpus program lexes: {:?}",
        lexed.errors
    );
    let mut out = String::with_capacity(src.len() + src.len() / 8);
    let mut copied = 0;
    let mut previous: Option<&Token> = None;
    let mut braces = 0usize;
    // The brace depth of the refinement whose predicate the token is in.
    let mut predicate_of: Option<usize> = None;
    let tokens: Vec<_> = lexed
        .tokens
        .iter()
        // A layout token is zero-width, and no operand.
        .filter(|(_, span)| span.start != span.end)
        .collect();
    for (i, (token, span)) in tokens.iter().enumerate() {
        let operand_before = matches!(
            previous,
            Some(
                Token::Ident(_)
                    | Token::Int(_)
                    | Token::String(_)
                    | Token::True
                    | Token::False
                    | Token::RParen
                    | Token::RBracket
                    | Token::RBrace
            )
        );
        let concatenates = matches!(previous, Some(Token::String(_)))
            || matches!(tokens.get(i + 1), Some((Token::String(_), _)));
        match token {
            Token::LBrace => braces += 1,
            Token::RBrace => {
                if predicate_of == Some(braces) {
                    predicate_of = None;
                }
                braces = braces.saturating_sub(1);
            }
            Token::Where if predicate_of.is_none() => predicate_of = Some(braces),
            _ => {}
        }
        let rewrites = predicate_of.is_none()
            && match token {
                Token::Minus => operand_before,
                Token::Plus => !concatenates,
                Token::Star
                | Token::EqEq
                | Token::Lt
                | Token::LtE
                | Token::Gt
                | Token::GtE
                | Token::And
                | Token::Or
                | Token::Not => true,
                _ => false,
            };
        if rewrites {
            out.push_str(&src[copied..span.start]);
            out.push('^');
            copied = span.start;
        }
        previous = Some(token);
    }
    out.push_str(&src[copied..]);
    out
}

#[cfg(test)]
mod tests {
    use super::caret_operators;

    #[test]
    fn caret_operators_rewrites_exactly_the_operators_with_a_sibling() {
        assert_eq!(
            caret_operators("y = -x + (a - -1) * 2 if not p and q or r == s <= t else u // v\n"),
            "y = -x ^+ (a ^- -1) ^* 2 if ^not p ^and q ^or r ^== s ^<= t else u // v\n",
        );
        assert_eq!(
            caret_operators("[\"> \" + x for x in xs if x + \"\" == x]\n"),
            "[\"> \" + x for x in xs if x + \"\" ^== x]\n",
        );
        assert_eq!(
            caret_operators("z: {Int where _ == {a: 1}.a + 3 and _ > 0} = 1 + 3\n"),
            "z: {Int where _ == {a: 1}.a + 3 and _ > 0} = 1 ^+ 3\n",
        );
    }
}
