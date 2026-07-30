#!/usr/bin/env python3
"""Tests for the doc-reference checker.

Most of these run the real checks over a throwaway repo tree (`CheckerCase`):
a `{path: contents}` dict goes in, the reported problems come out. That is the
only way to cover the decisions that live in the check functions themselves —
which references count as citations and which are left alone — and it is what
breaks when the checker regresses.

The narrower classes at the bottom cover the pieces that genuinely are
standalone grammars, where a fixture would obscure what is under test: the
heading-slug algorithm, the citation run, the Rust comment scanner, and the
source-path token.

Run with `python3 -m unittest` from this directory (ci.sh does this).
"""

import os
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_doc_refs as c  # noqa: E402


class CheckerCase(unittest.TestCase):
    """Runs the real checks over a fixture tree."""

    CHECKS = (c.check_markdown_links, c.check_doc_source_paths, c.check_doc_citations)

    def check(self, files, checks=None):
        """`{relpath: contents}` -> `["path:line: detail", ...]`.

        Contents are dedented and their leading newline dropped, so a
        triple-quoted fixture can show the line wrapping that is under test and
        still start at line 1.
        """
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel, text in files.items():
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")
            problems: list[c.Problem] = []
            repo = c.Repo(root)
            for check in checks or self.CHECKS:
                check(repo, problems)
            return [f"{p.source}: {p.detail}" for p in problems]

    def assertClean(self, files):
        self.assertEqual(self.check(files), [])

    def assertOneProblem(self, files, *fragments):
        problems = self.check(files)
        self.assertEqual(len(problems), 1, problems)
        for fragment in fragments:
            self.assertIn(fragment, problems[0])


class TestWrappedCitations(CheckerCase):
    """The defect this all started from: a citation wrapped across two `///`
    lines never matched, so its title went unchecked and nothing said so."""

    DOC = """
        # Application shape

        ## Closing the blind spots (no separate pass)
        """

    WRAPPED = '''
        /// The shape edge — see `d.md`, "Application
        /// shape".
        pub fn f() {}
        '''

    def test_wrapped_citation_is_checked_and_passes(self):
        self.assertClean({"d.md": self.DOC, "a.rs": self.WRAPPED})

    def test_wrapped_stale_citation_is_caught(self):
        # The regression test proper: on a per-line scan this reference is
        # invisible and the file passes.
        self.assertOneProblem(
            {"d.md": "# Something else\n", "a.rs": self.WRAPPED},
            "a.rs:1",
            'cited section "Application shape" not found',
        )

    def test_wrapped_title_may_not_cross_a_blank_comment_line(self):
        # The blank line ends the thought, so the quote never pairs — which
        # surfaces as the unterminated diagnostic rather than as a title
        # stitched together across two paragraphs.
        self.assertOneProblem(
            {
                "d.md": "# Application shape\n",
                "a.rs": '''
                    /// See `d.md`, "Application
                    ///
                    /// shape".
                    pub fn f() {}
                    ''',
            },
            "unterminated quoted citation",
        )

    def test_trailing_comments_on_separate_lines_do_not_join(self):
        # Code between them means two thoughts, not one wrapped citation — so
        # the quote on line 2 is not a title and nothing is reported.
        self.assertClean(
            {
                "d.md": "# Nothing\n",
                "a.rs": '''
                    let a = 1; // see `d.md`,
                    let b = 2; // "Application shape"
                    ''',
            }
        )

    def test_line_number_points_at_the_reference(self):
        self.assertOneProblem(
            {
                "d.md": "# Nothing\n",
                "a.rs": '''
                    //! Module header.
                    //!
                    //! Later on, see `d.md`, "Application
                    //! shape".
                    ''',
            },
            "a.rs:3",
        )

    def test_unterminated_citation_is_reported(self):
        self.assertOneProblem(
            {
                "d.md": "# Application shape\n",
                "a.rs": '/// see `d.md`, "Application shape\npub fn f() {}\n',
            },
            "unterminated quoted citation after d.md",
        )

    def test_abbreviated_title_is_not_the_heading(self):
        self.assertOneProblem(
            {
                "d.md": "# The model: histories and causal recursion\n",
                "a.rs": '/// see `d.md`, "The model".\n',
            },
            'cited section "The model" not found',
        )


class TestWrappedLinks(CheckerCase):
    """Check A reads whole prose for the same reason: the docs are
    hard-wrapped, so a link's text wraps like any other phrase."""

    def test_wrapped_link_text_is_still_checked(self):
        self.assertOneProblem(
            {
                "d.md": """
                    see the [ordering
                    rules](gone.md) for details
                    """
            },
            "link target does not exist: gone.md",
        )

    def test_wrapped_link_anchor_is_checked(self):
        self.assertOneProblem(
            {
                "d.md": "see the [ordering\nrules](t.md#nope)\n",
                "t.md": "# Ordering\n",
            },
            "anchor #nope not found",
        )

    def test_link_text_wrap_is_bounded(self):
        # Four lines of prose between `[` and `](` is not a link text — if it
        # were read as one, the missing target would be reported.
        self.assertClean(
            {
                "d.md": """
                    a [stray
                    bracket
                    and more
                    prose here
                    not a link](gone.md)
                    """
            }
        )

    def test_bracket_run_does_not_cross_a_paragraph(self):
        self.assertClean(
            {
                "d.md": """
                    a [1 stray bracket

                    more prose

                    not a link](gone.md)
                    """
            }
        )

    def test_fenced_and_inline_code_links_are_not_checked(self):
        self.assertClean(
            {
                "d.md": """
                    ```
                    [a](gone.md)
                    ```
                    prose `[b](gone.md)` only
                    """
            }
        )


class TestDocProseCitations(CheckerCase):
    """Check B reads doc prose as well as Rust comments — a doc citing another
    doc's section names it the same way."""

    def test_stale_citation_in_doc_prose_is_caught(self):
        self.assertOneProblem(
            {
                "a.md": 'see t.md, "The model"\n',
                "t.md": "# Something else\n",
            },
            'cited section "The model" not found',
        )

    def test_citation_hanging_off_a_link(self):
        self.assertOneProblem(
            {
                "a.md": 'see [t.md](t.md) §4 ("The model")\n',
                "t.md": "# Something else\n",
            },
            'cited section "The model" not found',
        )

    def test_title_backticks_survive_inline_code_handling(self):
        # Headings here are full of backticks; blanking inline code (as the
        # link scan does) would mangle the title into something that matches
        # nothing.
        self.assertClean(
            {
                "a.md": 'see t.md, "`Mut` is a CCL type"\n',
                "t.md": "# `Mut` is a CCL type\n",
            }
        )

    def test_bare_doc_name_in_prose_is_not_a_citation(self):
        # Two files share the name, so an ambiguity error would fire if this
        # mention were treated as a citation. In prose it is just prose.
        self.assertClean(
            {
                "a.md": "the pipeline is described in lowering.md.\n",
                "one/lowering.md": "# One\n",
                "two/lowering.md": "# Two\n",
            }
        )

    def test_quoting_a_title_demands_an_unambiguous_path(self):
        self.assertOneProblem(
            {
                "a.md": 'see lowering.md, "One"\n',
                "one/lowering.md": "# One\n",
                "two/lowering.md": "# Two\n",
            },
            "is ambiguous",
        )

    def test_comment_ref_must_resolve_even_without_a_title(self):
        # Unlike prose, a comment's `.md` mention *is* the citation.
        self.assertOneProblem(
            {"a.rs": "//! see `nowhere.md` for details\n"},
            "doc ref does not resolve: nowhere.md",
        )

    def test_dotfile_path_resolves(self):
        # `lstrip("./")` strips characters, not a prefix: it ate the leading
        # dot and lost the file entirely.
        self.assertClean(
            {
                "a.rs": '//! see `.github/scripts/doc-refs/README.md`, "Usage"\n',
                ".github/scripts/doc-refs/README.md": "# Usage\n",
            }
        )


class TestOptOut(CheckerCase):
    """`doc-refs-ignore` is honored by every check — prose that illustrates the
    reference syntax needs it as much as a migration note does."""

    def test_marker_covers_link_citation_and_source_path(self):
        self.assertClean(
            {
                "a.md": (
                    'see [x](gone.md), t.md "Nope" and `deleted.rs`'
                    " <!-- doc-refs-ignore -->\n"
                ),
                "t.md": "# Something else\n",
            }
        )

    def test_without_the_marker_all_three_fire(self):
        problems = self.check(
            {
                "a.md": 'see [x](gone.md), t.md "Nope" and `deleted.rs`\n',
                "t.md": "# Something else\n",
            }
        )
        self.assertEqual(len(problems), 3, problems)

    def test_marker_in_a_rust_comment(self):
        self.assertClean({"a.rs": "//! `nowhere.md` doc-refs-ignore\n"})


class TestSourcePaths(CheckerCase):
    """Check C: backticked source paths in doc prose."""

    def test_missing_source_path_is_caught(self):
        self.assertOneProblem(
            {"a.md": "the pass lives in `src/gone.rs`\n"},
            "source-path mention does not resolve",
        )

    def test_ambiguous_bare_name_counts_as_resolved(self):
        self.assertClean(
            {
                "a.md": "see `mod.rs`\n",
                "one/mod.rs": "",
                "two/mod.rs": "",
            }
        )


class TestSlug(unittest.TestCase):
    def test_github_examples(self):
        cases = {
            # dot dropped, spaces -> hyphens
            "4.5 Dependent refinements via Pi types": (
                "45-dependent-refinements-via-pi-types"
            ),
            # em-dash removed, surrounding spaces each become a hyphen (no collapse)
            "Transact — the domain-parameterized recurrence carrier": (
                "transact--the-domain-parameterized-recurrence-carrier"
            ),
            # the nastiest real anchor: symbols vanish, spaces stay as hyphens
            "Deferred collection operators — `defer` / `<<` / `<<=`": (
                "deferred-collection-operators--defer----"
            ),
            "`Cast` — explicit refinement acquisition": (
                "cast--explicit-refinement-acquisition"
            ),
            # non-ASCII letters and underscores are kept; parens/colon dropped
            "Structured names and α-uniquification (Barendregt convention)": (
                "structured-names-and-α-uniquification-barendregt-convention"
            ),
            "Lambda Elimination (`ccl/lambda_elim.rs`)": (
                "lambda-elimination-ccllambda_elimrs"
            ),
            "Purity invariant: CCL is a pure value language": (
                "purity-invariant-ccl-is-a-pure-value-language"
            ),
        }
        for heading, expected in cases.items():
            self.assertEqual(c._slug_base(heading), expected, heading)

    def test_wrapped_title_normalizes_to_one_line(self):
        # The wrap's newline and the next line's indent stand for one space;
        # `_slug_base` would otherwise make a hyphen of each.
        self.assertEqual(
            c._slug_base(c._normalize_title("Closing the single-sided blind\n spots")),
            "closing-the-single-sided-blind-spots",
        )


class TestHeadingAnchors(unittest.TestCase):
    def test_dedup_and_closed_atx(self):
        md = "# Foo\n## Foo\n### Foo ###\n"
        self.assertEqual(c.heading_anchors(md), {"foo", "foo-1", "foo-2"})

    def test_fenced_code_headings_ignored(self):
        md = "# Real\n```\n# Not a heading\n```\n## Also real\n"
        self.assertEqual(c.heading_anchors(md), {"real", "also-real"})

    def test_explicit_html_anchor(self):
        md = '<a id="stable-slug"></a>\n## Heading\n'
        self.assertEqual(c.heading_anchors(md), {"stable-slug", "heading"})


class TestCitationRun(unittest.TestCase):
    """The grammar of what follows a doc ref: which quotes are section titles
    and where the run stops.

    `tail` is the text immediately after the `.md` reference, as the checker
    sees it — comment markers already stripped, so a wrap shows up as a newline
    plus the indentation that stood after the `///`.
    """

    def titles(self, tail):
        return [c._one_line(t) for t in c._cited_titles(tail).titles]

    def dangling(self, tail):
        return c._cited_titles(tail).dangling

    def test_slash_separated_titles(self):
        self.assertEqual(
            self.titles('`, "The model" / "`LetRec`"'),
            ["The model", "`LetRec`"],
        )

    def test_rule_quote_is_not_a_title(self):
        # A quote introduced by a word/`:` clause is body text, not a heading.
        self.assertEqual(self.titles(', rule 1: "a Mut-typed value"'), [])

    def test_section_number_and_parens(self):
        self.assertEqual(
            self.titles(' §4 ("Retire desugar_defers")'),
            ["Retire desugar_defers"],
        )

    def test_title_wraps_mid_heading(self):
        self.assertEqual(self.titles(', "Application\n shape"'), ["Application shape"])

    def test_glue_wraps_before_the_title(self):
        self.assertEqual(self.titles(',\n "Application shape"'), ["Application shape"])

    def test_second_title_may_wrap(self):
        self.assertEqual(
            self.titles(', "The model" /\n "`LetRec`\n carrier"'),
            ["The model", "`LetRec` carrier"],
        )

    def test_unpaired_quote_cannot_reach_across_the_block(self):
        # Three wraps is past any real heading citation — pairing this opening
        # quote with one that far away would invent a title.
        tail = ', "Application\n shape\n and\n more"'
        self.assertEqual(self.titles(tail), [])
        self.assertTrue(self.dangling(tail))

    def test_dangling_after_a_good_title(self):
        tail = ', "The model" / "`LetRec`'
        self.assertEqual(self.titles(tail), ["The model"])
        self.assertTrue(self.dangling(tail))

    def test_no_quote_at_all_is_not_dangling(self):
        self.assertFalse(self.dangling(" for the details."))


class TestRustCommentScanner(unittest.TestCase):
    def comments(self, src):
        return [(p.first_line, p.text) for p in c._rust_comments(src)]

    def test_line_comment(self):
        self.assertEqual(
            self.comments("let x = 1; // see bar.md\n"), [(1, " see bar.md")]
        )

    def test_md_in_string_is_not_a_comment(self):
        # A `.md` inside a string literal must not be scanned as a doc ref.
        joined = " ".join(
            t for _, t in self.comments('let p = "docs/foo.md";\n// real ref: baz.md\n')
        )
        self.assertNotIn("docs/foo.md", joined)
        self.assertIn("baz.md", joined)

    def test_nested_block_comment(self):
        comments = self.comments("/* outer /* inner qux.md */ still */ code\n")
        self.assertEqual(len(comments), 1)
        self.assertIn("qux.md", comments[0][1])

    def test_line_numbers_after_multiline_string(self):
        src = 'let s = "a\nb\nc";\n// ref.md here\n'
        # The comment sits on line 4 after a 3-line string literal.
        self.assertEqual(self.comments(src), [(4, " ref.md here")])

    def test_consecutive_line_comments_are_one_comment(self):
        src = '/// see ir.md, "Application\n/// shape"\nfn f() {}\n'
        self.assertEqual(
            self.comments(src), [(1, ' see ir.md, "Application\n shape"')]
        )

    def test_blank_line_ends_a_run(self):
        self.assertEqual(
            self.comments("// one\n\n// two\n"), [(1, " one"), (3, " two")]
        )

    def test_line_at_maps_offsets_back_to_source_lines(self):
        (comment,) = c._rust_comments("fn f() {}\n// a\n// b ir.md\n// c\n")
        self.assertEqual(comment.first_line, 2)
        self.assertEqual(comment.line_at(comment.text.index("ir.md")), 3)
        self.assertEqual(comment.line_at(comment.text.index(" c")), 4)

    def test_block_comment_star_decoration_is_stripped(self):
        (comment,) = c._rust_comments('/* see ir.md, "Application\n * shape" */\n')
        self.assertIn('"Application\n shape"', comment.text)


class TestSourcePathToken(unittest.TestCase):
    """The `_SRC_PATH` gate for check C — accept real path tokens, reject prose."""

    def match(self, span):
        m = c._SRC_PATH.match(span)
        return m.group(1) if m else None

    def test_accepts_paths(self):
        self.assertEqual(self.match("ast.rs"), "ast.rs")
        self.assertEqual(self.match("src/ccl/lower/loops.rs"), "src/ccl/lower/loops.rs")
        self.assertEqual(self.match("Cargo.toml"), "Cargo.toml")
        # a trailing line/range ref is stripped from the resolved path
        self.assertEqual(self.match("fan.rs:170"), "fan.rs")
        self.assertEqual(self.match("fan.rs:170-182"), "fan.rs")

    def test_rejects_non_paths(self):
        for span in (
            "the map function",
            "a.rs with trailing words",
            "ir.md#some-anchor",
            "1.5x faster",
            "e.g.",
        ):
            self.assertIsNone(self.match(span), span)


if __name__ == "__main__":
    unittest.main()
