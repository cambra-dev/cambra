#!/usr/bin/env python3
"""Unit tests for the doc-reference checker's load-bearing logic.

The slug algorithm and the Rust comment scanner are the parts most likely to
drift or be subtly wrong, so they carry the most cases here. Run with
`python3 -m unittest` from this directory (ci.sh does this).
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_doc_refs as c  # noqa: E402


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


class TestCitationTitles(unittest.TestCase):
    def titles(self, tail):
        return list(c._cited_titles(tail))

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


class TestRustCommentScanner(unittest.TestCase):
    def spans(self, src):
        return list(c._rust_comment_spans(src))

    def test_line_comment(self):
        self.assertEqual(self.spans("let x = 1; // see bar.md\n"),
                         [(1, "// see bar.md")])

    def test_md_in_string_is_not_a_comment(self):
        # A `.md` inside a string literal must not be scanned as a doc ref.
        spans = self.spans('let p = "docs/foo.md";\n// real ref: baz.md\n')
        joined = " ".join(s for _, s in spans)
        self.assertNotIn("docs/foo.md", joined)
        self.assertIn("baz.md", joined)

    def test_nested_block_comment(self):
        spans = self.spans("/* outer /* inner qux.md */ still */ code\n")
        self.assertEqual(len(spans), 1)
        self.assertIn("qux.md", spans[0][1])

    def test_line_numbers_after_multiline_string(self):
        src = 'let s = "a\nb\nc";\n// ref.md here\n'
        # The comment sits on line 4 after a 3-line string literal.
        self.assertEqual(self.spans(src), [(4, "// ref.md here")])


if __name__ == "__main__":
    unittest.main()
