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
        return c._cited_titles(tail)[0]

    def dangling(self, tail):
        return c._cited_titles(tail)[1]

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


class TestWrappedCitations(unittest.TestCase):
    """A citation near the right margin wraps onto the next comment line. The
    tail here is what `check_code_refs` sees: a comment run with its `//`
    markers already stripped."""

    def titles(self, tail):
        return [" ".join(t.split()) for t in c._cited_titles(tail)[0]]

    def dangling(self, tail):
        return c._cited_titles(tail)[1]

    def test_title_wraps_mid_heading(self):
        self.assertEqual(self.titles(', "Application\n shape"'), ["Application shape"])

    def test_glue_wraps_before_the_title(self):
        self.assertEqual(self.titles(',\n "Application shape"'), ["Application shape"])

    def test_wrapped_title_slugs_as_one_line(self):
        # The wrap's newline + indent stands for the single space it replaced;
        # `_slug_base` would otherwise turn each of them into its own hyphen.
        title = self.titles(', "Closing the single-sided blind\n spots"')[0]
        self.assertEqual(
            c._slug_base(c._normalize_title(title)),
            "closing-the-single-sided-blind-spots",
        )

    def test_second_title_may_wrap(self):
        self.assertEqual(
            self.titles(', "The model" /\n "`LetRec`\n carrier"'),
            ["The model", "`LetRec` carrier"],
        )

    def test_blank_comment_line_ends_the_citation(self):
        # A new paragraph is a new thought: its quotes are body text.
        self.assertEqual(self.titles(' ir.md tail\n\n "Not a title"'), [])

    def test_unpaired_quote_cannot_reach_across_the_block(self):
        # Three wraps is past any real heading citation — pairing this opening
        # quote with a quote that far away would invent a title.
        tail = ', "Application\n shape\n and\n more"'
        self.assertEqual(self.titles(tail), [])
        self.assertTrue(self.dangling(tail))

    def test_dangling_quote_is_reported_not_ignored(self):
        self.assertEqual(self.titles(', "Application shape'), [])
        self.assertTrue(self.dangling(', "Application shape'))

    def test_no_quote_at_all_is_not_dangling(self):
        self.assertFalse(self.dangling(" for the details."))

    def test_dangling_after_a_good_title(self):
        tail = ', "The model" / "`LetRec`'
        self.assertEqual(self.titles(tail), ["The model"])
        self.assertTrue(self.dangling(tail))


class TestRustCommentScanner(unittest.TestCase):
    def spans(self, src):
        return [(cm.first_line, cm.text) for cm in c._rust_comments(src)]

    def test_line_comment(self):
        self.assertEqual(self.spans("let x = 1; // see bar.md\n"),
                         [(1, " see bar.md")])

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
        self.assertEqual(self.spans(src), [(4, " ref.md here")])

    def test_consecutive_line_comments_are_one_comment(self):
        # A sentence spans the lines it is wrapped over — the scanner must
        # hand the checks the whole run, markers stripped.
        src = '/// see ir.md, "Application\n/// shape"\nfn f() {}\n'
        self.assertEqual(self.spans(src), [(1, ' see ir.md, "Application\n shape"')])

    def test_trailing_comments_after_code_do_not_join(self):
        # Code between them means two separate thoughts, not one wrapped one.
        src = "let a = 1; // first\nlet b = 2; // second\n"
        self.assertEqual(self.spans(src), [(1, " first"), (2, " second")])

    def test_blank_line_ends_a_run(self):
        src = "// one\n\n// two\n"
        self.assertEqual(self.spans(src), [(1, " one"), (3, " two")])

    def test_line_at_maps_offsets_back_to_source_lines(self):
        src = "fn f() {}\n// a\n// b ir.md\n// c\n"
        (cm,) = c._rust_comments(src)
        self.assertEqual(cm.first_line, 2)
        self.assertEqual(cm.line_at(cm.text.index("ir.md")), 3)
        self.assertEqual(cm.line_at(cm.text.index(" c")), 4)

    def test_block_comment_star_decoration_is_stripped(self):
        src = '/* see ir.md, "Application\n * shape" */\n'
        (cm,) = c._rust_comments(src)
        self.assertIn('"Application\n shape"', cm.text)


class TestMarkdownLinkScanner(unittest.TestCase):
    """Links are found over whole prose, not line by line: the docs are
    hard-wrapped, so a link's text wraps like any other phrase."""

    def targets(self, md):
        prose = c._prose_lines(md)
        return [m.group(1) for m in c._MD_LINK.finditer(prose)]

    def test_link_text_wraps(self):
        self.assertEqual(
            self.targets("see the [ordering\nrules](design/mutability.md#ordering)\n"),
            ["design/mutability.md#ordering"],
        )

    def test_fenced_and_inline_code_links_are_not_checked(self):
        md = "```\n[a](gone.md)\n```\nprose `[b](gone.md)` and [c](real.md)\n"
        self.assertEqual(self.targets(md), ["real.md"])

    def test_line_numbers_survive_blanking(self):
        md = "# T\n\n```\n[a](gone.md)\n```\n\nsee [c](real.md)\n"
        prose = c._prose_lines(md)
        (m,) = list(c._MD_LINK.finditer(prose))
        self.assertEqual(c._line_at(prose, m.start()), 7)

    def test_ignore_marker_skips_a_link(self):
        # The opt-out marker is honored by every check, not just check C —
        # prose that illustrates the reference syntax needs it as much as a
        # migration note does.
        md = "a [x](gone.md) <!-- doc-refs-ignore -->\nb [y](real.md)\n"
        prose = c._prose_lines(md)
        kept = [
            m.group(1)
            for m in c._MD_LINK.finditer(prose)
            if c.IGNORE_MARKER not in c._line_of(prose, m.start())
        ]
        self.assertEqual(kept, ["real.md"])

    def test_bracket_run_does_not_reach_across_a_paragraph(self):
        # An unpaired `[` must not pair with a `](` two paragraphs later.
        md = "a [1 stray bracket\n\nmore prose\n\nnot a link](nope.md)\n"
        self.assertEqual(self.targets(md), [])

    def test_link_text_wrap_is_bounded(self):
        # Four lines of prose between `[` and `](` is not a link text.
        md = "a [stray\nbracket\nand more\nprose here\nnot a link](nope.md)\n"
        self.assertEqual(self.targets(md), [])


class TestDocProseCitations(unittest.TestCase):
    """Check B reads doc prose as well as Rust comments — a doc citing another
    doc's section names it the same way."""

    def cited(self, md):
        """Every (title, came-off-a-link) the doc-prose scan finds, as the
        checker walks it: one pass over all `.md` refs in the file."""
        prose = c._doc_prose(md).text
        out = []
        for m in c._MD_REF.finditer(prose):
            tail = c._citation_tail(prose, m)
            if tail is None:
                continue
            at, in_link = tail
            out += [
                (" ".join(t.split()), in_link) for t in c._cited_titles(prose[at:])[0]
            ]
        return out

    def test_inline_code_survives_so_titles_are_intact(self):
        # Unlike the link scanner, this one must keep backticks: headings here
        # are full of them, and stripping the spans would mangle the title.
        self.assertEqual(
            self.cited('see mutability.md, "`Mut` is a CCL type"\n'),
            [("`Mut` is a CCL type", False)],
        )

    def test_citation_hanging_off_a_link(self):
        # Two refs here — the link text and the destination. Only the
        # destination carries the citation; the text's tail starts at `](`,
        # which is not citation glue, so it contributes nothing.
        self.assertEqual(
            self.cited('see [mutability.md](mutability.md) "The model"\n'),
            [("The model", True)],
        )

    def test_section_marker_citation_after_a_link(self):
        # The `§"Title"` form the docs grew before it was checkable.
        self.assertEqual(
            self.cited('is [x](mutability.md) §4 ("The model")\n'),
            [("The model", True)],
        )

    def test_bare_doc_name_in_prose_is_not_a_citation(self):
        self.assertEqual(self.cited("the pipeline is described in mutability.md.\n"), [])

    def test_fenced_code_is_blanked(self):
        prose = c._doc_prose('# T\n```\nsee gone.md, "Nope"\n```\nreal\n').text
        self.assertIsNone(c._MD_REF.search(prose))

    def test_unclosed_link_yields_no_tail(self):
        prose = "see [x](mutability.md\n"
        m = c._MD_REF.search(prose)
        self.assertIsNone(c._citation_tail(prose, m))

    def test_ignore_marker_line_lookup(self):
        text = "one\ntwo doc-refs-ignore\nthree\n"
        self.assertIn(c.IGNORE_MARKER, c._line_of(text, text.index("two")))
        self.assertNotIn(c.IGNORE_MARKER, c._line_of(text, text.index("three")))


class TestRepoResolution(unittest.TestCase):
    def test_dotfile_path_resolves(self):
        # `lstrip("./")` would eat the leading dot and lose the file entirely.
        repo = c.Repo()
        resolved, _ = repo.resolve_suffix(".github/scripts/doc-refs/README.md")
        self.assertIsNotNone(resolved)
        resolved_dotted, _ = repo.resolve_suffix("./ci.sh")
        self.assertEqual(str(resolved_dotted), "ci.sh")


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
        for span in ("the map function", "a.rs with trailing words",
                     "ir.md#some-anchor", "1.5x faster", "e.g."):
            self.assertIsNone(self.match(span), span)


if __name__ == "__main__":
    unittest.main()
