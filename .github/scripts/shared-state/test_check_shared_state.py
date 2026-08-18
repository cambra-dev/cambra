#!/usr/bin/env python3
"""Unit tests for the shared-state checker.

Run first in CI so a checker bug cannot mask a real back channel — or, worse,
manufacture a failure that sends someone editing correct code.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_shared_state import (  # noqa: E402
    _code_view,
    _inner_type,
    _justified,
    _normalize,
    check_file,
)

FAKE = Path(__file__).resolve().parents[3] / "src" / "interpreter" / "fake.rs"


def findings(src: str) -> list[str]:
    return [f.what for f in check_file(FAKE, src)[0]]


def exceptions(src: str) -> list[str]:
    return [f.what for f in check_file(FAKE, src)[1]]


class InnerType(unittest.TestCase):
    def test_takes_balanced_brackets_not_the_first_close(self) -> None:
        # The bug this replaced: a non-greedy regex stopped at the first `>>`,
        # yielding `Option<Box<dyn TileOperator` — which matches no allowlist
        # entry, so a legitimate cycle slot read as a violation.
        text = "type S = Rc<RefCell<Option<Box<dyn TileOperator>>>>;"
        start = text.index("Option")
        self.assertEqual(_inner_type(text, start), "Option<Box<dyn TileOperator>>")

    def test_unterminated_type_is_none(self) -> None:
        text = "x: Rc<RefCell<HashMap<String,"
        self.assertIsNone(_inner_type(text, text.index("HashMap")))


class Normalize(unittest.TestCase):
    def test_keeps_the_space_after_dyn(self) -> None:
        self.assertEqual(_normalize("Box< dyn Consumer >"), "Box<dyn Consumer>")

    def test_collapses_punctuation_spacing(self) -> None:
        self.assertEqual(
            _normalize("HashMap<(String,String) , RouteSender>"),
            "HashMap<(String, String), RouteSender>",
        )


class Justification(unittest.TestCase):
    def test_same_line(self) -> None:
        self.assertEqual(findings("x: Rc<RefCell<Rows>>, // shared-state-ok: why"), [])

    def test_preceding_line(self) -> None:
        self.assertEqual(findings("// shared-state-ok: why\nx: Rc<RefCell<Rows>>,"), [])

    def test_scans_up_past_doc_comments_and_attributes(self) -> None:
        src = "// shared-state-ok: why\n/// docs\n#[allow(dead_code)]\nx: Rc<RefCell<Rows>>,"
        self.assertEqual(findings(src), [])

    def test_does_not_leak_across_a_code_line(self) -> None:
        # An annotation two fields up must not silence an unrelated one below.
        src = "// shared-state-ok: why\na: Rc<RefCell<Rows>>,\nb: Rc<RefCell<Other>>,"
        self.assertEqual(findings(src), ["shared cell of `Other`"])

    def test_bare_marker_without_a_reason_does_not_count(self) -> None:
        self.assertEqual(
            findings("// shared-state-ok:\nx: Rc<RefCell<Rows>>,"),
            ["shared cell of `Rows`"],
        )


class Detection(unittest.TestCase):
    def test_flags_the_retired_writer_buffer(self) -> None:
        # The violation this checker exists for.
        self.assertEqual(
            findings("pub type BodyInputBuffer = Rc<RefCell<WriterBuffer>>;"),
            ["shared cell of `WriterBuffer`"],
        )

    def test_allows_known_kinds(self) -> None:
        src = (
            "pub type SharedConsumer = Rc<RefCell<dyn Consumer>>;\n"
            "shared: Rc<RefCell<FanOutShared>>,\n"
            "source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,\n"
        )
        self.assertEqual(findings(src), [])

    def test_flags_a_hand_rolled_cycle_slot(self) -> None:
        # `CycleSlot` is the one definition of this cell (justified at its own
        # declaration), so a second copy has to argue for itself rather than
        # inherit the first one's reasoning.
        self.assertEqual(
            findings("type WriterSlot = Rc<RefCell<Option<Box<dyn TileOperator>>>>;"),
            ["shared cell of `Option<Box<dyn TileOperator>>`"],
        )

    def test_flags_other_cell_kinds(self) -> None:
        src = "a: Arc<Mutex<Rows>>,\nb: Rc<Cell<usize>>,\nc: Arc<RwLock<Rows>>,"
        self.assertEqual(
            findings(src),
            [
                "shared cell of `Rows`",
                "shared cell of `usize`",
                "shared cell of `Rows`",
            ],
        )

    def test_flags_ambient_mutable_state(self) -> None:
        self.assertEqual(
            findings("static mut ROWS: usize = 0;"), ["ambient mutable state"]
        )
        self.assertEqual(
            findings("thread_local! { static ROWS: usize = 0; }"),
            ["ambient mutable state"],
        )

    def test_flags_a_static_holding_an_interior_mutable_cell(self) -> None:
        # A `static` needs no `mut` to be ambient: the cell supplies the
        # mutability and the name supplies the reach.
        self.assertEqual(
            findings("static ROWS: Mutex<Vec<Row>> = Mutex::new(Vec::new());"),
            ["ambient mutable state"],
        )
        self.assertEqual(
            findings("static ROWS: OnceLock<Mutex<Rows>> = OnceLock::new();"),
            ["ambient mutable state"],
        )

    def test_flags_a_bare_cell_field(self) -> None:
        # The owner supplies the sharing: `Arc<State>` over a `State` holding a
        # `Mutex` is `Arc<Mutex<…>>` with the layers swapped.
        self.assertEqual(findings("    pending: Mutex<Rows>,"), ["cell of `Rows`"])
        self.assertEqual(findings("    pub used: RefCell<bool>,"), ["cell of `bool`"])

    def test_a_bare_cell_takes_a_justification_like_any_other(self) -> None:
        self.assertEqual(findings("// shared-state-ok: why\n    pending: Mutex<Rows>,"), [])

    def test_a_local_binding_is_not_a_field(self) -> None:
        self.assertEqual(findings("    let seen: RefCell<Rows> = RefCell::new(rows);"), [])

    def test_ignores_commented_out_code(self) -> None:
        self.assertEqual(findings("// x: Rc<RefCell<Rows>>,"), [])

    def test_reads_through_a_type_wrapped_across_lines(self) -> None:
        self.assertEqual(
            findings("x: Rc<RefCell<HashMap<String,\n    Rows>>>,"),
            ["shared cell of `HashMap<String, Rows>`"],
        )

    def test_flags_a_cell_whose_wrapper_rustfmt_split(self) -> None:
        # The gap this closes: matching per line, `Rc<` and `RefCell<` land on
        # different lines and the site is not seen *at all* — worse than the
        # `<unterminated type>` report below, which at least fails the gate.
        self.assertEqual(
            findings("x: Rc<\n    RefCell<Rows>,\n>,"),
            ["shared cell of `Rows`"],
        )

    def test_reports_an_unbalanced_type_rather_than_guessing(self) -> None:
        self.assertEqual(
            findings("x: Rc<RefCell<HashMap<String,"),
            ["shared cell of `<unterminated type>`"],
        )



class Exceptions(unittest.TestCase):
    def test_a_justified_site_is_listed_not_dropped(self) -> None:
        # The suppression and the listing are the same fact seen twice: an excused
        # site produces no finding, and is exactly what `EXPECTED_EXCEPTIONS`
        # enumerates.
        src = "// shared-state-ok: why\nx: Rc<RefCell<Rows>>,"
        self.assertEqual(findings(src), [])
        self.assertEqual(exceptions(src), ["shared cell of `Rows`"])

    def test_an_allowlisted_kind_is_not_an_exception(self) -> None:
        # A known-legitimate kind is not a hole in the invariant, so it does not
        # need an entry.
        src = "shared: Rc<RefCell<FanOutShared>>,"
        self.assertEqual(findings(src), [])
        self.assertEqual(exceptions(src), [])


class TestCode(unittest.TestCase):
    def test_skips_a_cfg_test_module(self) -> None:
        src = (
            "a: Rc<RefCell<Rows>>,\n"
            "#[cfg(test)]\n"
            "mod tests {\n"
            "    struct Spy {\n"
            "        log: Rc<RefCell<Vec<Guard>>>,\n"
            "    }\n"
            "}\n"
        )
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_skips_a_cfg_test_fn_without_swallowing_what_follows(self) -> None:
        # `#[cfg(test)]` is not always the trailing `mod tests` — it also gates a
        # single function mid-file, and the code after it is still production.
        src = (
            "impl E {\n"
            "    #[cfg(test)]\n"
            "    fn for_test() -> Self {\n"
            "        let _: Rc<RefCell<Vec<Guard>>>;\n"
            "    }\n"
            "}\n"
            "b: Rc<RefCell<Rows>>,\n"
        )
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_skips_a_cfg_test_use(self) -> None:
        src = "#[cfg(test)]\nuse foo::Rc;\nb: Rc<RefCell<Rows>>,\n"
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_does_not_skip_a_test_helpers_feature_gate(self) -> None:
        # That configuration compiles into a real library build, so it is
        # production code that tests also use.
        src = '#[cfg(any(test, feature = "test-helpers"))]\npub fn h() {\n    let _: Rc<RefCell<Rows>>;\n}\n'
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_does_not_skip_cfg_not_test(self) -> None:
        src = "#[cfg(not(test))]\nb: Rc<RefCell<Rows>>,\n"
        self.assertEqual(findings(src), ["shared cell of `Rows`"])


class CodeView(unittest.TestCase):
    def test_blanks_a_brace_inside_a_string(self) -> None:
        # The brace matching that skips a `#[cfg(test)]` item would otherwise
        # desync on it and blank an arbitrary amount of the file.
        src = (
            "#[cfg(test)]\n"
            'fn t() { let s = "}"; let _: Rc<RefCell<Spy>>; }\n'
            "b: Rc<RefCell<Rows>>,\n"
        )
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_blanks_a_raw_string(self) -> None:
        self.assertEqual(findings('let s = r#"x: Rc<RefCell<Rows>>,"#;'), [])

    def test_blanks_a_block_comment(self) -> None:
        self.assertEqual(findings("/* x: Rc<RefCell<Rows>>, */"), [])

    def test_a_lifetime_is_not_a_char_literal(self) -> None:
        # Treating `'a` as an unterminated char literal would blank forward to
        # the next quote and hide everything between.
        src = "struct S<'a> { r: &'a u8 }\nb: Rc<RefCell<Rows>>,\n"
        self.assertEqual(findings(src), ["shared cell of `Rows`"])

    def test_preserves_line_numbers(self) -> None:
        src = '// a comment\n/* block */\nx: Rc<RefCell<Rows>>,'
        self.assertEqual(_code_view(src).count("\n"), src.count("\n"))
        self.assertEqual(check_file(FAKE, src)[0][0].line, 3)


if __name__ == "__main__":
    unittest.main(verbosity=0)
