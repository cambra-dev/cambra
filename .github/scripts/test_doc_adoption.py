#!/usr/bin/env python3
"""Tests for `doc-adoption.py`'s diff scan.

Each case is a unified diff, because the defect is a property of the diff and not
of the file: the same final text is a defect when it arrived by insertion into a
doc block and fine when the block was written for it.
"""

import importlib.util
import pathlib
import unittest

_spec = importlib.util.spec_from_file_location(
    "doc_adoption", pathlib.Path(__file__).with_name("doc-adoption.py")
)
doc_adoption = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(doc_adoption)
scan = doc_adoption.scan


def diff(path, body):
    return f"--- a/{path}\n+++ b/{path}\n@@ -1,3 +1,9 @@\n{body}"


class ScanTest(unittest.TestCase):
    def test_item_inserted_into_a_doc_block_is_reported(self):
        d = diff(
            "src/a.rs",
            " /// Compile the thing.\n"
            " ///\n"
            "+/// What a binding compiles to.\n"
            "+enum LetBinding {}\n"
            "+\n"
            " /// The rest of the original doc.\n"
            " fn compile() {}\n",
        )
        hits = scan(d)
        self.assertEqual(len(hits), 1)
        self.assertIn("enum LetBinding", hits[0][2])

    def test_item_appended_after_an_item_is_not_reported(self):
        d = diff(
            "src/a.rs",
            " fn compile() {}\n"
            " \n"
            "+/// What a binding compiles to.\n"
            "+enum LetBinding {}\n",
        )
        self.assertEqual(scan(d), [])

    def test_item_with_no_doc_of_its_own_is_not_reported(self):
        d = diff("src/a.rs", " /// Compile the thing.\n+enum LetBinding {}\n fn compile() {}\n")
        self.assertEqual(scan(d), [])

    def test_a_wholly_new_file_is_not_reported(self):
        d = "--- /dev/null\n+++ b/src/a.rs\n@@ -0,0 +1,2 @@\n+/// Doc.\n+fn f() {}\n"
        self.assertEqual(scan(d), [])

    def test_attributes_between_doc_and_item_are_skipped(self):
        d = diff(
            "src/a.rs",
            " /// Original doc.\n"
            " ///\n"
            "+/// New test.\n"
            "+#[test]\n"
            "+fn inserted() {}\n"
            "+\n"
            " fn displaced() {}\n",
        )
        self.assertEqual(len(scan(d)), 1)

    def test_suppression_marker_silences_the_run(self):
        d = diff(
            "src/a.rs",
            " /// Compile the thing.\n"
            " ///\n"
            "+/// Deliberate. doc-adoption-ok\n"
            "+enum LetBinding {}\n"
            " fn compile() {}\n",
        )
        self.assertEqual(scan(d), [])

    def test_typescript_is_scanned(self):
        d = diff(
            "web/src/a.ts",
            " // Validate the node.\n"
            "+// Validate the spans.\n"
            "+function validateSpans() {}\n"
            "+\n"
            " function validateNode() {}\n",
        )
        self.assertEqual(len(scan(d)), 1)

    def test_an_unscanned_language_is_ignored(self):
        d = diff("docs/a.md", " # Heading\n+# Another\n+text\n")
        self.assertEqual(scan(d), [])

    def test_a_removed_context_line_does_not_anchor(self):
        d = diff("src/a.rs", " /// Doc.\n-/// Removed.\n+/// New.\n+fn inserted() {}\n")
        self.assertEqual(scan(d), [])


if __name__ == "__main__":
    unittest.main()
