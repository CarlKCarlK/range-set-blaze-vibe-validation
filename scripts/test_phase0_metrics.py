#!/usr/bin/env python3
"""Regression tests for the Phase 0/v2 lexical collector."""

import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).with_name("phase0_metrics.py")
spec = importlib.util.spec_from_file_location("phase0_metrics", SCRIPT)
metrics = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(metrics)


class LexerTests(unittest.TestCase):
    def test_primed_identifiers_are_code(self):
        text = ("def mkNR' := 1\n"
                "def h' := mkNR'\n"
                "def h'' := h'\n"
                "def xs' := h''\n"
                "-- comment after primed identifiers\n"
                "have later := xs'\n")
        clean = metrics.strip_comments(text)
        self.assertIn("def mkNR' := 1", clean)
        self.assertIn("def h'' := h'", clean)
        self.assertIn("have later := xs'", clean)
        row = metrics.count_source("Test.lean", text)
        self.assertEqual(row["active_code_loc"], 5)
        self.assertEqual(row["tokens"]["have"], 1)

    def test_character_literals_strings_and_comments(self):
        text = (r'''def chars := ['a', '\n', '\\', '\x41', '\u{41}']
def text := "a string with -- and /- nested-looking text -/"
-- a line comment with ' and /-
/- outer comment
   /- nested comment -/
   still a comment
-/
def after := 'x'
''')
        clean = metrics.strip_comments(text)
        self.assertIn("['a', '\\n', '\\\\', '\\x41', '\\u{41}']", clean)
        self.assertIn('"a string with -- and /- nested-looking text -/"', clean)
        self.assertIn("def after := 'x'", clean)
        self.assertNotIn("still a comment", clean)

    def test_exact_mknr_regression_does_not_reclassify_later_text(self):
        declaration = "/- Pack endpoints -/\nprivate def mkNR' (x : Int) := x\n"
        later = ("def h' := 1\n"
                 "have later := h'\n"
                 "def c := 'a'\n")
        with_declaration = metrics.strip_comments(declaration + later)
        without_declaration = metrics.strip_comments(later)
        self.assertEqual(with_declaration.splitlines()[-3:], without_declaration.splitlines())
        before = metrics.count_source("Test.lean", declaration + later)
        after = metrics.count_source("Test.lean", later)
        self.assertEqual(before["tokens"]["have"], after["tokens"]["have"])
        self.assertEqual(before["active_code_loc"] - after["active_code_loc"], 1)


if __name__ == "__main__":
    unittest.main()
