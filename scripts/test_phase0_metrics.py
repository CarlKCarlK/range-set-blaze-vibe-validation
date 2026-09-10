#!/usr/bin/env python3
"""Regression tests for the corrected-v2 fields and v3 dashboard collector."""

import importlib.util
import pathlib
import sys
import unittest

SCRIPT = pathlib.Path(__file__).with_name("phase0_metrics.py")
sys.dont_write_bytecode = True
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

    def test_dashboard_ignores_comments_docstrings_strings_and_characters(self):
        text = ('''/-! `cases have simp List.span` in a module docstring. -/\n'''
                '''-- by_cases rw takeWhile\n'''
                '''def message := "induction suffices dropWhile"\n'''
                '''def chars := ['s', 'h']\n'''
                '''theorem real : True := by\n'''
                '''  have h : True := by simp\n'''
                '''  show True\n'''
                '''  exact h\n''')
        row = metrics.count_source("Test.lean", text)
        self.assertEqual(row["dashboard"]["proof_branching"], {
            "cases": 0, "by_cases": 0, "induction": 0,
        })
        self.assertEqual(row["dashboard"]["proof_plumbing"], {
            "have": 1, "show": 1, "suffices": 0, "rw": 0,
        })
        self.assertEqual(row["dashboard"]["automation"]["simp"], 1)
        self.assertEqual(row["dashboard"]["representation_detail"]["list_span"], 0)

    def test_exact_and_qualified_names(self):
        text = ('''theorem t : True := by\n'''
                '''  cases' h with x\n'''
                '''  rcases h with ⟨h, _⟩\n'''
                '''  have h' := List.Pairwise.sublist\n'''
                '''  have h'' := List.pairwise_append\n'''
                '''  have a := List.span p xs\n'''
                '''  have b := List . span p xs\n'''
                '''  have c := xs.getLast?\n'''
                '''  exact trivial\n''')
        row = metrics.count_source("Test.lean", text)
        self.assertEqual(row["dashboard"]["proof_branching"]["cases"], 0)
        detail = row["dashboard"]["representation_detail"]
        self.assertEqual(detail["pairwise_append"], 1)
        self.assertEqual(detail["Sublist"], 0)
        self.assertEqual(detail["list_span"], 2)
        self.assertEqual(detail["getLast?"], 1)

    def test_declaration_shape_and_privacy(self):
        text = ('''def a := 1\n'''
                '''abbrev A := Nat\n'''
                '''private lemma hidden : True := by trivial\n'''
                '''protected theorem visible : True := by trivial\n'''
                '''@[simp] private lemma attributed : True := by trivial\n'''
                '''noncomputable def choice : Nat := 0\n''')
        declarations = metrics.count_source("Test.lean", text)["dashboard"]["declarations"]
        self.assertEqual(declarations["definitions"], 2)
        self.assertEqual(declarations["abbreviations"], 1)
        self.assertEqual(declarations["lemmas"], 2)
        self.assertEqual(declarations["theorems"], 1)
        self.assertEqual(declarations["private_lemma_theorem_declarations"], 2)
        self.assertEqual(declarations["public_lemma_theorem_declarations"], 1)


if __name__ == "__main__":
    unittest.main()
