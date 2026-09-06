"""Regression tests for the source scanner and the axiom-report acceptance gate."""
import os
import unittest
from unittest.mock import patch

from check import EXPECTED, check_axiom_output, code_only, count_code_lines, lean_environment


class EnvironmentTests(unittest.TestCase):
    def test_ambient_lean_paths_do_not_override_the_project(self):
        with patch.dict(os.environ, {"LEAN_PATH": "foreign-artifacts",
                                     "LEAN_SRC_PATH": "foreign-sources",
                                     "GOLDBACH_TEST_KEEP": "preserved"}):
            env = lean_environment()
            self.assertNotIn("LEAN_PATH", env)
            self.assertNotIn("LEAN_SRC_PATH", env)
            self.assertEqual(env["GOLDBACH_TEST_KEEP"], "preserved")
            self.assertEqual(os.environ["LEAN_PATH"], "foreign-artifacts")


class SourceMaskTests(unittest.TestCase):
    def test_nested_comments(self):
        text = "theorem ok : True := by trivial /- sorry /- axiom -/ admit -/"
        result = code_only(text)
        self.assertIn("by trivial", result)
        self.assertNotIn("sorry", result)
        self.assertEqual(len(text), len(result))

    def test_line_comments_and_strings(self):
        text = 'def s := "sorry \\" /-" -- axiom\ntheorem bad := sorry\n'
        result = code_only(text)
        self.assertEqual(result.count("sorry"), 1)
        self.assertEqual(result.count("\n"), text.count("\n"))

    def test_code_survives(self):
        text = "axiom bad : False\nexample : False := by sorry\n"
        self.assertEqual(code_only(text), text)

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError):
            code_only("/- unfinished")


class CodeLineCountTests(unittest.TestCase):
    def test_comments_and_blank_lines(self):
        self.assertEqual(count_code_lines(
            "\n/- outer\n/- inner -/\n-/\n-- comment\ndef answer := 42 -- tail\n"), 1)

    def test_strings_are_code(self):
        self.assertEqual(count_code_lines('def text :=\n  "-- /- not a comment -/"\n'), 2)

    def test_escaped_quotes(self):
        self.assertEqual(count_code_lines('def text := "escaped \\" -- text" -- tail\n'), 1)

    def test_code_after_block_comment(self):
        self.assertEqual(count_code_lines('/- doc -/ theorem ok : True := by trivial\n'), 1)


class AxiomReportTests(unittest.TestCase):
    @staticmethod
    def reports(extra=""):
        names = ",\n Classical.choice, Quot.sound" + extra
        return "\n".join(f"'{name}' depends on axioms: [propext{names}]" for name in EXPECTED)

    def test_multiline_reports(self):
        check_axiom_output(self.reports())

    def test_missing_report_rejected(self):
        with self.assertRaises(RuntimeError):
            check_axiom_output("")

    def test_nonstandard_axiom_rejected(self):
        with self.assertRaises(RuntimeError):
            check_axiom_output(self.reports(", sorryAx"))

    def test_early_nonstandard_report_rejected(self):
        bad = "'Goldbach.chen_theorem' depends on axioms: [sorryAx]\n"
        with self.assertRaises(RuntimeError):
            check_axiom_output(bad + self.reports())

    def test_duplicate_report_rejected(self):
        duplicate = "'Goldbach.chen_theorem' depends on axioms: [propext]\n"
        with self.assertRaises(RuntimeError):
            check_axiom_output(duplicate + self.reports())

    def test_standard_subset_accepted(self):
        check_axiom_output("\n".join(
            f"'{name}' depends on axioms: [propext]" for name in EXPECTED))


if __name__ == "__main__":
    unittest.main()
