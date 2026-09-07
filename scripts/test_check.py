"""Regression tests for the source scanner and the axiom-report acceptance gate."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check
from check import (
    EXPECTED, ONE_NINE_EXPECTED, ONE_TWO_EXPECTED, check_axiom_output, code_only,
    count_code_lines, lean_environment, module_glob_matches, static_checks,
)


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

    def test_empty_axiom_cones_accepted(self):
        check_axiom_output("\n".join(
            f"'{name}' does not depend on any axioms" for name in EXPECTED))

    def test_duplicate_empty_report_rejected(self):
        duplicate = "'Goldbach.one_plus_one_nine' does not depend on any axioms\n"
        with self.assertRaisesRegex(RuntimeError, "duplicate"):
            check_axiom_output(self.reports() + "\n" + duplicate)

    def test_old_reports_do_not_cover_new_theorems(self):
        old = "\n".join(f"'{name}' depends on axioms: [propext]" for name in ONE_TWO_EXPECTED)
        check_axiom_output(old, ONE_TWO_EXPECTED)
        with self.assertRaisesRegex(RuntimeError, "missing axiom reports"):
            check_axiom_output(old)

    def test_new_theorems_are_individually_required(self):
        for missing in ONE_NINE_EXPECTED:
            with self.subTest(missing=missing):
                reports = "\n".join(f"'{name}' depends on axioms: [propext]"
                                    for name in EXPECTED - {missing})
                with self.assertRaisesRegex(RuntimeError, missing):
                    check_axiom_output(reports)

    def test_new_nonstandard_axiom_rejected(self):
        bad = "'Goldbach.one_plus_one_nine' depends on axioms: [customAxiom]\n"
        with self.assertRaisesRegex(RuntimeError, "nonstandard axioms"):
            check_axiom_output(bad + self.reports())

    def test_malformed_report_rejected(self):
        reports = self.reports().replace("depends on axioms:", "depends on unknown axioms:", 1)
        with self.assertRaisesRegex(RuntimeError, "missing axiom reports"):
            check_axiom_output(reports)


class LibraryCoverageTests(unittest.TestCase):
    def setUp(self):
        # Use the real project manifest, with small source-only regression fixtures.
        lakefile = (check.ROOT / "lakefile.toml").read_text(encoding="utf-8")
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.write("lakefile.toml", lakefile)
        for name in ("Goldbach", "MathlibNt", "AnalyticNumberTheory"):
            self.write(name + ".lean", "-- independent entrypoint\n")
        root_patch = patch.object(check, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    def scan(self, issue=None):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            if issue is None:
                return static_checks()
            with self.assertRaises(RuntimeError):
                static_checks()
        result = json.loads(output.getvalue())
        self.assertTrue(any(issue in item for item in result["issues"]), result)
        return result

    def test_lake_glob_semantics(self):
        self.assertTrue(module_glob_matches("Goldbach", "Goldbach"))
        self.assertFalse(module_glob_matches("Goldbach.Helper", "Goldbach"))
        self.assertFalse(module_glob_matches("Goldbach", "Goldbach.+"))
        self.assertTrue(module_glob_matches("Goldbach.Audit.Deep", "Goldbach.+"))
        self.assertFalse(module_glob_matches("GoldbachExtra.Audit", "Goldbach.+"))
        self.assertTrue(module_glob_matches("Goldbach", "Goldbach.*"))

    def test_library_helpers_are_covered_but_not_in_entrypoint_closure(self):
        for module in ("Goldbach/Audit", "MathlibNt/Helper", "PrimeNumberTheoremAnd/Helper"):
            self.write(module + ".lean", "-- independently built module\n")
        result = self.scan()
        self.assertEqual(result["source_modules"], result["default_build_modules"])
        self.assertEqual(result["library_only_modules"], 3)
        self.assertEqual(result["reachable_modules"], 3)
        self.assertEqual(result["entrypoint_closures"]["Goldbach"], 1)
        self.assertEqual(set(result["default_libraries"]), set(check.SOURCE_DIRS))

    def test_new_entrypoint_does_not_inflate_old_closure(self):
        self.write("Goldbach/OnePlusOneNine.lean", "import MathlibNt.Helper\n")
        self.write("Goldbach/OnePlusOneNineChecks.lean", "import Goldbach.OnePlusOneNine\n")
        self.write("MathlibNt/Helper.lean", "-- helper\n")
        closures = self.scan()["entrypoint_closures"]
        self.assertEqual(closures["Goldbach"], 1)
        self.assertEqual(closures["Goldbach.OnePlusOneNine"], 2)
        self.assertEqual(closures["Goldbach.OnePlusOneNineChecks"], 3)

    def test_library_only_missing_import_rejected(self):
        self.write("Goldbach/Audit.lean", "public import MathlibNt.Missing\n")
        self.scan("missing local module: Goldbach.Audit -> MathlibNt.Missing")

    def test_library_only_cycle_rejected(self):
        self.write("Goldbach/Audit.lean", "import Goldbach.Helper\n")
        self.write("Goldbach/Helper.lean", "import Goldbach.Audit\n")
        self.scan("import cycle")

    def test_unconfigured_root_rejected(self):
        self.write("UnbuiltAudit.lean", "-- outside all configured globs\n")
        self.scan("outside default library build coverage")

    def test_default_build_includes_local_imports_outside_globs(self):
        self.write("Goldbach/Audit.lean", "import RootHelper\n")
        self.write("RootHelper.lean", "-- built as a dependency, not a glob match\n")
        result = self.scan()
        self.assertEqual(result["default_build_modules"], result["source_modules"])
        self.assertEqual(result["default_library_glob_modules"] + 1, result["default_build_modules"])

    def test_nondefault_library_does_not_supply_build_coverage(self):
        manifest = self.root / "lakefile.toml"
        manifest.write_text(manifest.read_text().replace(
            'defaultTargets = ["Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd"]',
            'defaultTargets = ["Goldbach", "MathlibNt", "AnalyticNumberTheory"]'), encoding="utf-8")
        self.write("PrimeNumberTheoremAnd/Helper.lean", "-- not built by a default target\n")
        self.scan("outside default library build coverage")

    def test_missing_explicit_library_root_rejected(self):
        (self.root / "Goldbach.lean").unlink()
        with self.assertRaisesRegex(ValueError, "missing library glob module: Goldbach"):
            self.scan()

    def test_prohibited_tokens_in_library_only_modules_rejected(self):
        for token in ("sorry", "admit", "axiom", "native_decide", "unsafe", "debug.skipKernelTC"):
            with self.subTest(token=token):
                self.write("Goldbach/Audit.lean", token + "\n")
                self.scan("prohibited token " + token)

    def test_release_private_path_rejected(self):
        self.write("README.md", "/" + "home/worker/private-project\n")
        self.scan("private machine path")

    def test_worktree_git_pointer_is_not_release_content(self):
        self.write(".git", "gitdir: /" + "home/worker/repository/.git/worktrees/release\n")
        self.scan()

    def test_compiler_internal_name_rejected(self):
        self.write("Goldbach/Audit.lean", "#check " + "_private" + ".Hidden.0.lemma\n")
        self.scan("compiler-internal declaration name")

    def test_untranslated_release_text_rejected(self):
        self.write("README.md", "\u4e2d\u6587\n")
        self.scan("untranslated CJK text")


class CommandTests(unittest.TestCase):
    @staticmethod
    def lean_result(command, **kwargs):
        expected = (ONE_TWO_EXPECTED if command[-1] == "Goldbach/Checks.lean"
                    else ONE_NINE_EXPECTED)
        text = "\n".join(f"'{name}' depends on axioms: [propext]" for name in expected)
        return subprocess.CompletedProcess(command, 0, text)

    def run_main(self, args=(), *, side_effect=None):
        with patch("sys.argv", ["check.py", *args]), patch.object(check, "static_checks") as scan, \
                patch.object(check.subprocess, "run", side_effect=side_effect or self.lean_result) as run, \
                contextlib.redirect_stdout(io.StringIO()):
            status = check.main()
        scan.assert_called_once_with()
        return status, run

    def test_default_runs_both_strict_probes(self):
        status, run = self.run_main()
        self.assertEqual(status, 0)
        self.assertEqual([call.args[0][-1] for call in run.call_args_list],
                         ["Goldbach/Checks.lean", "Goldbach/OnePlusOneNineChecks.lean"])
        for call in run.call_args_list:
            self.assertEqual(call.args[0][:-1], ["lake", "env", "lean", "-DwarningAsError=true"])
            self.assertEqual(call.kwargs["cwd"], check.ROOT)

    def test_one_two_only_runs_old_probe(self):
        status, run = self.run_main(["--one-two-only"])
        self.assertEqual(status, 0)
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0][-1], "Goldbach/Checks.lean")

    def test_static_only_never_runs_lean(self):
        for args in (["--static-only"], ["--static-only", "--one-two-only"]):
            status, run = self.run_main(args)
            self.assertEqual(status, 0)
            run.assert_not_called()

    def test_lean_failure_propagates(self):
        status, run = self.run_main(side_effect=[subprocess.CompletedProcess([], 7, "failed")])
        self.assertEqual(status, 7)
        run.assert_called_once()

    def test_second_probe_failure_propagates(self):
        good = self.lean_result(["Goldbach/Checks.lean"])
        status, run = self.run_main(side_effect=[good, subprocess.CompletedProcess([], 9, "failed")])
        self.assertEqual(status, 9)
        self.assertEqual(run.call_count, 2)

    def test_new_probe_cannot_replay_only_old_reports(self):
        old = self.lean_result(["Goldbach/Checks.lean"])
        with self.assertRaisesRegex(RuntimeError, "missing axiom reports"):
            self.run_main(side_effect=[old, old])

    def test_duplicate_across_probes_rejected(self):
        old = self.lean_result(["Goldbach/Checks.lean"])
        new = self.lean_result(["Goldbach/OnePlusOneNineChecks.lean"])
        new.stdout += "\n'Goldbach.chen_theorem' depends on axioms: [propext]"
        with self.assertRaisesRegex(RuntimeError, "duplicate"):
            self.run_main(side_effect=[old, new])


if __name__ == "__main__":
    unittest.main()
