import json
import tempfile
import unittest
from pathlib import Path

from check_palomar_sources import inspect_tree


class PalomarSourceRequirements(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Palomar").mkdir()
        (self.root / "Palomar/comparator.json").write_text(json.dumps({
            "challenge_module": "Palomar.Challenge", "solution_module": "Palomar.Solution"}))
        (self.root / "Palomar/Challenge.lean").write_text("module\npublic theorem claim : True := by sorry\n")
        (self.root / "Palomar/Solution.lean").write_text("module\npublic theorem claim : True := True.intro\n")

    def test_comment_mentioning_module_does_not_supply_a_header(self):
        (self.root / "Legacy.lean").write_text("/-! module describes this example -/\nimport Init\n")
        self.assertIn("Source needs a module header: Legacy.lean", inspect_tree(self.root)["issues"])

    def test_leading_copyright_comment_is_allowed(self):
        (self.root / "Example.lean").write_text("/- Copyright notice -/\nmodule\n")
        self.assertEqual(inspect_tree(self.root)["issues"], [])

    def test_unused_sources_still_have_the_line_limit(self):
        (self.root / "Unused.lean").write_text("module\n" + "-- comment\n" * 10_000)
        self.assertIn("Source exceeds 10000 physical lines: Unused.lean", inspect_tree(self.root)["issues"])

    def test_build_named_directories_receive_source_checks(self):
        (self.root / ".build").mkdir()
        (self.root / ".build/Legacy.lean").write_text("import Init\n")
        self.assertIn("Source needs a module header: .build/Legacy.lean", inspect_tree(self.root)["issues"])

    def test_challenge_holes_are_isolated_from_solution(self):
        solution = self.root / "Palomar/Solution.lean"
        solution.write_text("module\npublic theorem claim : True := by sorry\n")
        self.assertIn("Prohibited Solution token: sorry", inspect_tree(self.root)["issues"])

    def test_broken_lean_symlinks_are_rejected(self):
        (self.root / "Hidden.lean").symlink_to("missing-source")
        self.assertIn("Lean source is a symbolic link: Hidden.lean", inspect_tree(self.root)["issues"])

    def test_missing_solution_is_reported(self):
        (self.root / "Palomar/Solution.lean").unlink()
        self.assertTrue(any(issue.startswith("Invalid Comparator sources:")
                            for issue in inspect_tree(self.root)["issues"]))

    def test_module_paths_cannot_escape_the_publication(self):
        config = self.root / "Palomar/comparator.json"
        config.write_text(json.dumps({"challenge_module": "../Other",
                                      "solution_module": "Palomar.Solution"}))
        self.assertTrue(any("safe dotted Lean names" in issue
                            for issue in inspect_tree(self.root)["issues"]))


if __name__ == "__main__":
    unittest.main()
