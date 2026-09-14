"""Structural regression checks for the verification/documentation boundary.

Actionlint checks YAML and Actions semantics separately. These small guards do
not execute GitHub Actions or claim a cold-build performance measurement.
"""
from pathlib import Path
import re
import unittest

WORKFLOW = Path(__file__).resolve().parents[1] / ".github/workflows/lean.yml"


def job(text, name):
    match = re.search(rf"^  {re.escape(name)}:\n(.*?)(?=^  [\w-]+:\n|\Z)",
                      text, re.M | re.S)
    if match is None:
        raise AssertionError(f"missing job: {name}")
    return match[1]


class WorkflowBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.verify = job(self.text, "verify")
        self.docs = job(self.text, "documentation")

    def test_full_source_build_is_not_skipped_on_cache_hit(self):
        self.assertIn("lake --wfail build", self.verify)
        # Cache-hit telemetry is allowed; conditional validation steps are not.
        conditions = re.findall(r"^\s+if:\s*(.+)$", self.verify, re.M)
        self.assertEqual(conditions, ["always()"])  # timing-log upload only
        self.assertIn("python3 scripts/check.py", self.verify)
        self.assertIn("unittest discover", self.verify)

    def test_all_original_replay_targets_remain(self):
        for module in ("Goldbach.Theorem", "Goldbach.Checks",
                       "Goldbach.OnePlusOneNine", "Goldbach.OnePlusOneNineChecks",
                       "Goldbach.All"):
            self.assertIn(f"lake env leanchecker --verbose {module}\n", self.verify)

    def test_documentation_has_own_budget_but_requires_verification(self):
        self.assertIn("    needs: verify\n", self.docs)
        self.assertIn("    timeout-minutes:", self.docs)
        self.assertNotIn("scripts/build_docs.py", self.verify)
        for command in ("scripts/build_docs.py", "scripts/verify_blueprint.py",
                        "scripts/build_site.py", "leanblueprint web"):
            self.assertIn(command, self.docs)
        self.assertNotIn("--module ", self.docs)

    def test_same_run_artifacts_and_revision_guard(self):
        self.assertIn("name: lean-build-${{ github.sha }}", self.verify)
        self.assertIn("name: lean-build-${{ github.sha }}", self.docs)
        self.assertNotIn("run-id:", self.docs)
        self.assertIn('test "$built_revision" = "$(git rev-parse HEAD)"', self.docs)
        self.assertIn('sha256sum --check "$RUNNER_TEMP/verified-build/build-config.sha256"', self.docs)
        self.assertIn('tar -xf "$RUNNER_TEMP/verified-build/lean-build.tar"', self.docs)

    def test_cache_does_not_restore_old_site(self):
        cache = self.docs.split("Restore documentation compiler cache", 1)[1]
        cache = cache.split("      - name:", 1)[0]
        self.assertIn("docbuild/lake-manifest.json", cache)
        self.assertIn("docbuild/*.lean", cache)
        for path in ("docbuild/.lake/build/api", "docbuild/.lake/build/site", "blueprint/web"):
            self.assertNotIn(path, cache)
        self.assertIn("hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')", self.verify)

    def test_deploy_requires_both_and_timed_pipelines_fail_closed(self):
        self.assertIn("needs: [verify, documentation]", job(self.text, "deploy"))
        self.assertIn("defaults:\n  run:\n    shell: bash\n", self.text)
        self.assertIn("/usr/bin/time -v lake --wfail build", self.verify)
        self.assertIn("/usr/bin/time -v python3 scripts/build_docs.py", self.docs)


if __name__ == "__main__":
    unittest.main()
