"""Guards for independent proof verification and static documentation release."""
from pathlib import Path
import re
import unittest

WORKFLOW = Path(__file__).resolve().parents[1] / '.github/workflows/lean.yml'


def job(text, name):
    match = re.search(rf'^  {re.escape(name)}:\n(.*?)(?=^  [\w-]+:\n|\Z)', text, re.M | re.S)
    if match is None:
        raise AssertionError(f'missing job: {name}')
    return match[1]


class WorkflowBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.verify = job(self.text, 'verify')

    def test_full_source_build_is_not_skipped_on_cache_hit(self):
        self.assertIn('lake --wfail build', self.verify)
        conditions = re.findall(r'^\s+if:\s*(.+)$', self.verify, re.M)
        self.assertEqual(conditions, ['always()'])
        self.assertIn('python3 scripts/check.py', self.verify)
        self.assertIn('unittest discover', self.verify)

    def test_all_original_replay_targets_remain(self):
        actual = re.findall(r'lake env leanchecker --verbose (\S+)', self.verify)
        self.assertEqual(actual, ['Goldbach.Theorem', 'Goldbach.Checks',
                                 'Goldbach.OnePlusOneNine', 'Goldbach.OnePlusOneNineChecks',
                                 'Goldbach.All'])

    def test_proof_workflow_does_not_generate_or_deploy_pages(self):
        self.assertEqual(re.findall(r'^  ([\w-]+):$', self.text.split('jobs:', 1)[1], re.M), ['verify'])
        for token in ('scripts/build_docs.py', 'leanblueprint web', 'actions/deploy-pages',
                      'actions/upload-pages-artifact', 'needs: verify'):
            self.assertNotIn(token, self.text)

    def test_generated_branch_does_not_trigger_theorem_builds(self):
        self.assertIn('push:\n    branches-ignore: [gh-pages]', self.text)
        self.assertIn('  pull_request:', self.text)
        self.assertIn('  workflow_dispatch:', self.text)

    def test_only_compiler_cache_not_old_pages_is_restored(self):
        self.assertIn('path: .lake/build', self.verify)
        self.assertIn("hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')", self.verify)
        for path in ('docbuild/.lake/build/api', 'docbuild/.lake/build/site', 'blueprint/web'):
            self.assertNotIn(path, self.text)
        self.assertNotIn('lean-build.tar', self.text)

    def test_timing_pipeline_retains_bash_failure_semantics(self):
        self.assertIn('defaults:\n  run:\n    shell: bash\n', self.text)
        self.assertIn('/usr/bin/time -v lake --wfail build', self.verify)
        self.assertIn('permissions:\n  contents: read', self.text)
        self.assertNotIn('pages: write', self.text)
        self.assertIn('if: always()', self.verify)


if __name__ == '__main__':
    unittest.main()
