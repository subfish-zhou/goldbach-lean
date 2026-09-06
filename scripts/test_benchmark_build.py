"""Regression tests for the clean-build measurement boundary."""
import os
from pathlib import Path
import platform
import tempfile
import unittest

from benchmark_build import process_memory, source_fingerprint, uncached_dependency_builds


class BenchmarkTests(unittest.TestCase):
    def make_sources(self, root):
        for name in ('Goldbach', 'MathlibNt', 'AnalyticNumberTheory', 'PrimeNumberTheoremAnd'):
            (root / name).mkdir()
        (root / 'Goldbach/Statement.lean').write_text('-- fingerprint fixture\n')
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            (root / name).write_text(name + '\n')

    def test_uncached_dependencies_are_not_mistaken_for_project_builds(self):
        lines = ["✔ [1/4] Built Goldbach.Statement (1s)",
                 "ℹ [2/4] Built Mathlib.Data.Nat.Basic (1s)",
                 "✔ [3/4] Built Architect (1s)",
                 "✔ [4/4] Built MathlibNt.Check:olean (1s)"]
        self.assertEqual(uncached_dependency_builds(lines),
                         ["Architect", "Mathlib.Data.Nat.Basic"])

    def test_fingerprint_does_not_depend_on_checkout_path(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            left, right = Path(a), Path(b)
            self.make_sources(left)
            self.make_sources(right)
            self.assertEqual(source_fingerprint(left), source_fingerprint(right))

    def test_source_and_toolchain_changes_are_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_sources(root)
            original = source_fingerprint(root)
            (root / 'Goldbach/Statement.lean').write_text('-- changed fixture\n')
            changed = source_fingerprint(root)
            self.assertNotEqual(original, changed)
            (root / 'lean-toolchain').write_text('changed toolchain\n')
            self.assertNotEqual(changed, source_fingerprint(root))

    def test_report_updates_do_not_change_the_source_fingerprint(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_sources(root)
            original = source_fingerprint(root)
            (root / 'docs').mkdir()
            (root / 'docs/BUILD_BENCHMARK.md').write_text('measurement report\n')
            self.assertEqual(original, source_fingerprint(root))

    @unittest.skipUnless(platform.system() == 'Linux', 'Linux process sampler')
    def test_process_sampler_reads_the_current_process(self):
        rss, pss, processes, failures = process_memory(os.getpid())
        self.assertGreater(rss, 0)
        self.assertGreater(pss, 0)
        self.assertGreaterEqual(processes, 1)
        self.assertGreaterEqual(failures, 0)


if __name__ == '__main__':
    unittest.main()
