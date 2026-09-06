#!/usr/bin/env python3
"""Measure a clean project build with already prepared dependency caches.

Run from a fresh checkout after `lake exe cache get` and
`lake --wfail build Architect`. Project .olean files
must not exist. Dependency setup, documentation generation and proof replay
are outside the timed interval. No files are deleted by this script.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def source_fingerprint(root: Path) -> str:
    paths = list(root.glob('*.lean'))
    for name in ('Goldbach', 'MathlibNt', 'AnalyticNumberTheory', 'PrimeNumberTheoremAnd'):
        paths.extend((root / name).rglob('*.lean'))
    paths.extend(root / name for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(path.relative_to(root).as_posix().encode() + b'\0')
        digest.update(path.read_bytes() + b'\0')
    return digest.hexdigest()


def process_memory(root_pid: int) -> tuple[int, int, int, int]:
    parents = {}
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            parents[int(entry.name)] = int(stat[1])
        except (OSError, ValueError, IndexError):
            pass
    selected = {root_pid}
    while True:
        more = {pid for pid, parent in parents.items() if parent in selected}
        if more <= selected:
            break
        selected.update(more)
    rss = pss = failures = 0
    for pid in selected:
        try:
            fields = dict(line.split(':', 1) for line in
                          Path(f'/proc/{pid}/smaps_rollup').read_text().splitlines() if ':' in line)
            rss += int(fields['Rss'].split()[0]) * 1024
            pss += int(fields['Pss'].split()[0]) * 1024
        except (OSError, KeyError, ValueError):
            failures += 1
    return rss, pss, len(selected), failures


def uncached_dependency_builds(lines):
    libraries = {'Goldbach', 'MathlibNt', 'AnalyticNumberTheory', 'PrimeNumberTheoremAnd'}
    built = [match[1] for line in lines
             if (match := re.match(r'^\S+ \[[^\]]+\] Built ([^\s(]+)', line))]
    return sorted({name for name in built if name.split(':')[0].split('.')[0] not in libraries})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True,
                        help='new directory for build.log and result.json')
    args = parser.parse_args()
    if list((ROOT / '.lake/build').rglob('*.olean')):
        parser.error('project compiled modules already exist; use a fresh checkout')
    if not (ROOT / '.lake/packages').is_dir():
        parser.error('prepare the pinned dependency cache first')
    if not (ROOT / '.lake/packages/LeanArchitect/.lake/build/lib/lean/Architect.olean').is_file():
        parser.error('prepare the Blueprint dependency first: lake --wfail build Architect')
    if platform.system() != 'Linux':
        parser.error('the process-memory sampler requires Linux')
    args.output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'GIT_DIR', 'GIT_WORK_TREE'):
        env.pop(name, None)
    env['LEAN_NUM_THREADS'] = '2'
    env['GIT_TERMINAL_PROMPT'] = '0'
    lake = shutil.which('lake')
    if lake is None:
        parser.error('lake is not on PATH')
    command = [lake, '-Kjobs=8', '--wfail', 'build']
    cpu = next((line.split(':', 1)[1].strip() for line in
                Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), 'unknown')
    git = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, env=env,
                         text=True, capture_output=True)
    report = {
        'scope': 'Clean build of all four project libraries with cached pinned dependencies; excludes dependency acquisition, cache preparation, documentation and proof replay',
        'command': ['lake', '-Kjobs=8', '--wfail', 'build'],
        'LEAN_NUM_THREADS': '2', 'logical_cpus': os.cpu_count(),
        'cpu_model': cpu, 'machine': platform.machine(),
        'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'source_revision': git.stdout.strip() if git.returncode == 0 else None,
        'source_fingerprint_sha256': source_fingerprint(ROOT),
        'initial_load_average': os.getloadavg(),
        'status': 'running', 'started_unix': time.time(),
        'peak_sum_rss_bytes': 0, 'peak_sum_pss_bytes': 0,
        'peak_process_count': 0, 'samples': 0, 'pss_read_failures': 0,
        'sample_interval_seconds': 1,
        'memory_method': 'Approximately once per second, sum PSS/RSS for Lake and observed descendants. PSS apportions shared pages; RSS can double-count. Excludes filesystem cache and other jobs; sampled peaks are not minimum RAM requirements.',
    }
    result = args.output / 'result.json'
    start = time.monotonic()
    with (args.output / 'build.log').open('w') as log:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        while process.poll() is None:
            rss, pss, count, failures = process_memory(process.pid)
            report['peak_sum_rss_bytes'] = max(report['peak_sum_rss_bytes'], rss)
            report['peak_sum_pss_bytes'] = max(report['peak_sum_pss_bytes'], pss)
            report['peak_process_count'] = max(report['peak_process_count'], count)
            report['samples'] += 1
            report['pss_read_failures'] += failures
            report['elapsed_seconds'] = time.monotonic() - start
            if report['samples'] % 10 == 0:
                result.write_text(json.dumps(report, indent=2) + '\n')
            try:
                process.wait(timeout=1)
            except subprocess.TimeoutExpired:
                pass
    report['elapsed_seconds'] = time.monotonic() - start
    report['finished_unix'] = time.time()
    report['exit_code'] = process.returncode
    lines = (args.output / 'build.log').read_text().splitlines()
    report['warning_count'] = sum(line.startswith('warning:') for line in lines)
    report['success_line'] = next((line for line in reversed(lines)
                                   if 'Build completed successfully' in line), None)
    report['source_fingerprint_after_sha256'] = source_fingerprint(ROOT)
    report['source_unchanged'] = report['source_fingerprint_after_sha256'] == report['source_fingerprint_sha256']
    report['uncached_dependency_builds'] = uncached_dependency_builds(lines)
    report['status'] = 'passed' if process.returncode == 0 and report['success_line'] and not report['warning_count'] and report['source_unchanged'] and not report['uncached_dependency_builds'] else 'failed'
    report['final_load_average'] = os.getloadavg()
    result.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
