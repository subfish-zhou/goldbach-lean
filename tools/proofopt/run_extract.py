#!/usr/bin/env python3
"""Execute the pinned extractor and seal successful, input-bound JSONL output."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import re
import time
from index import digest, file_digest, manifest_key, seal_records, validate_manifest


def check_module_receipts(raw, stderr, requested):
    actual = dict.fromkeys(requested, 0)
    for line in raw.splitlines():
        row = json.loads(line)
        if row['module'] not in actual:
            raise ValueError('unexpected extractor module')
        actual[row['module']] += 1
    emitted = {}
    for name, count in re.findall(r'^module=(\S+) declarations=(\d+) parts=', stderr, re.M):
        if name in emitted:
            raise ValueError('duplicate module completion receipt')
        emitted[name] = int(count)
    if emitted != actual:
        raise ValueError('missing module receipt or truncated declaration payload')


def extract(manifest_path, lean, lean_path, output, timeout=600, modules=None):
    manifest = json.loads(manifest_path.read_bytes())
    requested = [m for m in manifest['modules'] if modules is None or m['module'] in modules]
    if modules is not None and {m['module'] for m in requested} != set(modules):
        raise ValueError('requested module absent from manifest')
    if not requested:
        raise ValueError('empty requested module set')
    if output.exists():
        raise FileExistsError(output)
    tool = Path(__file__).with_name('Extract.lean').resolve()
    tool_hash = file_digest(tool)
    subset = dict(manifest, modules=requested)
    validate_manifest(subset)
    tsv = output.with_suffix('.inputs.tsv')
    raw = output.with_suffix('.raw.jsonl')
    log = output.with_suffix('.stderr.log')
    receipt = output.with_suffix('.run.json')
    for path in (tsv, raw, log, receipt):
        if path.exists():
            raise FileExistsError(path)
    tsv.write_text(''.join(m['module']+'\t'+m['object']+'\n' for m in requested))
    env = os.environ.copy()
    for key in tuple(env):
        if key in ('GIT_DIR','GIT_WORK_TREE','LEAN_SYSROOT') or key.endswith(('_LEDGER_GIT_DIR','_LEDGER_WORK_TREE')):
            env.pop(key,None)
    env.update(LEAN_PATH=lean_path, LEAN_NUM_THREADS='2')
    command = [str(lean), '--run', str(tool), '--manifest', str(tsv)]
    started = time.monotonic()
    record = {'command': command, 'manifest_sha256': manifest_key(manifest),
              'extractor_sha256': tool_hash, 'requested_modules': [m['module'] for m in requested],
              'status': 'running'}
    receipt.write_text(json.dumps(record, indent=2)+'\n')
    try:
        with raw.open('xb') as stdout, log.open('xb') as stderr:
            result = subprocess.run(command, cwd=tool.parent, env=env, stdout=stdout, stderr=stderr, timeout=timeout)
        record['exit_code'] = result.returncode
        if result.returncode:
            raise RuntimeError(f'extractor failed, exit {result.returncode}; see {log}')
        validate_manifest(subset)
        if file_digest(tool) != tool_hash:
            raise ValueError('extractor source changed during run')
        raw_bytes = raw.read_bytes()
        check_module_receipts(raw_bytes, log.read_text(), record['requested_modules'])
        sealed = seal_records(manifest, raw_bytes, record['requested_modules'], tool_hash)
        with output.open('xb') as f:
            f.write(sealed)
        record.update(status='sealed', output_sha256=digest(sealed))
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        record['elapsed_seconds'] = time.monotonic()-started
        receipt.write_text(json.dumps(record, indent=2)+'\n')
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--lean-path', required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--timeout', type=int, default=600)
    p.add_argument('--modules', nargs='+')
    a = p.parse_args()
    record = extract(a.manifest,a.lean,a.lean_path,a.output,a.timeout,a.modules)
    print(json.dumps({k:v for k,v in record.items() if k not in ('requested_modules','command')}))


if __name__ == '__main__':
    main()
