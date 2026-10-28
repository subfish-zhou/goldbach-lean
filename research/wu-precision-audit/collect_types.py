"""Collect compiled declaration signatures from a fully verified Wu source tree.

Use separate output directories named baseline and current for compare_types.py.
The baseline must be built from the baseline revision before collecting it.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('wu_directory', type=Path)
parser.add_argument('output_directory', type=Path)
args = parser.parse_args()
wu = args.wu_directory.resolve()
out = args.output_directory.resolve()
root = Path(__file__).resolve().parents[2]
status = json.loads((wu / 'build/STATUS.json').read_text())
assert status['status'] == 'passed', status
manifest = json.loads((wu / 'source-manifest.json').read_text())
assert status['verified'] == status['planned'] == len(manifest)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = []
modules = sorted('src/' + row['module'].replace('.', '/') + '.lean' for row in manifest)
by_module = {row['module']: row for row in manifest}
(out / 'types').mkdir(parents=True, exist_ok=True)
for i, source in enumerate(modules):
    module = source[4:-5].replace('/', '.')
    relative = Path(source).relative_to('src')
    obj = (wu / 'build/lib' / relative).with_suffix('.olean')
    receipt = json.loads((wu / 'build/receipts' / relative).with_suffix('.json').read_text())
    assert sha(wu / source) == by_module[module]['source_sha256'] == receipt['source_sha256']
    assert receipt['exit_code'] == 0 and sha(obj) == receipt['object_sha256']
    rows.append(f'{wu / source}\t{obj}\t{out / "types" / f"{i}.json"}')
(out / 'type-manifest.tsv').write_text('\n'.join(rows) + '\n')
(out / 'type-modules.json').write_text(json.dumps(modules))
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
with (out / 'type-extraction.log').open('w') as log:
    subprocess.run(['lake', 'env', 'lean', '--run',
                    str(root / 'research/chen-audit/TypeCensus.lean'),
                    str(out / 'type-manifest.tsv')], cwd=wu, env=env,
                   stdout=log, stderr=subprocess.STDOUT, check=True)
print('TYPE_CENSUS_PASS', len(modules))
