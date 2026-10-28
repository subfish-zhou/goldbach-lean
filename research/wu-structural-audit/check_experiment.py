"""Check the isolated Hf4 candidate against the accepted local import objects.

This does not install the candidate in the integrated Wu theorem.
Run the Wu full build and check_classical.py first.
"""
from pathlib import Path
import json
import os
import subprocess

HERE = Path(__file__).resolve().parent
WU = HERE.parent / 'wu2008'
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
plan = json.loads((WU / 'build/PLAN.json').read_text())
prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
    cwd=WU, env=env, text=True).strip()
env['LEAN_PATH'] = ':'.join([str(WU / 'build/lib'), *plan['package_paths']])
p = subprocess.run([prefix + '/bin/lean', '-j2', '-DwarningAsError=true',
    '-DautoImplicit=false', str(HERE / 'hf4/Hf4SeriesEnvelope.lean')],
    cwd=WU, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(HERE / 'hf4/build.log').write_text(p.stdout)
print(p.stdout, end='')
assert p.returncode == 0
assert 'sorryAx' not in p.stdout
assert p.stdout.count('depends on axioms: [propext, Classical.choice, Quot.sound]') == 4
