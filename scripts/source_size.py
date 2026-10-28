#!/usr/bin/env python3
"""Measure local theorem import closures and complete source-tree changes.

Print JSON to stdout; sources and the checked-in report are never changed.
"""
from pathlib import Path
import argparse, subprocess, importlib.util, json, re, hashlib, datetime

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('release_checks', ROOT / 'scripts/check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', default='c4e1b8d00dda9661140f95e0f03f0d5a08d636c2',
                    help='Git revision used for the complete before/after source comparison.')
args = parser.parse_args()
BASE = subprocess.check_output(['git', 'rev-parse', args.baseline], cwd=ROOT, text=True).strip()
IMPORT = re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)', re.M)

def measure(raw):
    text = raw.decode('utf-8')
    masked = checks.code_only(text, keep_strings=True)
    imports = []
    for match in IMPORT.finditer(checks.code_only(text)):
        imports.extend(match.group(1).split())
    return {'physical_lines': len(text.splitlines()),
            'code_lines': sum(bool(line.strip()) for line in masked.splitlines()),
            'utf8_bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
            'imports': imports}

def mod(path):
    return str(Path(path).with_suffix('')).replace('/', '.')

current = {mod(p.relative_to(ROOT)): measure(p.read_bytes()) for p in checks.source_files()}
entries = subprocess.check_output(['git','ls-tree','-r','-z',BASE],cwd=ROOT).split(b'\0')
selected = []
for row in entries:
    if not row: continue
    meta, name = row.split(b'\t',1)
    p = Path(name.decode())
    if p.suffix == '.lean' and (len(p.parts)==1 or p.parts[0] in checks.SOURCE_DIRS):
        selected.append((str(p), meta.split()[2].decode()))
proc = subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
baseline = {}
for p, oid in selected:
    proc.stdin.write((oid+'\n').encode()); proc.stdin.flush()
    header = proc.stdout.readline().split()
    raw = proc.stdout.read(int(header[2])); assert proc.stdout.read(1)==b'\n'
    baseline[mod(p)] = measure(raw)
proc.stdin.close(); assert proc.wait()==0
manifest = json.loads((ROOT/'research/wu2008/source-manifest.json').read_text())
research = {}
for row in manifest:
    name = row['module']
    p = (ROOT/'research/wu2008/src'/Path(*name.split('.'))).with_suffix('.lean')
    raw = p.read_bytes(); assert hashlib.sha256(raw).hexdigest()==row['source_sha256'],p
    research[name] = measure(raw)

def closure(data, root):
    seen = set(); pending = [root]
    while pending:
        n = pending.pop()
        if n in seen or n not in data: continue
        seen.add(n); pending.extend(data[n]['imports'])
    return seen

def summarize(data, names):
    return {'modules':len(names), **{k:sum(data[n][k] for n in names) for k in ['physical_lines','code_lines','utf8_bytes']}}

def difference(a,b):
    return {k:b[k]-a[k] for k in a}

roots = [('1+2','Goldbach.Theorem'),('1+1.9','Goldbach.OnePlusOneNine')]
results = {}
for label, entry in roots:
    results[label] = {'root':entry,'baseline':summarize(baseline,closure(baseline,entry)),
                      'current':summarize(current,closure(current,entry))}
results['1+1.894'] = {'root':'WR2ClassicalCertificate','current':summarize(research,closure(research,'WR2ClassicalCertificate'))}
changed = {n for n in baseline.keys() & current.keys() if baseline[n]['sha256']!=current[n]['sha256']}
added = current.keys()-baseline.keys(); deleted = baseline.keys()-current.keys()
before = summarize(baseline,changed|deleted); after = summarize(current,changed|added)
file_changes = []
for n in sorted(changed|added|deleted):
    b = summarize(baseline,{n} if n in baseline else set())
    a = summarize(current,{n} if n in current else set())
    file_changes.append({'module':n,'status':'new' if n in added else 'deleted' if n in deleted else 'modified','baseline':b,'current':a,'delta':difference(b,a)})
report = {'measured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'baseline_commit':BASE,
 'method':{'scope':'Complete transitive local module import closure, including the selected entry module. Each module counted once per closure. Mathlib and other external Lake dependencies excluded. Shared dependencies are counted in each separate theorem closure.',
           'code_lines':'Nonblank lines after masking Lean nested block comments and line comments; strings retained. Includes definitions, theorem statements, proofs, imports, and commands. This is source size, not minimal declaration-level proof size.',
           'physical_lines':'All text lines, including blank lines and comments; terminal line without newline also counted.',
           'baseline_scope':'The complete baseline source snapshot is compared with the working tree, counting all additions, deletions and moved code. Historical import closures are source measurements; the selected default baseline was independently accepted before cleanup.'},
 'theorems':results,
 'working_tree_changes_vs_baseline':{'modified_existing_modules':len(changed),'added_modules':len(added),'deleted_modules':len(deleted),'affected_before':before,'affected_after':after,'net_delta':difference(before,after),'files':file_changes},
 'whole_trees':{'baseline_main':summarize(baseline,set(baseline)),'current_main':summarize(current,set(current)),'current_research':summarize(research,set(research))}}
print(json.dumps(report, ensure_ascii=False, indent=2))
