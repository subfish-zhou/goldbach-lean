"""Prepare reviewed private-proof deletions outside production; no Lean jobs."""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import re
import runpy

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/azureuser/goldbach-lean')
SOURCE = ROOT/'research/wu2008/src'
AUDIT = Path('/tmp/wu-next-private-prune-audit/opportunities.json')
AUDIT_SHA = '5009f198766b7513f42effdf55423f52d6ce886f60dabf27e2f74ee23b5d1e95'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
hs = lambda text: hashlib.sha256(text.encode()).hexdigest()
DOCS = {
    'vonMangoldt_zero': '/-- The von Mangoldt arithmetic function vanishes at zero. -/\n',
    'log_one_sub_prime_odd_bound': '/-- Local logarithmic correction for an odd prime p ≥ 3:\n|log(1 - 1/(p-1)) + 1/(p-1)| ≤ 2/(p-1)². -/\n',
}


def main():
    assert sha(AUDIT) == AUDIT_SHA
    audit = json.loads(AUDIT.read_text())
    assert len(audit['candidates']) == 22
    # Keep the reviewed entire4151-module lexical use universe unchanged.
    for name, digest in audit['source_bindings'].items():
        assert sha(Path(name)) == digest, name
    lexer = Path('/tmp/wu-structural-full-probe/lexical.py')
    code = runpy.run_path(str(lexer))['code_only']
    spec = importlib.util.spec_from_file_location('counter', ROOT/'scripts/check.py')
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    groups = {}
    for row in audit['candidates']:
        groups.setdefault(row['module'], []).append(row)
    assert len(groups) == 13
    files, diff = [], []
    totals = dict(effective_lines=0, physical_lines=0, bytes=0)
    for module, rows in sorted(groups.items()):
        relative = Path(*module.split('.')).with_suffix('.lean')
        path = SOURCE/relative
        original = path.read_text()
        masked = code(original, keep_strings=True)
        intervals = []
        for row in rows:
            assert sha(path) == row['source_sha256']
            start, limit = row['start_character'], row['provisional_end_character']
            assert hs(original[start:limit]) == row['provisional_fragment_sha256']
            # Exclude comments attached to the following declaration, including
            # its docstring. End at the final actual code character plus newline.
            end = start + len(masked[start:limit].rstrip())
            if original[end:end+1] == '\n': end += 1
            name = row['written_name']
            if name in DOCS:
                prefix = DOCS[name]
                assert original[start-len(prefix):start] == prefix
                start -= len(prefix)
            fragment = original[start:end]
            fragment_code = code(fragment)
            declarations = re.findall(r'^private\s+(?:theorem|lemma)\s+([^\s:]+)', fragment_code, re.M)
            assert declarations == [name]
            assert not re.search(r'^(?:attribute|instance|def|abbrev|structure|class|namespace|end)\b', fragment_code, re.M)
            intervals.append(dict(name=name, start=start, end=end, fragment=fragment,
                                  fragment_sha256=hs(fragment)))
        intervals.sort(key=lambda r: r['start'])
        assert all(a['end'] <= b['start'] for a,b in zip(intervals, intervals[1:]))
        new = original
        for row in reversed(intervals):
            new = new[:row['start']] + new[row['end']:]
        restored = new
        for row in intervals:
            restored = restored[:row['start']] + row['fragment'] + restored[row['start']:]
        assert restored == original
        new_tokens = re.findall(r"[A-Za-z_][\w']*", code(new, keep_strings=True))
        assert all(row['name'].split('.')[-1] not in new_tokens for row in intervals)
        removed = dict(effective_lines=counter.count_code_lines(original)-counter.count_code_lines(new),
                       physical_lines=len(original.splitlines())-len(new.splitlines()),
                       bytes=len(original.encode())-len(new.encode()))
        for k in totals: totals[k] += removed[k]
        output = HERE/'overlay'/relative
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(new)
        files.append(dict(module=module, file=str(relative), before_sha256=hs(original),
                          after_sha256=sha(output), deletions=intervals, predicted_removed=removed))
        diff.extend(difflib.unified_diff(original.splitlines(True), new.splitlines(True),
                    fromfile='before/'+str(relative), tofile='after/'+str(relative)))
    assert totals['effective_lines'] == 116
    manifest = dict(status='UNCOMPILED_DELETION_CANDIDATE_NOT_ADOPTED',
        Lean_executed=False, production_modified=False, audit_path=str(AUDIT), audit_sha256=AUDIT_SHA,
        files=files, declarations=22, modules=13, predicted_removed=totals,
        retained_source_characters_identical=True, exact_roundtrip_restoration=True,
        public_declarations_removed=0, definitions_or_numeric_values_modified=0,
        overlaps_active_v7_changed_modules=False,
        remaining='Actual source/module compilation, retained interfaces/registrations and downstream/full-project/kernel checks; include only after active pipeline clears, no restart of V7.')
    (HERE/'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False)+'\n')
    (HERE/'candidate.diff').write_text(''.join(diff))
    print(json.dumps(dict(manifest_sha256=sha(HERE/'manifest.json'), predicted_removed=totals,
                         modules=13, declarations=22, actual_Lean_validation=False)))


if __name__ == '__main__':
    main()
