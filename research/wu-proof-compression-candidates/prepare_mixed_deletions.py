#!/usr/bin/env python3
"""Prepare reversible deletions after both compiled and source reference closure.

This writes an isolated overlay only. It neither compiles nor adopts the edits.
All declaration ranges come from the actual compiler query, not lexical spans.
"""

import argparse
import bisect
import collections
import difflib
import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def words(text):
    return set(re.findall(r"[A-Za-z_][\w']*", text))


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ranges-dir', type=Path, required=True)
    parser.add_argument('--census-dir', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    output = args.output_dir.resolve()
    assert not output.exists()
    range_dir, census_dir = args.ranges_dir.resolve(), args.census_dir.resolve()
    rp = json.loads((range_dir / 'plan.json').read_text())
    rr = json.loads((range_dir / 'execution-result.json').read_text())
    assert rr['status'] == 'ACTUAL_COMPILER_ROOT_AND_FAMILY_RANGES_PASS_NOT_SOURCE_RETIREMENT_OR_ACCEPTANCE'
    assert rr['exit_code'] == 0 and sha(range_dir / 'ranges.json') == rr['payload_sha256']
    cr = json.loads((census_dir / 'execution-result.json').read_text())
    assert cr['status'] == 'ACTUAL_MIXED_KIND_FAMILY_CENSUS_PASS_NOT_SOURCE_RETIREMENT_OR_ACCEPTANCE'
    assert cr['exit_code'] == 0 and cr['context_digest'] == rr['context_digest']
    assert sha(census_dir / 'census.json') == cr['payload_sha256']
    assert sha(census_dir / 'family-selection.json') == cr['selection_sha256']
    census = json.loads((census_dir / 'census.json').read_text())
    selection = json.loads((census_dir / 'family-selection.json').read_text())
    cp = json.loads((census_dir / 'plan.json').read_text())
    model_path = Path(cp['opportunities'])
    model = json.loads(model_path.read_text())
    run = Path(rp['run'])
    assert sha(run / 'source-manifest.json') == model['source_manifest_sha256']
    manifest = {r['module']: r for r in json.loads((run / 'source-manifest.json').read_text())}
    targets = {r['basename']: r for r in census['candidates']}
    by_name = {r['name']: r['basename'] for r in census['candidates']}
    records = {r['written_name'].split('.')[-1]: r for r in model['candidates']}
    ranges = {r['basename']: r for r in json.loads((range_dir / 'ranges.json').read_text())['roots']}
    assert len(targets) == len(records) == len(ranges) == census['candidateCount']
    assert targets.keys() == records.keys() == ranges.keys()
    spec = importlib.util.spec_from_file_location('published_counter', repo / 'scripts/check.py')
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    bindings = {str(p): sha(p) for p in [Path(__file__).resolve(), repo / 'scripts/check.py', model_path, run / 'source-manifest.json']}
    for directory, names in [(range_dir, ['ranges.json', 'execution-result.json', 'plan.json']), (census_dir, ['census.json', 'family-selection.json', 'execution-result.json', 'plan.json'])]:
        bindings.update({str(directory / n): sha(directory / n) for n in names})
    groups = collections.defaultdict(list)
    for base, row in records.items():
        groups[row['module']].append(base)
    reasons = collections.defaultdict(list)
    for row in selection['retained']:
        reasons[row['basename']].extend(row['reasons'])
    all_bases = set(targets)
    adjacency = collections.defaultdict(set)
    for edge in census['edges']:
        if edge['userFamily'] is not None:
            adjacency[by_name[edge['userFamily']]].add(by_name[edge['target']])
    texts, intervals = {}, {}
    for module, row in manifest.items():
        path = run / 'src' / Path(*module.split('.')).with_suffix('.lean')
        assert sha(path) == row['source_sha256'], module
        text = texts[module] = path.read_text()
        assert text.encode() == path.read_bytes()
        masked = counter.code_only(text)
        starts = [m.start() for m in re.finditer(r'^\S', masked, re.M)]
        lines = text.splitlines(keepends=True)
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line))

        def at(pos, which):
            line, column = pos[which + 'Line'], pos[which + 'Column']
            assert 1 <= line <= len(lines) and 0 <= column <= len(lines[line - 1].rstrip('\n'))
            return offsets[line - 1] + column

        rows = []
        for base in groups[module]:
            source, r, target = records[base], ranges[base], targets[base]
            assert r['name'] == target['name'] and r['module'] == module
            assert source['original_source_sha256'] == row['source_sha256']
            start, end = at(r['range'], 'start'), at(r['range'], 'end')
            ss, ee = at(r['selectionRange'], 'start'), at(r['selectionRange'], 'end')
            assert start <= ss < ee <= end and text[ss:ee] == source['written_name'], base
            declaration_line = offsets[source['original_line'] - 1]
            assert start <= declaration_line <= ss, base
            prefix = source['preceding_scoped_directive']
            if prefix:
                index = bisect.bisect_left(starts, declaration_line)
                assert index > 0
                previous = starts[index - 1]
                assert masked[previous:declaration_line].strip() == prefix, base
                assert re.fullmatch(r'(?:set_option|omit|include|open)\b[\s\S]*\bin', prefix), base
                start = min(start, previous)
            newline = text.find('\n', end)
            newline = len(text) if newline < 0 else newline
            tail = text[end:newline]
            if not tail.strip() or tail.lstrip().startswith('--'):
                end = newline + (newline < len(text))
            fragment = text[start:end]
            fc = counter.code_only(fragment)
            declarations = re.findall(r"^(?:(?:private|protected|public|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w.']*)", fc, re.M)
            assert declarations == [source['written_name']], (base, declarations)
            if '@[' in fc:
                reasons[base].append('attribute syntax requires separate registration review')
            assert not re.search(r'^(?:attribute|instance|structure|class|namespace|end|axiom)\b', fc, re.M), base
            assert r['docString'] is None or '/--' in fragment, base
            item = dict(basename=base, runtime_name=r['name'], written_name=source['written_name'], kind=target['kind'], visibility=source['visibility'], start_character=start, end_character=end, fragment=fragment, fragment_sha256=digest(fragment), compiler_range=r['range'], selection_range=r['selectionRange'], scoped_prefix=prefix, has_compiled_docstring=r['docString'] is not None)
            rows.append(item)
            adjacency[base].update(words(counter.code_only(fragment, keep_strings=True)) & all_bases)
        rows.sort(key=lambda r: r['start_character'])
        assert all(a['end_character'] <= b['start_character'] for a, b in zip(rows, rows[1:])), module
        intervals[module] = rows
        outside = text
        for item in reversed(rows):
            outside = outside[:item['start_character']] + outside[item['end_character']:]
        for base in words(counter.code_only(outside, keep_strings=True)) & all_bases:
            reasons[base].append('reference in retained source outside all candidate ranges: ' + module)
    # Current consumers are read afresh; historical evidence is excluded explicitly.
    archival = [repo / 'research/wu2008/history', repo / 'research/wu-hf4-constructive-wip', repo / 'research/wu-hf4-constructive-audit/isolated']
    exclusions = []
    consumers = []
    for relative in subprocess.check_output(['rg', '--files', '-g', '*.md', '-g', '*.py', '-g', '*.lean'], cwd=repo, text=True).splitlines():
        path = repo / relative
        if path.is_relative_to(repo / 'research/wu2008/src'):
            continue
        if any(path.is_relative_to(root) for root in archival):
            exclusions.append(dict(path=relative, sha256=sha(path)))
            continue
        bindings[str(path)] = sha(path)
        consumers.append(relative)
        for base in words(path.read_text()) & all_bases:
            reasons[base].append('reference in current consumer: ' + relative)
    retained = set(reasons)
    todo = list(retained)
    while todo:
        user = todo.pop()
        for target in adjacency[user] - retained:
            reasons[target].append('required in source or compiled family of retained candidate: ' + user)
            retained.add(target)
            todo.append(target)
    selected = all_bases - retained
    assert selected <= {r['basename'] for r in selection['selected']}
    for edge in census['edges']:
        if by_name[edge['target']] in selected:
            assert edge['userFamily'] is not None and by_name[edge['userFamily']] in selected
    output.mkdir(parents=True)
    files, patch = [], []
    totals = collections.Counter()
    for module, text in texts.items():
        removals = [r for r in intervals[module] if r['basename'] in selected]
        after = text
        for item in reversed(removals):
            after = after[:item['start_character']] + after[item['end_character']:]
        assert not (words(counter.code_only(after, keep_strings=True)) & selected), module
        if not removals:
            continue
        restored = after
        for item in removals:
            restored = restored[:item['start_character']] + item['fragment'] + restored[item['start_character']:]
        assert restored == text, module
        delta = dict(code_lines=counter.count_code_lines(text) - counter.count_code_lines(after), physical_lines=len(text.splitlines()) - len(after.splitlines()), utf8_bytes=len(text.encode()) - len(after.encode()))
        totals.update(delta)
        relative = Path(*module.split('.')).with_suffix('.lean')
        destination = output / 'overlay' / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(after)
        files.append(dict(module=module, file=str(relative), before_sha256=digest(text), after_sha256=digest(after), deletions=removals, predicted_removed=delta))
        patch.extend(difflib.unified_diff(text.splitlines(keepends=True), after.splitlines(keepends=True), fromfile='before/' + str(relative), tofile='after/' + str(relative)))
    result = dict(status='SOURCE_AND_COMPILED_REFERENCE_CLOSED_EXACT_OVERLAY_UNCOMPILED_NOT_ADOPTED', baseline_run=str(run), context_digest=rr['context_digest'], bindings=bindings, selected_declarations=len(selected), selected_kinds=dict(collections.Counter(targets[b]['kind'] for b in selected)), retained=[dict(**targets[b], reasons=sorted(set(reasons[b]))) for b in sorted(retained)], modules=len(files), predicted_removed=dict(totals), exact_roundtrip=True, untouched_characters_identical=True, current_consumers=consumers, archival_exclusions=exclusions, files=files)
    save(output / 'manifest.json', result)
    (output / 'candidate.diff').write_text(''.join(patch))
    print(json.dumps({k: result[k] for k in ['status', 'selected_declarations', 'selected_kinds', 'modules', 'predicted_removed']}))


if __name__ == '__main__':
    main()
