#!/usr/bin/env python3
"""Stage compiler range metadata for the existing census targets; execute no Lean."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--census-plan', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--family-members', action='store_true', help='Also query compiler ranges for generated-family members')
    args = parser.parse_args()
    census_path, output = args.census_plan.resolve(), args.output_dir.resolve()
    census = json.loads(census_path.read_text())
    assert census['status'] in ['PREPARED_UNCOMPILED_CENSUS_NOT_RETIREMENT_ACCEPTANCE',
                                'PREPARED_UNCOMPILED_MIXED_KIND_CENSUS_NOT_RETIREMENT_ACCEPTANCE']
    assert not output.exists() and output != Path(census['run'])
    assert Path(census['run']) not in output.parents
    for filename, expected in census['bindings'].items():
        assert sha(Path(filename)) == expected, filename
    original = census_path.parent / 'Probe.lean'
    source = original.read_text()
    source = source[:source.index('  let mut targets : Std.HashMap Name String := {}')]
    if not args.family_members:
        start = source.index('private partial def familyOf ')
        end = source.index('private def kind :', start)
        source = source[:start] + source[end:]
    marker = 'set_option maxHeartbeats'
    assert source.count(marker) == 1
    source = source.replace(marker, """private def rangeJson (r : DeclarationRange) : Json := Json.mkObj [
  ("startLine", toJson r.pos.line), ("startColumn", toJson r.pos.column),
  ("endLine", toJson r.endPos.line), ("endColumn", toJson r.endPos.column)]

""" + marker)
    output.mkdir(parents=True)
    payload = output / 'ranges.json'
    source += """  let mut rows : Array Json := #[]
  for (base, owner) in wanted do
    let names := resolved[base]?.getD #[]
    unless names.size == 1 do
      throwError "Nonunique range target: {base}"
    let n := names[0]!
    let ranges ← findDeclarationRanges? n
    let doc ← Lean.Elab.Command.liftIO <| findSimpleDocString? env n (includeBuiltin := false)
    rows := rows.push <| Json.mkObj [
      ("basename", toJson base), ("module", toJson owner), ("name", toJson n.toString),
      ("range", ranges.map (fun r => rangeJson r.range) |>.getD Json.null),
      ("selectionRange", ranges.map (fun r => rangeJson r.selectionRange) |>.getD Json.null),
      ("docString", toJson doc)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile @@OUTPUT@@ (Json.arr rows).compress
end DeadProofFamilyAudit
"""
    if args.family_members:
        source = source.replace('  let mut rows : Array Json := #[]',
                                '  let mut rows : Array Json := #[]\n  let mut rangeTargets : Std.HashMap Name String := {}')
        source = source.replace('    let n := names[0]!\n    let ranges',
                                '    let n := names[0]!\n    rangeTargets := rangeTargets.insert n owner\n    let ranges')
        original_write = '  Lean.Elab.Command.liftIO <| IO.FS.writeFile @@OUTPUT@@ (Json.arr rows).compress'
        assert source.count(original_write) == 1
        source = source.replace(original_write, """  let mut familyRows : Array Json := #[]
  for (n, ci, owner) in decls do
    if let some (root, expected) := familyOf rangeTargets n then
      if owner == expected then
        let ranges ← findDeclarationRanges? n
        familyRows := familyRows.push <| Json.mkObj [
          ("name", toJson n.toString), ("family", toJson root.toString),
          ("module", toJson owner), ("kind", toJson (kind ci)),
          ("range", ranges.map (fun r => rangeJson r.range) |>.getD Json.null),
          ("selectionRange", ranges.map (fun r => rangeJson r.selectionRange) |>.getD Json.null)]
  let payload := Json.mkObj [
    ("schema", toJson "wu-declaration-and-family-ranges-v1"),
    ("status", toJson "ELABORATED_RANGE_METADATA_NOT_SOURCE_OWNERSHIP_OR_DELETION_ACCEPTANCE"),
    ("modules", toJson observed.size), ("rootCount", toJson rows.size),
    ("roots", Json.arr rows), ("members", Json.arr familyRows)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile @@OUTPUT@@ payload.compress""")
    source = source.replace('@@OUTPUT@@', json.dumps(str(payload)))
    query = output / 'Probe.lean'
    query.write_text(source)
    bindings = {**census['bindings'], **{str(p): sha(p) for p in [Path(__file__).resolve(), census_path, query]}}
    plan = {
        'status': 'PREPARED_UNCOMPILED_COMPILER_RANGES_NOT_DELETION_ACCEPTANCE',
        'run': census['run'], 'census_plan': str(census_path),
        'candidate_count': census['candidate_count'], 'research_modules': census['research_modules'],
        'includes_family_member_ranges': args.family_members,
        'query': str(query), 'payload': str(payload), 'bindings': bindings,
        'requires_before_execution': ['Successful terminal source build and 34 validation gates', 'Actual compiled family census and selection', 'Exclusive Lean lock and exact pinned library context'],
        'requires_before_deletion': ['Exact basename/module/runtime-name agreement with actual census', 'All selected declarations have compiler ranges', 'Source/header/docstring/scoped-directive and registration review', 'Disjoint reversible source edits, downstream compilation and kernel validation'],
    }
    (output / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    print(json.dumps({'status': plan['status'], 'candidates': plan['candidate_count'], 'query': str(query)}))


if __name__ == '__main__':
    main()
