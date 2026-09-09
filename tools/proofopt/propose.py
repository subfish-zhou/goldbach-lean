#!/usr/bin/env python3
"""Create an isolated source proposal from a successful coverage receipt.

This does not install or certify the proposal: compile it independently, compare
its full declarations, audit its axiom cone and replay it before integration.
"""
import argparse
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
from index import SourceText, digest
from run_coverage import identifier


def propose(database, results, target, source, output, lean, lean_path, recipe='exact'):
    rows=json.loads(results.read_text())
    rows=[r for r in rows if r['target']==target and r['status']=='success']
    if len(rows)!=1:
        raise ValueError('select exactly one successful coverage result per target')
    receipt=rows[0]
    if not (receipt['kernel_checked'] and not receipt['has_mvar'] and not receipt['has_sorry'] and not receipt['remaining']):
        raise ValueError('invalid coverage success')
    with closing(sqlite3.connect(database.resolve().as_uri()+'?mode=ro',uri=True)) as conn:
        conn.row_factory=sqlite3.Row
        state=conn.execute("SELECT value FROM metadata WHERE key='state'").fetchone()
        if state is None or state[0]!='complete':raise ValueError('incomplete discovery index')
        ambiguous=conn.execute('SELECT name FROM ambiguous_declarations WHERE name IN (?,?)',(target,receipt['provider'])).fetchall()
        if ambiguous:raise ValueError('ambiguous target or provider occurrence')
        row=conn.execute('SELECT * FROM declarations WHERE name=?',(target,)).fetchone()
        provider=conn.execute('SELECT * FROM declarations WHERE name=?',(receipt['provider'],)).fetchone()
        if row is None or provider is None or not row['explicit']:
            raise ValueError('missing explicit declaration record')
        module=json.loads(conn.execute('SELECT metadata FROM modules WHERE module=?',(row['module'],)).fetchone()[0])
    original=(source/module['source']).read_bytes()
    if digest(original)!=module['source_sha256']:
        raise ValueError('source no longer matches discovery baseline')
    st=SourceText(original.decode('utf-8'))
    span=json.loads(row['span']);snippet=st.slice(span)
    output.mkdir(parents=True,exist_ok=False)
    snippet_path=output/'declaration.txt';snippet_path.write_bytes(snippet.encode())
    probe=output/'SourceProbe.lean'
    probe.write_text('import proofopt.SourceSpan\nimport '+identifier(row['module'])+'\nopen scoped BigOperators\n#proofopt_body '+json.dumps(str(snippet_path))+'\n')
    env=os.environ.copy();env.pop('LEAN_SYSROOT',None);env.update(LEAN_PATH=lean_path,LEAN_NUM_THREADS='2')
    run=subprocess.run([str(lean),str(probe)],cwd=output,env=env,capture_output=True,text=True,timeout=120)
    (output/'source-parser.log').write_text(run.stdout+run.stderr)
    if run.returncode:
        raise RuntimeError('source parser failed; see source-parser.log')
    markers=[json.loads(x.split('PROOFOPT_BODY ',1)[1]) for x in run.stdout.splitlines() if 'PROOFOPT_BODY ' in x]
    if len(markers)!=1:raise ValueError('source parser receipt missing/duplicated')
    bounds=markers[0]
    begin_chars=st.position(span[0],span[1]);base=len(st.text[:begin_chars].encode())
    a,b=base+bounds['start_byte'],base+bounds['end_byte']
    if original[a:b]!=snippet.encode()[bounds['start_byte']:bounds['end_byte']]:
        raise ValueError('source byte mapping mismatch')
    recipes={
        'exact': 'by\n  exact _root_.'+identifier(receipt['provider']),
        'apply': 'by\n  apply _root_.'+identifier(receipt['provider']),
        'discharge': 'by\n  apply _root_.'+identifier(receipt['provider'])+' <;>\n    first | assumption | rfl | (simp only [*]; done)',
    }
    if recipe not in recipes:raise ValueError('unsupported source recipe')
    replacement=recipes[recipe].encode()
    modified=original[:a]+replacement+original[b:]
    import_line=('import '+identifier(provider['module'])+'\n').encode()
    added_import=provider['module']!=row['module'] and import_line not in original.splitlines(keepends=True)
    if added_import:modified=import_line+modified
    path=output/module['source'];path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(modified)
    report={'target':target,'recipe':recipe,'provider':receipt['provider'],'module':row['module'],'provider_module':provider['module'],
            'source':module['source'],'baseline_sha256':digest(original),'candidate_sha256':digest(modified),
            'candidate_path':str(path),'old_body_bytes':[a,b],'added_direct_import':added_import,
            'original_lines':len(original.splitlines()),'candidate_lines':len(modified.splitlines()),
            'status':'proposal_only; requires independent source compilation and acceptance'}
    (output/'proposal.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['database','results','source','output','lean']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--target',required=True);p.add_argument('--lean-path',required=True)
    p.add_argument('--recipe',choices=['exact','apply','discharge'],default='exact')
    a=p.parse_args();print(json.dumps(propose(a.database,a.results,a.target,a.source,a.output,a.lean,a.lean_path,a.recipe)))


if __name__=='__main__':main()
