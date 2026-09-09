#!/usr/bin/env python3
"""Compile tool sources and exercise positive/negative Lean fixtures in private outputs."""
import argparse
import json
import os
from pathlib import Path
import subprocess
from run_coverage import parse_results


def check(lean, lean_path, output):
    output.mkdir(parents=True, exist_ok=False)
    tools = Path(__file__).resolve().parent
    objects = output/'proofopt'; objects.mkdir()
    env = os.environ.copy(); env.pop('LEAN_SYSROOT',None)
    env.update(LEAN_PATH=str(output)+':'+lean_path,LEAN_NUM_THREADS='2')
    def invoke(name, args, success=True):
        r=subprocess.run([str(lean),*args],cwd=output,env=env,capture_output=True,text=True,timeout=180)
        (output/(name+'.log')).write_text(r.stdout+r.stderr)
        if (r.returncode==0) != success:
            raise AssertionError(f'{name}: exit {r.returncode}: {r.stdout+r.stderr}')
        return r.stdout
    for name in ['Coverage','SourceSpan','Extract','Compare','Audit']:
        invoke('compile-'+name,['-R',str(tools.parent),'-DautoImplicit=false','-DwarningAsError=true',
                                '-o',str(objects/(name+'.olean')),str(tools/(name+'.lean'))])
    fixtures='''import proofopt.Coverage
namespace Fixture
universe u
theorem general (α : Sort u) (x : α) : x = x := rfl
theorem target (n : Nat) : n = n := rfl
theorem restricted (n : Nat) (_h : n = 0) : n = n := rfl
theorem backwards (n : Nat) : n = n := target n
#proofopt_coverage Fixture.target Fixture.general
#proofopt_coverage Fixture.target Fixture.restricted
#proofopt_coverage Fixture.target Fixture.target
#proofopt_coverage Fixture.target Fixture.backwards
end Fixture
'''
    p=output/'CoverageFixture.lean';p.write_text(fixtures)
    text=invoke('coverage-fixtures',['-o',str(output/'CoverageFixture.olean'),str(p)])
    rows=parse_results(text,[('Fixture.target','Fixture.'+x) for x in ['general','restricted','target','backwards']])
    assert [r['status'] for r in rows]==['success','not_covered','rejected','rejected']
    row=rows[0]
    p=output/'Replay.lean';p.write_text('import CoverageFixture\ntheorem replay : '+row['type']+' := '+row['proof']+'\n')
    invoke('coverage-replay',['-DautoImplicit=false','-DwarningAsError=true',str(p)])
    p=output/'Corrupted.lean';p.write_text('import CoverageFixture\ntheorem corrupted : False := '+row['proof']+'\n')
    invoke('coverage-corrupted',[str(p)],False)
    cases={'ordinary':'theorem alpha (n : Nat) : n = n := by\n  rfl\n',
           'nested':'/-- Unicode α, fake := by /- nested -/ -/\ntheorem β (n : Nat) (h : n = n := by rfl) : n = n := by\n  have h2 : n = n := h\n  exact h2\n',
           'where':'theorem gamma : True := by exact helper\nwhere\n  helper : True := True.intro\n',
           'equations':'theorem eqns : (n : Nat) → n = n\n  | _ => rfl\n'}
    for name,source in cases.items():
        raw=output/(name+'.txt');raw.write_text(source)
        p=output/(name+'.lean');p.write_text('import proofopt.SourceSpan\n#proofopt_body '+json.dumps(str(raw))+'\n')
        good=name in ('ordinary','nested')
        text=invoke('span-'+name,[str(p)],good)
        if good:
            marker=next(x for x in text.splitlines() if 'PROOFOPT_BODY ' in x)
            r=json.loads(marker.split('PROOFOPT_BODY ')[1])
            body=source.encode()[r['start_byte']:r['end_byte']].decode()
            assert body.startswith('by') and body.rstrip().endswith('rfl' if name=='ordinary' else 'exact h2')
    variants = {
        'before': 'def datum : Nat := 1\ntheorem kept (n : Nat) : n = n := rfl\n',
        'same': 'def datum : Nat := 1\ntheorem kept (n : Nat) : n = n := Eq.refl n\n',
        'type': 'def datum : Nat := 1\ntheorem kept (n : Int) : n = n := rfl\n',
        'opaque': 'opaque datum : Nat := 1\ntheorem kept (n : Nat) : n = n := rfl\n',
        'value': 'def datum : Nat := 2\ntheorem kept (n : Nat) : n = n := rfl\n',
    }
    for name, source in variants.items():
        folder=output/name;folder.mkdir();path=folder/'Fixture.lean';path.write_text(source)
        invoke('compare-compile-'+name,['-R',str(folder),'-o',str(folder/'Fixture.olean'),str(path)])
    names=output/'names.txt';names.write_text('datum\nkept\n')
    for name in ['same','type','value','opaque']:
        invoke('compare-'+name,['--run',str(tools/'Compare.lean'),str(output/'before/Fixture.olean'),str(output/name/'Fixture.olean'),str(names)],name=='same')
    audit_cases={
        'allowed': ('#proofopt_axioms Fixture.target\n#proofopt_consumes Fixture.backwards Fixture.target\n',True),
        'forbidden': ('#proofopt_axioms sorryAx\n',False),
        'missing_path': ('#proofopt_consumes Fixture.target Fixture.backwards\n',False),
    }
    for name,(body,good) in audit_cases.items():
        p=output/('Audit_'+name+'.lean');p.write_text('import CoverageFixture\nimport proofopt.Audit\n'+body)
        invoke('audit-'+name,[str(p)],good)
    receipt={'tool_compiles':5,'coverage_pairs':4,'proof_text_replayed':1,'corrupted_type_rejected':True,'source_span_cases':4,'preservation_cases':4,'audit_cases':3}
    (output/'acceptance.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=Path,required=True);p.add_argument('--lean-path',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();print(json.dumps(check(a.lean,a.lean_path,a.output)))


if __name__=='__main__':main()
