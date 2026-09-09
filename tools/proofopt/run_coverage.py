#!/usr/bin/env python3
"""Bounded explicit-pair coverage with independent proof-text re-elaboration."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

PREFIX = 'PROOFOPT_COVERAGE '


def parse_results(stdout, expected):
    rows = [json.loads(line.split(PREFIX,1)[1]) for line in stdout.splitlines() if PREFIX in line]
    pairs = [(r['target'],r['provider']) for r in rows]
    if len(pairs) != len(set(pairs)) or set(pairs) != set(expected):
        raise ValueError('coverage result inventory mismatch')
    for row in rows:
        if row['status'] == 'success' and not (row.get('kernel_checked') is True and
                row.get('has_mvar') is False and row.get('has_sorry') is False and row.get('remaining') == []):
            raise ValueError('invalid success receipt')
    return rows


def identifier(name):
    # Do not turn untrusted JSON into arbitrary Lean commands. Standard full names,
    # including Greek/subscript identifiers, are supported; exotic escaped names
    # need explicit manual probes instead of silently changing their spelling.
    if not name or any(not re.fullmatch(r"[^\W\d][\w'!?]*", s, re.UNICODE) for s in name.split('.')):
        raise ValueError('unsupported Lean identifier: '+name)
    return name


def logged_run(command, output, env, timeout, tag):
    try:
        result=subprocess.run(command,cwd=output,env=env,capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        def text(value):
            return value.decode(errors='replace') if isinstance(value,bytes) else (value or '')
        (output/(tag+'.log')).write_text(text(exc.stdout)+text(exc.stderr))
        (output/(tag+'-failure.json')).write_text(json.dumps({'status':'timeout','command':command,'seconds':timeout})+'\n')
        raise
    (output/(tag+'.log')).write_text(result.stdout+result.stderr)
    return result


def run(pairs, lean, lean_path, output, timeout=180):
    output.mkdir(parents=True, exist_ok=False)
    pairs = list({(p['target'],p['provider']):p for p in pairs}.values())
    imports = sorted({identifier(p[k]) for p in pairs for k in ('target_module','provider_module')})
    header = 'import proofopt.Coverage\n'+''.join('import '+m+'\n' for m in imports)
    code = header+'\n'+''.join('#proofopt_coverage '+identifier(p['target'])+' '+identifier(p['provider'])+'\n' for p in pairs)
    probe = output/'Probe.lean'; probe.write_text(code)
    env = os.environ.copy(); env.pop('LEAN_SYSROOT',None)
    env.update(LEAN_PATH=lean_path,LEAN_NUM_THREADS='2')
    command=[str(lean),str(probe)]
    result=logged_run(command,output,env,timeout,'probe')
    if result.returncode:
        raise RuntimeError('coverage process failed; see '+str(output/'probe.log'))
    rows=parse_results(result.stdout,[(p['target'],p['provider']) for p in pairs])
    (output/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
    passed=[r for r in rows if r['status']=='success']
    # Generated proof lambdas retain original binder names, including unused
    # hypotheses. This style-only exception applies to replay, not source builds.
    replay=header+'\nset_option linter.unusedVariables false\n'
    for i,row in enumerate(passed):
        replay+='section\n'
        if row['levels']:
            replay+='universe '+' '.join(identifier(x) for x in row['levels'])+'\n'
        replay+=f"theorem proofoptReplay{i} : {row['type']} := {row['proof']}\nend\n"
    path=output/'Replay.lean';path.write_text(replay)
    replay_result=logged_run([str(lean),'-DautoImplicit=false','-DwarningAsError=true',str(path)],output,env,timeout,'replay')
    if replay_result.returncode:
        raise RuntimeError('proof text replay failed; see '+str(output/'replay.log'))
    receipt={'pairs':len(rows),'kernel_success':len(passed),'text_replay_success':len(passed),
             'not_covered':sum(r['status']=='not_covered' for r in rows),
             'rejected':sum(r['status']=='rejected' for r in rows),'errors':sum(r['status']=='error' for r in rows),
             'actual_source_replacements':0}
    (output/'acceptance.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidates',type=Path,required=True);p.add_argument('--lean',type=Path,required=True)
    p.add_argument('--lean-path',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--limit',type=int,default=20);p.add_argument('--timeout',type=int,default=180)
    a=p.parse_args(); data=json.loads(a.candidates.read_text())
    print(json.dumps(run(data['candidates'][:a.limit],a.lean,a.lean_path,a.output,a.timeout)))


if __name__=='__main__':main()
