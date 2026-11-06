#!/usr/bin/env python3
"""Measure the manifest-bound Wu source tree and final local import closure."""
from pathlib import Path
import argparse,hashlib,importlib.util,json

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2]);a=ap.parse_args();repo=a.repo.resolve();root=repo/'research/wu2008';manifest=root/'source-manifest.json';rows=json.loads(manifest.read_text());byname={r['module']:r for r in rows};assert len(rows)==len(byname)
 counter=repo/'scripts/check.py';spec=importlib.util.spec_from_file_location('published_source_counter',counter);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);counts={}
 for n,r in byname.items():
  p=(root/'src'/Path(*n.split('.'))).with_suffix('.lean');raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==r['source_sha256'],n;text=raw.decode();counts[n]=dict(code_lines=m.count_code_lines(text),physical_lines=len(text.splitlines()),utf8_bytes=len(raw))
 assert {str(p.relative_to(root/'src').with_suffix('')).replace('/','.')for p in(root/'src').rglob('*.lean')}==set(byname)
 closure=set();todo=['WR2ClassicalCertificate']
 while todo:
  n=todo.pop()
  if n not in byname or n in closure:continue
  closure.add(n);todo.extend(byname[n]['imports'])
 def total(names):return dict(modules=len(names),**{k:sum(counts[n][k]for n in names)for k in ['code_lines','physical_lines','utf8_bytes']})
 before=json.loads((repo/'research/wu-hf4-constructive-audit/measurement.json').read_text())['after'];after=dict(whole_tree=total(set(byname)),theorem_closure=total(closure));savings={scope:{k:before[scope][k]-after[scope][k]for k in ['code_lines','physical_lines','utf8_bytes']}for scope in after}
 result=dict(status='ACTUAL_INSTALLED_MANIFEST_BOUND_SOURCE_MEASUREMENT',manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),counter_sha256=hashlib.sha256(counter.read_bytes()).hexdigest(),metric='scripts/check.py count_code_lines; strings retained; whole imported local modules; external Lake dependencies excluded',before=before,after=after,savings=savings);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
