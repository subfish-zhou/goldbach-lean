"""Read-only comparison with the actual accepted structural toolchain pins."""
from pathlib import Path
import hashlib,json,subprocess
EXPECTED_PLAN='04d9a31438198668bfec595f9949f2e1e32e9aef7dc425f051c99d8419fa1410'
EXPECTED={'bin/lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','bin/leanchecker':'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a','lib/lean/Init.olean':'1e95ecbedde5d49a3e6550ec04f0d4176245196093254e26015c4b5f5a5844fd'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def review(P):
 old=Path('/tmp/wu-structural-full-probe-v7/full/plan.json');assert sha(old)==EXPECTED_PLAN;prior=json.loads(old.read_text());assert P['lean']==prior['lean']and P['package_paths']==prior['package_paths'];base=Path(P['sysroot']);assert base/'bin/lean'==Path(P['lean']);bindings={str(old):EXPECTED_PLAN}
 for name,h in EXPECTED.items():
  p=base/name;assert sha(p)==h,('changed toolchain artifact',str(p));bindings[str(p)]=h
 revisions={r['name']:r['rev']for r in prior['pinned_packages']};seen={}
 for name in P['package_paths']:
  q=Path(name);roots=[p for p in[q,*q.parents]if p.parent.name=='packages'and p.parent.parent.name=='.lake'];assert len(roots)==1;root=roots[0];assert root.name in revisions;actual=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();assert actual==revisions[root.name];seen[root.name]=actual
 assert set(seen)==set(revisions)
 return dict(status='ACTUAL_COMPILER_CHECKER_INIT_HASHES_AND_TEN_PACKAGE_REVISIONS_MATCH_ACCEPTED_BASELINE',bindings=bindings,package_revisions=seen)
if __name__=='__main__':
 P=json.loads(Path('/tmp/wu-hf4-installed-v7-resume-v1/plan.json').read_text());result=review(P);Path('/tmp/wu-hf4-adoption-v1/toolchain-actual-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status=result['status'],artifacts=len(result['bindings'])-1,packages=len(result['package_revisions']))))
