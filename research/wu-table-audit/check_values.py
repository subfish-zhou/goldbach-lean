from pathlib import Path
import json,re,hashlib,subprocess,argparse
parser=argparse.ArgumentParser(description='Exact comparison of reconstructed Fourth tables with the immutable original git tables.')
parser.add_argument('--repo',type=Path,default=Path.cwd())
args=parser.parse_args()
root=args.repo.resolve();src=root/'research/wu2008/src'
old={}
baseline='c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'
original_hashes={}
for key in ['B','Bq','outer','outerq']:
    name=f'research/wu2008/src/WR2ClassicalFourthData{key}.lean'
    raw=subprocess.check_output(['git','show',f'{baseline}:{name}'],cwd=root)
    original_hashes[key]=hashlib.sha256(raw).hexdigest()
    old[key]=[int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]
    assert len(old[key])==10541
assert original_hashes['B']=='d2a8bd20ac142d9be9d84dada08a27015fa944c185a0b2c6187d1d071a166e1f'
assert original_hashes['outer']=='77d13f96dab6fbb3062f5ea1c71c9eb4b07a1fbdef74d0794fbf25f8e655ee30'
for key in ['Bq','outerq']:
    raw=(src/f'WR2ClassicalFourthData{key}.lean').read_bytes()
    assert [int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]==old[key]

D=6*4000**3;report={}
for key,E in [('B',2),('outer',56)]:
 raw=(src/f'WR2ClassicalFourthData{key}.lean').read_bytes();nums=[int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]
 assert len(nums)==2636
 actual=[]
 for i in range(10541):
  b,j=divmod(i,4);x=nums[b]
  for t in range(4*b,4*b+j):x+=(3*4000**2*(old[key+'q'][t]+old[key+'q'][t+1])+E*10**15+D-1)//D
  actual.append(x)
 assert actual==old[key]
 report[key]=dict(values=len(actual),anchors=len(nums),exact_original_match=True,final_value=actual[-1],source_sha256=hashlib.sha256(raw).hexdigest())
helper=(src/'WR2ClassicalCumulativeTable.lean').read_text()
assert 'if i ≤ 10540 then accumulate q E (anchor (i/4)) (4*(i/4)) (i%4) else 0' in helper
assert '(3*4000^2*(q i+q (i+1))+E*1000000000000000+(6*4000^3-1))/(6*4000^3)' in helper
assert '| n+1 => accumulate q E anchor start n + increment q E (start+n)' in helper
report['default_tail']='The compressed definition explicitly returns zero for every i > 10540, matching the original block tables.'
report['arithmetic']='Exact Python integers, not floating point; Lean consumers are checked separately.'
report['baseline_commit']=baseline
report['original_source_sha256']=original_hashes
print(json.dumps(report,indent=2))
