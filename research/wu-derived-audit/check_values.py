from pathlib import Path
import json,re,hashlib,subprocess,argparse
parser=argparse.ArgumentParser(description='Exact comparison of reconstructed Fourth tables with the immutable original git tables.')
parser.add_argument('--repo',type=Path,default=Path.cwd())
args=parser.parse_args()
root=args.repo.resolve();src=root/'research/wu2008/src'
old={}
baseline='c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'
original_hashes={}
for key in ['B','Bq','C','D','outer','outerq']:
    name=f'research/wu2008/src/WR2ClassicalFourthData{key}.lean'
    raw=subprocess.check_output(['git','show',f'{baseline}:{name}'],cwd=root)
    original_hashes[key]=hashlib.sha256(raw).hexdigest()
    old[key]=[int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]
    assert len(old[key])==(2541 if key in ['C','D'] else 10541)
assert original_hashes['B']=='d2a8bd20ac142d9be9d84dada08a27015fa944c185a0b2c6187d1d071a166e1f'
assert original_hashes['outer']=='77d13f96dab6fbb3062f5ea1c71c9eb4b07a1fbdef74d0794fbf25f8e655ee30'
def literal(key):
    raw=(src/f'WR2ClassicalFourthData{key}.lean').read_bytes()
    return [int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]
assert literal('Bq') == old['Bq']
den=6*4000**3;report={}
actual_tables={'Bq':literal('Bq')}
for key,E in [('B',2),('C',2),('D',1),('outer',56)]:
 if key in ['C','D']:
  parent,base=('B',12000) if key=='C' else ('C',16000)
  actual_tables[key+'q']=[(4000*v+base+i-1)//(base+i) for i,v in enumerate(actual_tables[parent][:2541])]
 if key == 'outer':
  actual_tables['outerq']=[]
  for i in range(10541):
   numerator=2654*4000**2*(10**15+actual_tables['B'][i]+(actual_tables['D'][i-8000] if i>=8000 else 0))
   denominator=(12000+i)*(5308000-200*(12000+i))
   actual_tables['outerq'].append((numerator+denominator-1)//denominator)
  assert actual_tables['outerq']==old['outerq']
  report['outerq']={'values':10541,'exact_original_match':True}
 raw=(src/f'WR2ClassicalFourthData{key}.lean').read_bytes();nums=[int(m[1]) for m in re.finditer(rb'^  \| \d+ => (\d+)$',raw,re.M)]
 count=2541 if key in ['C','D'] else 10541
 assert len(nums)==(636 if key in ['C','D'] else 2636)
 actual=[]
 for i in range(count):
  b,j=divmod(i,4);x=nums[b]
  for t in range(4*b,4*b+j):x+=(3*4000**2*(actual_tables[key+'q'][t]+actual_tables[key+'q'][t+1])+E*10**15+den-1)//den
  actual.append(x)
 assert actual==old[key]
 actual_tables[key]=actual
 report[key]=dict(values=len(actual),anchors=len(nums),exact_original_match=True,final_value=actual[-1],source_sha256=hashlib.sha256(raw).hexdigest())
 if key in ['C','D']:
  expected=f'def {key} (i : ℕ) : ℕ := if i ≤ 2540 then ClassicalCumulativeTable.table (ClassicalCumulativeDivision.quotient {parent} {base}) {E} {key}Anchor i else 0'
  assert expected in raw.decode()
division=(src/'WR2ClassicalCumulativeDivision.lean').read_text()
assert 'def ceilDiv (n d : ℕ) : ℕ := (n+d-1)/d' in division
assert 'def quotient (q : ℕ → ℕ) (base i : ℕ) : ℕ := ceilDiv (4000*q i) (base+i)' in division
helper=(src/'WR2ClassicalCumulativeTable.lean').read_text()
assert 'if i ≤ 10540 then accumulate q E (anchor (i/4)) (4*(i/4)) (i%4) else 0' in helper
assert '(3*4000^2*(q i+q (i+1))+E*1000000000000000+(6*4000^3-1))/(6*4000^3)' in helper
assert '| n+1 => accumulate q E anchor start n + increment q E (start+n)' in helper
outerq_source=(src/'WR2ClassicalFourthDataouterq.lean').read_text()
assert 'if i ≤ 10540 then' in outerq_source and 'else 0' in outerq_source
assert 'let numerator := 2654*4000^2*(1000000000000000+B i+(if 8000 ≤ i then D (i-8000) else 0))' in outerq_source
assert 'let denominator := (12000+i)*(5308000-200*(12000+i))' in outerq_source
assert '(numerator+denominator-1)/denominator' in outerq_source
report['outerq']['source_sha256']=hashlib.sha256(outerq_source.encode()).hexdigest()
report['default_tail']='The definitions return zero above 10540 for B/outer/outerq and above 2540 for C/D, matching the original block tables.'
report['arithmetic']='Exact Python integers, not floating point; Lean consumers are checked separately.'
report['baseline_commit']=baseline
report['original_source_sha256']=original_hashes
print(json.dumps(report,indent=2))
