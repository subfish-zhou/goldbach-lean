"""Reconstruct every new certificate and compare with the accepted literal generator."""
from pathlib import Path
from fractions import Fraction
import hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=ROOT/'research/wu2008/src'
base=json.loads((HERE/'baseline-source-index.json').read_text())
spec=importlib.util.spec_from_file_location('accepted_hf4_generator',HERE/'baseline_generator.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
original=old.generate()
assert len(original)==15
for name,text in original.items():
    assert hashlib.sha256(text.encode()).hexdigest()==base[Path(name).stem]['sha256'],name

# Bind the interpretation of derived expressions to the actual Lean definitions.
ops=(SRC/'Hf4QuadExactOperations.lean').read_text()
for name,expected in {
 'addExact':'⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d,p.error+q.error⟩',
 'scale':'⟨s*p.a,s*p.b,s*p.c,s*p.d,|s|*p.error⟩',
}.items():
    rhs=re.search(r'def '+name+r'\b.*?:=\s*([^\n]+)',ops,re.S)[1]
    assert ''.join(rhs.split())==expected,name
for name in ['Hf4QuadRationalModel','Hf4QuadCompactDag']:
    assert hashlib.sha256((SRC/(name+'.lean')).read_bytes()).hexdigest()==base[name]['sha256'],name

counts={'literal':0,'addExact':0,'neg':0,'scale':0}
def records(text,shared,count=False):
    values={}
    for j,rhs in re.findall(r'^def c(\d+) : Certificate := (.+)$',text,re.M):
        assert int(j) not in values
        if rhs.startswith('⟨'):
            v=tuple(Fraction(x.strip('()')) for x in rhs.strip('⟨⟩').split(','))
            kind='literal'
        else:
            op,*refs=rhs.split()
            def ref(x):
                return shared[int(x.split('.c')[1])] if x.startswith('SharedCertificates.') else values[int(x[1:])]
            kind=op.removeprefix('RationalModel.')
            if kind=='scale':
                k=Fraction(refs[0].strip('()'));a=ref(refs[1]);v=tuple(k*x for x in a[:4])+(abs(k)*a[4],)
            else:
                a=ref(refs[0])
                if kind=='neg':v=tuple(-x for x in a[:4])+(a[4],)
                else:
                    assert kind=='addExact',op
                    b=ref(refs[1]);v=tuple(x+y for x,y in zip(a,b))
        assert len(v)==5
        values[int(j)]=v
        if count:counts[kind]+=1
    return values

shared=records((SRC/'Hf4QuadSharedCertificates.lean').read_text(),{},True)
assert len(shared)==49
panels=0
for name in ['Hf4QuadPanel0.lean']+[f'Hf4QuadBatch{i}.lean' for i in range(13)]:
    before=original[name];after=(SRC/name).read_text()
    op=re.findall(r'namespace Hf4Quad.Panel(\d+)\n(.*?)end Hf4Quad.Panel\1',before,re.S)
    np=re.findall(r'namespace Hf4Quad.Panel(\d+)\n(.*?)end Hf4Quad.Panel\1',after,re.S)
    assert len(op)==len(np)
    for (oi,ot),(ni,nt) in zip(op,np):
        assert oi==ni
        expected=records(ot,{})
        local=records(nt,shared,True)
        assert not (shared.keys() & local.keys())
        actual=shared|local
        assert len(expected)==len(actual)==381
        assert actual==expected,oi
        for th in ['compact_model','mass_bounds']:
            signature=lambda t:re.search(r'theorem '+th+r'.*? :=',t,re.S)[0]
            assert signature(ot)==signature(nt),(oi,th)
        panels+=1
assert panels==40
report=dict(original_generator_matches_accepted_sources=15,panels=panels,
    certificate_values_compared=15240,exact_rational_fields=76200,
    preserved_public_statements=80,all_fields_exact=True,stored_records=counts,
    original_literal_records=15240,actual_literal_records_removed=15240-counts['literal'],
    arithmetic='Exact fractions parsed from original and actual new Lean source; operator definitions bound above. This audit does not replace Lean verification.',
    baseline_generator_sha256=hashlib.sha256((HERE/'baseline_generator.py').read_bytes()).hexdigest())
print(json.dumps(report,indent=2))
