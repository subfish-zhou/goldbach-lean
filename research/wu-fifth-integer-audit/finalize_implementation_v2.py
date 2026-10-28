"""Root-reviewable finalizer; execute manually only after all acceptance gates."""
from pathlib import Path
import json,hashlib,shutil,datetime,re
root=Path('/home/azureuser/goldbach-lean');wu=root/'research/wu2008';audit=root/'research/wu-fifth-integer-audit';tmp=Path('/tmp/wu-fifth-production')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def writejson(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
require(not (tmp/'acceptance-complete.json').exists(),'already finalized')
checks=read(tmp/'checks-complete.json');require(checks['status']=='pass' and checks['modules']==4142,'postvalidation incomplete')
size=read(audit/'source-size.json');w=size['whole_tree']['after'];c=size['theorem_closure']['after'];red=size['whole_tree']['reduction']
require((w['modules'],w['code_lines'],c['modules'],c['code_lines'])==(4142,584819,3755,544065),'measurement')
require((red['modules'],red['code_lines'],red['physical_lines'])==(39,3779,3699),'reduction')
status=read(wu/'build/STATUS.json');require(status['status']=='passed' and status['verified']==status['planned']==4142,'build incomplete')
manifest=sha(wu/'source-manifest.json');accept=read(wu/'build/classical-acceptance.json')
require(accept['status']=='pass' and accept['modules']==4142 and accept['manifest_sha256']==manifest,'literal acceptance stale')
preserve=read(audit/'preservation.json');values=read(audit/'actual-source-values.json')
for name,x in [('preservation',preserve),('values',values)]:
 require(x['status']=='PASS' and x['fixed_Git_payment_equality']==3072 and x['interpreted_actual_Lean_Nat_payments']==3072 and x['independent_64point_sums']==48 and x['outside_support_zero_guard_exact'],name+' failed')
 for file,digest in x['candidate_source_hashes'].items():require(sha(wu/'src'/file)==digest,name+' source stale '+file)
 require(x['interpreter_sha256']==sha(audit/'lean_nat.py'),name+' interpreter stale')
require(preserve['unchanged_Certificate'] and preserve['Root_all_paid_declarations']==3 and preserve['sum_total_declarations']==6 and preserve['cPoly_body_and_QName_preserved'] and preserve['TableCheck_other_body_preserved'],'contracts')
totals={'initial':273358482524540,'middle':661191362320992,'terminal':405237426677551}
for branch,total in totals.items():require(values['branches'][branch]['total']==total and values['branches'][branch]['exact_all_values_match'],'totals')
negative=read(audit/'negative-controls.json');require(negative and all(x['rejected'] for x in negative),'negative controls')
kernels=checks['kernel_replays'];require(kernels==read(tmp/'kernel-modules.json'),'kernel lists differ');require('WR2ClassicalCertificate' in kernels and 'WR2ClassicalFifthCertificate' in kernels,'kernel scopes')
generators=['classical_c_eighth_certificates.py','classical_sixth_certificates.py','classical_fourth_certificates.py','classical_fifth_certificates.py']
glogs=list(tmp.glob('generator-*.log'));require(len(glogs)==4,'generator log count')
logs=[tmp/n for n in ['full-build.log','literal-check.log','verify-sources.log','measure.log','preservation.log','actual-source-values.log','negative_controls.log']]+glogs+[tmp/('kernel-'+n+'.log') for n in kernels]
for p in logs:require(p.is_file(),'missing '+str(p))
# Read live documents, with narrowly bounded replacements, preserving concurrent main-project edits.
docpaths=[root/'README.md',root/'docs/SOURCE_SIZE.md',wu/'README.md',root/'docs/VERIFICATION.md',root/'docs/RELEASE_NOTES.md',wu/'mathematical-status.json']
original={p:p.read_text() for p in docpaths};changes={};count=w['modules'];saving=red['code_lines'];cumulative=1126636-c['code_lines']
def rewrite_wu(text):
 pairs={'4181':'4142','4,181':'4,142','3794':'3755','3,794':'3,755','547,844':'544,065','645,758':'642,059','578,792':f'{cumulative:,}','517':'3,779'}
 for old,new in pairs.items():text=re.sub(r'(?<![\d,])'+re.escape(old)+r'(?![\d,])',lambda _:new,text)
 return text.replace('WU_LIGHT_NUMERIC_LAYERS.md','WU_FIFTH_INTEGER_PAYMENTS.md').replace('wu-light-layer-audit','wu-fifth-integer-audit').replace('light numeric layer compression','Fifth integer payment compression').replace('light numeric layer snapshot','Fifth integer payment snapshot').replace('本轮纯数值分层与模块合并','本轮第五项整数公式压缩').replace('当前纯数值分层与模块合并','当前第五项整数公式压缩')
p=root/'README.md';s=original[p];start=s.index('## Wu04/Wu08:');end=s.index('\n## ',start+1);changes[p]=s[:start]+rewrite_wu(s[start:end])+s[end:]
p=root/'docs/SOURCE_SIZE.md';s=original[p];lines=s.splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith('| Wu04/Wu08') or line.startswith('latest independently accepted ['):lines[i]=rewrite_wu(line)
s=''.join(lines);start=s.index('accepted full inventory contains ');end=s.index('\n\n',start);changes[p]=s[:start]+rewrite_wu(s[start:end])+s[end:]
p=wu/'README.md';lines=original[p].splitlines(keepends=True)
for i,line in enumerate(lines):
 if line.startswith(('**4181 模块','当前[统计与验收]','本页中的 8826','当前纯数值分层与模块合并')):lines[i]=rewrite_wu(line)
 elif '当前记录见[最新验收](../wu-light-layer-audit/validation.json)' in line:lines[i]=line.replace('当前记录见[最新验收](../wu-light-layer-audit/validation.json)','当前记录见[最新验收](../wu-fifth-integer-audit/validation.json)')
changes[p]=''.join(lines)
p=root/'docs/VERIFICATION.md';s=original[p];start=s.index('The [Wu04/Wu08 development]');end=s.index('\n## ',start);chunk=re.sub(r'Its \d+-module source build','Its 4142-module source build',s[start:end]);s=s[:start]+chunk+s[end:]
start=s.index('## Wu light numeric layers');end=s.find('\n## ',start+1);end=len(s) if end<0 else end;s=s[:start]+s[start:end].replace('The current 4,181-module','The then-current 4,181-module')+s[end:]
entry=f'''## Wu Fifth integer payments (2026-10-27)

The 4,142-module research source/receipt build, literal statements and standard
axioms, four generator checks, exact source-value/preservation audits and
{len(kernels)} named independent kernel replays pass. All 3,072 original payments,
48 separate 64-point sums and three totals are unchanged. The phase removes
3,779 effective lines, 3,699 physical lines and 39 modules.
See [the acceptance audit](../research/wu-fifth-integer-audit/validation.json).

'''
pos=s.index('## Wu light numeric layers');changes[p]=s[:pos]+entry+s[pos:]
p=root/'docs/RELEASE_NOTES.md';s=original[p];pos=s.index('\n')+1;changes[p]=s[:pos]+'''
## Wu Fifth integer payments (2026-10-27)

Exact integer formulas replace three 1,024-entry Fifth payment tables and their
repeated pointwise certificates. Pairing the signed polynomial coefficients
preserves the degree-12 polynomial exactly and justifies every Nat subtraction.
All original precision, constants, 3,072 payments and 48 block sums remain.
The accepted 4,142-module phase removes 3,779 effective lines and 39 modules.
[Report](WU_FIFTH_INTEGER_PAYMENTS.md).

'''+s[pos:]
s=json.loads(original[wu/'mathematical-status.json']);s.setdefault('pre_fifth_integer_acceptance',s['final_acceptance'].copy());a=s['final_acceptance'];a.update(modules=count,manifest_sha256=manifest,build_log='build/fifth-integer-compression-build.log',final_source_import_closure_modules=c['modules'],fifth_integer_compression_audit='../wu-fifth-integer-audit/validation.json');s['completion_audit']['scope']='Historical initial completion audit; current acceptance is final_acceptance and ../wu-fifth-integer-audit/validation.json.'
report=f'''# Fifth-slot exact integer payment formulas

This phase follows [the lightweight numeric layers](WU_LIGHT_NUMERIC_LAYERS.md).
The final `WuPaper.ClassicalSlots.one8938` theorem, legacy `one894` interface,
original constants, grids and numerical precision are unchanged.

Three 1,024-entry payment tables are replaced by exact Nat formulas. The existing
12-term logarithm lower polynomial uses the shared homogeneous integer Horner
identity. The degree-12 signed cPoly is regrouped into five positive/negative
coefficient pairs with common denominator 52,254,720. On its original domain
0 ≤ Y ≤ D, each pair satisfies b*Y ≤ a*D, so every Nat subtraction is exact.
This is an algebraic identity, not a new approximation or constant adjustment.
The original cPoly QName and expression move to a pure rational data module;
the real bridges and final Fifth Certificate remain unchanged.

The generic rational identity and Nat floor inequality replace 48 pointwise
GridBlock certificates. Three sum containers still check 48 independent
64-point sums using `decide +kernel`. Their original numerator totals are
273358482524540, 661191362320992 and 405237426677551, with payment scale 10^12.
All 3,072 original payments and the zero outside-support guard are preserved.

| Scope | Effective lines before | Effective lines after | Reduction |
|---|---:|---:|---:|
| Full local Wu tree | 588,598 | 584,819 | 3,779 |
| Final theorem import closure | 547,844 | 544,065 | 3,779 |

The full tree contains 4,142 modules and {w['physical_lines']:,} physical lines;
the theorem closure contains 3,755 modules and {c['physical_lines']:,} physical
lines. Net savings include all new helpers: 39 modules, 3,699 physical lines
and {red['utf8_bytes']:,} bytes. External Lake packages are excluded. These count
whole imported modules, not minimum declaration-level proofs.

The full source/receipt build, literal statements and standard axioms, four
generators, independent actual-source Nat interpretation, preservation checks,
{len(negative)} negative controls and {len(kernels)} named kernel replays pass. The interpreter
checks actual Lean formula syntax, including clipped Nat subtraction and
division-by-zero semantics, against frozen original tables. This Python check
supplements Lean proof/kernel checking. Unchanged receipts may be reused after
dependency validation; this is not a forced clean build or a claimed speedup.

See [the accepted audit](../research/wu-fifth-integer-audit/validation.json) and
[reproduction commands](../research/wu-fifth-integer-audit/README.md).
'''
auditreadme='''# Fifth integer payment acceptance audit

Reproduce from the repository root:

```sh
python3 research/wu-fifth-integer-audit/measure.py
python3 research/wu-fifth-integer-audit/preservation.py
python3 research/wu-fifth-integer-audit/actual-source-values.py
python3 research/wu-fifth-integer-audit/negative_controls.py
python3 research/wu2008/diagnostics/classical_fifth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_c_eighth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_sixth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_fourth_certificates.py --check research/wu2008/src
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2 --timeout 1200
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

Frozen records bind the previous accepted inventory, original payment tables,
public statements and all sources outside the Fifth scope. The actual-source
interpreter checks all 3,072 values and 48 block sums. Negative controls verify
that relevant alterations are rejected. These checks supplement Lean checking.
The validation record lists kernel scopes, tool/source hashes and logs. Older
acceptance directories remain unchanged historical records.
See [the report](../../docs/WU_FIFTH_INTEGER_PAYMENTS.md).
'''
# First write occurs only after all gates and transforms succeed.
for p,text in original.items():require(p.read_text()==text,'concurrent document edit '+str(p))
for p in logs:shutil.copy2(p,audit/p.name)
for name in ['classical-acceptance.json','classical-literal-axioms.log']:shutil.copy2(wu/'build'/name,audit/name)
for name in ['checks-complete.json','kernel-modules.json']:shutil.copy2(tmp/name,audit/name)
shutil.copy2(Path(__file__),audit/'finalize_implementation_v2.py')
shutil.copy2(tmp/'full-build.log',wu/'build/fifth-integer-compression-build.log');shutil.copy2(tmp/'kernel-WR2ClassicalCertificate.log',wu/'build/classical-kernel-replay.log')
a['records']={n:sha(wu/'build'/n) for n in ['fifth-integer-compression-build.log','classical-acceptance.json','classical-literal-axioms.log','classical-kernel-replay.log']};changes[wu/'mathematical-status.json']=json.dumps(s,ensure_ascii=False,indent=2)+'\n'
for p,text in changes.items():p.write_text(text)
(root/'docs/WU_FIFTH_INTEGER_PAYMENTS.md').write_text(report);(audit/'README.md').write_text(auditreadme)
record=dict(status='pass',accepted_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=manifest,modules=count,theorem_closure_modules=c['modules'],effective_lines_removed=saving,physical_lines_removed=3699,modules_removed=39,theorem='WuPaper.ClassicalSlots.one8938',legacy_theorem='WuPaper.ClassicalSlots.one894',payments=3072,independent_64point_sums=48,original_totals=totals,kernel_replays=kernels,build_tools={n:sha(wu/n) for n in ['build.py','test_build.py','check_classical.py','verify_sources.py']},generators={n:sha(wu/'diagnostics'/n) for n in generators},audit_tools={p.name:sha(p) for p in audit.glob('*.py')},documentation={str(p.relative_to(root)):sha(p) for p in [*docpaths,root/'docs/WU_FIFTH_INTEGER_PAYMENTS.md']},files={str(p.relative_to(audit)):sha(p) for p in sorted(audit.rglob('*')) if p.is_file() and p.name!='validation.json' and '__pycache__' not in p.parts})
writejson(audit/'validation.json',record)
for name,digest in record['files'].items():require(sha(audit/name)==digest,'evidence changed '+name)
for p in [root/'docs/WU_FIFTH_INTEGER_PAYMENTS.md',audit/'README.md']:
 for target in re.findall(r'\]\(([^)]+)\)',p.read_text()):
  if '://' not in target and not target.startswith('#'):require((p.parent/target.split('#')[0]).exists(),'broken link '+target)
writejson(tmp/'acceptance-complete.json',dict(status='pass',modules=count,manifest_sha256=manifest,audit=str(audit/'validation.json')))
print('ACCEPTANCE_FINALIZED_AND_VERIFIED',count,saving,flush=True)
