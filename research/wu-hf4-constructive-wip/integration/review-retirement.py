from pathlib import Path
import json,hashlib,importlib.util,re
B=Path(__file__).resolve().parent;R=Path('/home/azureuser/goldbach-lean/research/wu2008');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();p=Path('/tmp/wu-hf4-post-v5-integration-v2/prepare.py');s=importlib.util.spec_from_file_location('retirement_audit',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
P=json.loads((B/'plan.json').read_text());retired=json.loads(Path('/tmp/wu-hf4-post-v5-integration-v2/retired-declarations.json').read_text())['declarations'];texts={n:(R/'src'/Path(*n.split('.'))).with_suffix('.lean').read_text()for n in P['production_sources']};assert all(hashlib.sha256(t.encode()).hexdigest()==P['production_sources'][n]for n,t in texts.items());preserved={f'Hf4Quad.Panel{i}.mass_bounds'for i in range(40)}
a=m.reference_audit(texts,retired,preserved);assert not a['unpreserved_resolved_references'];overlay={n:(B/'overlay'/Path(*n.split('.'))).with_suffix('.lean').read_text()for n in P['overlay']};b=m.reference_audit(overlay,retired,preserved);assert not b['unpreserved_resolved_references']
# Inspect registrations in the retired source scope, after lexical comments/strings.
commands=[]
for n in P['retired']:
 for i,line in enumerate(m.COUNTER.code_only(texts[n]).splitlines(),1):
  if re.search(r'@\[|^\s*(?:attribute|(?:local\s+|scoped\s+)?instance|syntax|macro|elab|initialize|builtin_initialize|export|notation)\b',line):commands.append(dict(module=n,line=i,source=line))
assert not commands,commands
out=dict(status='ACTUAL_INSTALLED_BASELINE_SOURCE_REFERENCE_AND_REGISTRATION_REVIEW_NOT_FORMAL_NAME_CENSUS',plan_sha256=sha(B/'plan.json'),baseline_sha256=P['baseline_manifest_sha256'],retired_module_count=len(P['retired']),explicit_retired_declaration_count=len(retired)-40,preserved_original_mass_headers=40,retired_source_registration_commands=commands,baseline_reference_audit=a,new_reference_audit=b,limitations='Source name/open-scope resolution only; generated private names and reflection are not exhaustively enumerated. Complete formal source-context and public-interface checks remain separate.')
(B/'retirement-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','retired_module_count','explicit_retired_declaration_count','preserved_original_mass_headers']}))
