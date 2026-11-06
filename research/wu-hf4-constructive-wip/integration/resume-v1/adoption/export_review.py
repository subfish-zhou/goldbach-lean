"""Independent expected-name/payload and exact exporter invocation review."""
from pathlib import Path
import json,hashlib
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
NORMALIZATION='erase-mdata-binder-names; levelParams-positional-alpha-v1'
def payload(data,names,values):
 assert data['schema']=='wu-public-interface-v1'and data['normalization']==NORMALIZATION
 assert type(data['include_definitions'])is bool and data['include_definitions'] is values
 assert data['requested_names']==names and len(names)==len(set(names))
 rows=data['declarations'];assert len(rows)==len(names)and [r['name']for r in rows]==names
 for r in rows:
  assert type(r['levelParamCount'])is int and r['levelParamCount']>=0
  assert r['kind']in['axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor']
  assert isinstance(r['type'],list)and r['type']
  if values:assert r['kind']=='definition'and isinstance(r['definitionValue'],list)and r['definitionValue']
  else:assert r['definitionValue'] is None
 return rows

def review(validation,P,run,ROOT):
 selector=Path('/tmp/wu-structural-interface-selection-v2');names0=json.loads((selector/'types-unicode-names.json').read_text());dropped={f'Hf4Quad.Panel{i}.compact_model'for i in range(40)};assert dropped<=set(names0);names=[n for n in names0 if n not in dropped];assert len(names)==696
 oldmods=json.loads((selector/'types-unicode-modules.json').read_text())['modules']['after'];newmods=[n for n in oldmods if n not in P['retired']]+['Hf4ConstructiveTablePublic'];templatefile=Path('/tmp/wu-public-interface-audit-v2/InterfaceTemplate.lean');assert sha(templatefile)=='26acc89d938f60a51338ad2b9ef5949531a07e2646171b6e4aedab0cd4b243fa';template=templatefile.read_text();captures={str(templatefile):sha(templatefile),str(selector/'types-unicode-names.json'):sha(selector/'types-unicode-names.json'),str(selector/'types-unicode-modules.json'):sha(selector/'types-unicode-modules.json')}
 def name_expr(n):
  out='Name.anonymous'
  for part in n.split('.'):out='(Name.str '+out+' '+json.dumps(part,ensure_ascii=False)+')'
  return out
 def check(label,requested,modules,lib,values):
  source=validation/(label+'.lean');obj=validation/(label+'.olean');output=validation/(label+'.json');text=template.replace('@@MODULE_IMPORTS@@','\n'.join('import '+m for m in modules)).replace('@@NAMES@@','['+', '.join(name_expr(n)for n in requested)+']').replace('@@INCLUDE_DEFINITIONS@@',str(values).lower()).replace('@@OUTPUT_PATH@@',json.dumps(str(output)));assert source.read_text()==text
  j=json.loads((validation/(label+'.invocation.json')).read_text());assert j['command']==[P['lean'],'-j1','-DwarningAsError=true','-DautoImplicit=false','-o',str(obj),str(source)];assert j['environment']['LEAN_SYSROOT']==P['sysroot']and j['environment']['LEAN_PATH']==':'.join([str(lib),*P['package_paths']]);assert obj.is_file()
  for p in [source,obj,output]:captures[str(p)]=sha(p)
  d=json.loads(output.read_text());payload(d,requested,values);return d
 a=check('before-types',names,oldmods,ROOT/'build/lib',False);b=check('after-types',names,newmods,run/'lib',False);assert a==b
 values=[r['name']for r in a['declarations']if r['kind']=='definition'];assert len(values)==183
 a=check('before-values',values,oldmods,ROOT/'build/lib',True);b=check('after-values',values,newmods,run/'lib',True);assert a==b
 return captures
