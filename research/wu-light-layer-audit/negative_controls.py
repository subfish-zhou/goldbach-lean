#!/usr/bin/env python3
"""Mutation tests of preservation checks; modifies only in-memory strings."""
import importlib.util,json
from pathlib import Path
here=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('preservation',here/'preservation.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
original={str(p.relative_to(m.SRC)):p.read_text() for p in m.SRC.rglob('*.lean')}
cases=[
 ('payment_budget','WR2ClassicalFourthBPayBatch000.lean','maxHeartbeats 4000000','maxHeartbeats 4000001'),
 ('payment_statement','WR2ClassicalFourthBPayBatch000.lean','j : Fin 256','j : Fin 255'),
 ('payment_proof','WR2ClassicalFourthBPayBatch000.lean','by_cases hb','by_cases hacked'),
 ('aggregate_print','WR2ClassicalFourthAllBPay.lean','#print axioms','#check'),
 ('aggregate_reference','WR2ClassicalFourthAllBPay.lean','BPay_block_000','BPay_block_001'),
 ('moved_nat','WR2ClassicalFourthIntegerConditions.lean','56*1000000000000000','55*1000000000000000'),
 ('moved_rational','WR2ExactRationalLogData.lean','^25/','^24/'),
 ('frozen_data','WR2ClassicalFourthDataBq.lean','10540','10539'),
 ('import_only_body','WR2ClassicalCumulativeTable.lean','namespace WuPaper','namespace Other'),
]
results=[]
for label,name,before,after in cases:
 assert before in original[name],label
 altered=dict(original);altered[name]=altered[name].replace(before,after,1)
 try:m.audit(altered)
 except AssertionError as e:results.append({'case':label,'rejected':True,'reason':str(e)})
 else:raise AssertionError(('mutation escaped',label))
(here/'negative-controls.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS',len(results),'in-memory negative controls; formal sources unchanged')
