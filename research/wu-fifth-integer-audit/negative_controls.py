#!/usr/bin/env python3
"""Read-only mutations: source scopes, contracts and the actual Nat interpreter."""
from pathlib import Path
import json
from preservation import audit,SRC,HERE,PREFIX
from lean_nat import evaluator
original={str(p.relative_to(SRC)):p.read_text() for p in SRC.rglob('*.lean')}
cases=[('support',PREFIX+'IntegerData.lean','if i < 1024','if i < 1025'),('ratio_integer',PREFIX+'IntegerData.lean','265400*','265401*'),('cPoly_pair',PREFIX+'IntegerPolynomial.lean','1451520*D','1451521*D'),('public_payment',PREFIX+'InitialPayments.lean','1000000000000','1000000000001'),('public_total',PREFIX+'MiddlePayments.lean','661191362320992','661191362320993'),('root_contract',PREFIX+'TerminalRoot.lean','i < 1024','i < 1023'),('sum_index',PREFIX+'MiddleSums.lean','middlePaymentBlockSum 0','middlePaymentBlockSum 1'),('frozen_final','WR2ClassicalCertificate.lean','theorem','lemma')]
results=[]
for label,name,before,after in cases:
 assert before in original[name],label
 modified=dict(original);modified[name]=modified[name].replace(before,after,1)
 try:audit(modified)
 except AssertionError as e:results.append({'case':label,'rejected':True,'reason':str(e)})
 else:raise AssertionError(('escaped audit',label))
# Specifically exercise interpretation of actual source polynomial coefficients,
# independently of the unchanged-Horner source hash guard.
modified=dict(original);name='WR2IntegerLogHorner.lean';assert '334639305*Q^11' in modified[name]
modified[name]=modified[name].replace('334639305*Q^11','334639306*Q^11',1)
assert evaluator(modified)('middle',0)!=evaluator(original)('middle',0)
results.append({'case':'actual_Horner_AST_coefficient','rejected':True,'reason':'Actual-source interpreted payment changes'})
(HERE/'negative-controls.json').write_text(json.dumps(results,indent=2)+'\n');print('PASS',len(results),'negative controls; production sources unmodified')
