import copy,unittest
from pathlib import Path
import adopt
class GateTests(unittest.TestCase):
 def setUp(self):
  self.run=Path('/tmp/gate-fixture-not-runtime');self.targets=['New'+str(i)for i in range(18)];self.plan=dict(affected=self.targets,overlay=self.targets);self.labels=['before-types','after-types','before-values','after-values','literal-axioms']+['kernel-'+n for n in self.targets+['WR2ClassicalCertificate']]+['producer-check'];self.report=dict(status=adopt.SUCCESS,run=str(self.run),types=696,values=183,kernels=19,source_proofs=389,reused_original_source_proofs=53,new_source_compilations=336,steps=[dict(label=n,exit_code=0)for n in self.labels])
 def test_exact_shape_only(self):self.assertEqual(len(adopt.gate_report(self.report,self.plan,self.run)),19)
 def test_boolean_exit_rejected(self):
  self.report['steps'][0]['exit_code']=False
  with self.assertRaises(AssertionError):adopt.gate_report(self.report,self.plan,self.run)
 def test_missing_gate_rejected(self):
  self.report['steps'].pop()
  with self.assertRaises(AssertionError):adopt.gate_report(self.report,self.plan,self.run)
 def test_gate_order_rejected(self):
  self.report['steps'][0],self.report['steps'][1]=self.report['steps'][1],self.report['steps'][0]
  with self.assertRaises(AssertionError):adopt.gate_report(self.report,self.plan,self.run)
 def test_proof_provenance_counts_rejected(self):
  for key,value in [('source_proofs',388),('new_source_compilations',389),('reused_original_source_proofs',0)]:
   r=copy.deepcopy(self.report);r[key]=value
   with self.assertRaises(AssertionError):adopt.gate_report(r,self.plan,self.run)
 def test_failure_or_wrong_run_rejected(self):
  r=copy.deepcopy(self.report);r['status']='VALIDATION_FAILED_NOT_ADOPTED'
  with self.assertRaises(AssertionError):adopt.gate_report(r,self.plan,self.run)
  with self.assertRaises(AssertionError):adopt.gate_report(self.report,self.plan,Path('/tmp/other-fixture'))
if __name__=='__main__':unittest.main()
