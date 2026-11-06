from pathlib import Path
import copy,json,unittest
import export_review
class ExportReviewTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  b=Path('/tmp/wu-hf4-uniform-interface-v1/after');cls.types=json.loads((b/'UniformTypes.json').read_text());cls.values=json.loads((b/'UniformData.json').read_text())
 def test_actual_previously_compiled_payloads(self):
  for d,mode in [(self.types,False),(self.values,True)]:self.assertEqual(len(export_review.payload(d,d['requested_names'],mode)),len(d['requested_names']))
 def test_empty_equal_payload_not_enough(self):
  d=copy.deepcopy(self.types);d['declarations']=[]
  with self.assertRaises(AssertionError):export_review.payload(d,self.types['requested_names'],False)
 def test_wrong_requested_names_rejected(self):
  d=copy.deepcopy(self.types);d['requested_names']=list(reversed(d['requested_names']))
  with self.assertRaises(AssertionError):export_review.payload(d,self.types['requested_names'],False)
 def test_hidden_value_omission_rejected(self):
  d=copy.deepcopy(self.values);d['declarations'][0]['definitionValue']=None
  with self.assertRaises(AssertionError):export_review.payload(d,self.values['requested_names'],True)
 def test_wrong_definition_kind_rejected(self):
  d=copy.deepcopy(self.values);d['declarations'][0]['kind']='theorem'
  with self.assertRaises(AssertionError):export_review.payload(d,self.values['requested_names'],True)
 def test_boolean_universe_count_rejected(self):
  d=copy.deepcopy(self.types);d['declarations'][0]['levelParamCount']=False
  with self.assertRaises(AssertionError):export_review.payload(d,self.types['requested_names'],False)
if __name__=='__main__':unittest.main()
