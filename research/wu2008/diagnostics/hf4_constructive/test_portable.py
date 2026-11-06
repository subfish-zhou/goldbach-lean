from pathlib import Path
import hashlib,importlib.util,json,shutil,tempfile,unittest
from unittest.mock import patch
import produce
ROOT=Path(__file__).resolve().parent
class PortableTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.constructive=produce.generate('constructive');cls.checkpoint=produce.generate('checkpoint')
 def test_exact17_both_routes(self):
  golden=json.loads((ROOT/'frozen/golden.json').read_text())
  for route,pair in [('constructive',self.constructive),('checkpoint',self.checkpoint)]:
   files,report=pair;self.assertEqual(len(files),17);self.assertEqual({n.removesuffix('.lean'):hashlib.sha256(b).hexdigest()for n,b in files.items()},golden['routes'][route]['modules']);self.assertEqual(json.loads(report)['canonical_fields_sha256'],golden['canonical_fields_sha256'])
 def test_constructive_has_no_stale_inverse_namespace(self):
  counter=produce.load('frozen_counter',ROOT/'lib/source_counter.py')
  for n,b in self.constructive[0].items():self.assertNotIn('InverseDag',counter.code_only(b.decode()),n)
 def test_public_formal_headers_remain40_original(self):
  import re
  actual=re.findall(r'theorem mass_bounds.*?(?= := by)',self.constructive[0]['Hf4ConstructiveTablePublic.lean'].decode(),re.S)
  original=json.loads((ROOT/'frozen/original-headers.json').read_text());self.assertEqual(actual,[original[str(i)]['header']for i in range(40)])
 def test_no_retired_modules_generated(self):
  retired=set(json.loads((ROOT/'frozen/golden.json').read_text())['retired_modules_not_generated'])
  for files,_ in [self.constructive,self.checkpoint]:self.assertFalse(set(n.removesuffix('.lean')for n in files)&retired)
 def test_header_origin_exact40(self):
  h=json.loads((ROOT/'frozen/original-headers.json').read_text());origin=json.loads((ROOT/'frozen/header-origin.json').read_text());self.assertEqual(len(h),40);self.assertEqual(len(origin['preV5_original_source_sha256']),14)
  for i,row in h.items():self.assertEqual(hashlib.sha256(row['header'].encode()).hexdigest(),origin['exact40header_sha256'][f'Hf4Quad.Panel{i}.mass_bounds'])
 def relocated(self,path):
  dest=path/'relocated package with spaces';shutil.copytree(ROOT,dest,ignore=shutil.ignore_patterns('__pycache__'));spec=importlib.util.spec_from_file_location('relocated_portable',dest/'produce.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return dest,m
 def test_relocated_read_fence_no_old_sources(self):
  with tempfile.TemporaryDirectory()as d:
   dest,m=self.relocated(Path(d));rb=Path.read_bytes;rt=Path.read_text
   def bytes_read(p,*args,**kw):
    if not p.resolve().is_relative_to(dest):raise AssertionError('external producer read '+str(p))
    return rb(p,*args,**kw)
   def text_read(p,*args,**kw):
    if not p.resolve().is_relative_to(dest):raise AssertionError('external producer read '+str(p))
    return rt(p,*args,**kw)
   with patch.object(Path,'read_bytes',bytes_read),patch.object(Path,'read_text',text_read):
    self.assertEqual(m.generate('constructive'),self.constructive);self.assertEqual(m.generate('checkpoint'),self.checkpoint)
 def test_header_mutation_rejected(self):
  with tempfile.TemporaryDirectory()as d:
   dest,m=self.relocated(Path(d));p=dest/'frozen/original-headers.json';p.write_text(p.read_text().replace('17511388157','17511388158',1))
   with self.assertRaisesRegex(AssertionError,'frozen input differs'):m.generate('constructive')
 def test_numeric_formula_mutation_rejected(self):
  with tempfile.TemporaryDirectory()as d:
   dest,m=self.relocated(Path(d));p=dest/'lib/legacy_hf4.py';p.write_text(p.read_text().replace('D=10**14','D=10**13',1))
   with self.assertRaisesRegex(AssertionError,'frozen input differs'):m.generate('checkpoint')
 def test_extra_input_rejected(self):
  with tempfile.TemporaryDirectory()as d:
   dest,m=self.relocated(Path(d));(dest/'frozen/extra.json').write_text('{}')
   with self.assertRaisesRegex(AssertionError,'input inventory'):m.verify_inputs()
if __name__=='__main__':unittest.main()
