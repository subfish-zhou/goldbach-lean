from pathlib import Path
import json,os,shutil,tempfile,unittest
from unittest.mock import patch
import core
class TransactionTests(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);core.ROOT=Path(self.temp.name)/'root';core.ROOT.mkdir();self.tx=Path(self.temp.name)/'tx';self.tx.mkdir();self.before={'src/A.lean':b'old A','src/Deleted.lean':b'old deleted','src/New.lean':None,'build/STATUS.json':b'{"status":"passed"}'};self.after={'src/A.lean':b'new A','src/Deleted.lean':None,'src/New.lean':b'new entry','build/STATUS.json':b'{"status":"pending"}'};core.ALLOWED=frozenset(self.before);self.journal={'phase':'prepared','items':[]}
  for name,b in self.before.items():
   p=core.ROOT/name
   if b is not None:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);q=self.tx/'backup'/name;q.parent.mkdir(parents=True,exist_ok=True);os.link(p,q)
   new=self.after[name];q=self.tx/'stage'/name
   if new is not None:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(new)
   self.journal['items'].append(dict(target=name,old_sha256=core.sha(p)if b is not None else None,new_sha256=core.sha(q)if new is not None else None))
 def assert_bytes(self,expected):
  for name,b in expected.items():
   p=core.ROOT/name;self.assertEqual(p.read_bytes()if p.exists()else None,b)
 def test_exact_commit(self):
  core.commit_items(self.tx,self.journal,lambda:self.assert_bytes(self.after));self.assert_bytes(self.after);self.assertEqual(json.loads((self.tx/'journal.json').read_text())['phase'],'committed_pending_production_verification')
 def test_failed_verification_restores_deletion_addition_and_metadata(self):
  def fail():raise RuntimeError('post-install check failed')
  with self.assertRaisesRegex(RuntimeError,'post-install'):core.commit_items(self.tx,self.journal,fail)
  self.assert_bytes(self.before);self.assertEqual(json.loads((self.tx/'journal.json').read_text())['phase'],'rolled_back')
 def test_partial_replace_failure_rolls_back(self):
  replace=os.replace
  def fail(src,dst):
   if Path(src)==self.tx/'stage/src/New.lean':raise OSError('injected stage failure')
   return replace(src,dst)
  with patch.object(core.os,'replace',fail):
   with self.assertRaisesRegex(OSError,'injected'):core.commit_items(self.tx,self.journal,lambda:None)
  self.assert_bytes(self.before)
 def test_corrupt_backup_rejected_before_restore(self):
  self.journal['phase']='mutating';core.save(self.tx/'journal.json',self.journal);p=self.tx/'backup/src/A.lean';p.unlink();p.write_bytes(b'corrupt')
  with self.assertRaisesRegex(RuntimeError,'backup changed'):core.restore(self.tx)
  self.assert_bytes(self.before)
 def test_path_escape_and_unlisted_target_rejected(self):
  for s in ['../x','/tmp/x','src/Unlisted.lean']:
   with self.assertRaises(RuntimeError):core.valid_target(s)
 def test_symlink_target_rejected(self):
  p=core.ROOT/'src/New.lean';p.symlink_to('/tmp')
  with self.assertRaises(RuntimeError):core.valid_target('src/New.lean')
if __name__=='__main__':unittest.main()
