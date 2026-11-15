import unittest
from pathlib import Path
import run_page_pool_frame_hints as h
class FrameHints(unittest.TestCase):
 def setUp(self):self.before=(Path(__file__).parent/'fixtures/run-page-pool-frame-before.lisp').read_text()
 def test_exact_proof_only_insertions(self):
  after=h.transform(self.before)
  self.assertEqual(after.count(':hints'),22)
  
  for table in h.TABLES:after=after.replace('\n'+h.hint(table),'')
  self.assertEqual(after,self.before)
 def test_idempotent(self):
  once=h.transform(self.before);self.assertEqual(h.transform(once),once)
 def test_existing_hint_requires_composition(self):
  with self.assertRaises(ValueError):h.transform('(fn2-pool-preserves f (x) :hints (("Goal" :use other)))')
if __name__=='__main__':unittest.main()
