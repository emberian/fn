#!/usr/bin/env python3
"""Source transformation controls; no ACL2 execution."""
from pathlib import Path
import sys, unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from rewrite_root1_reader_outputs import transform, ADDITIONS, CHILDREN
class Rewrite(unittest.TestCase):
 def source(self):
  return "(defconst *fn2-checkpoint-root1-children* '(fn2-checkpoint-root1))\n(defconst *fn2-checkpoint-root1-outputs* '("+'\n'.join('('+op+' fn2-checkpoint-root1)' for op in ADDITIONS)+'))'
 def test_exact_mutating_subsets_and_idempotence(self):
  out,n=transform(self.source());self.assertEqual(n,6)
  for c in CHILDREN:self.assertIn(c,out)
  self.assertEqual(transform(out),(out,0))
 def test_missing_callback_refused(self):
  with self.assertRaises(ValueError):transform(self.source().replace('(fn2-checkpoint-root1-work fn2-checkpoint-root1)',''))
 def test_actual_mv_limit_refused(self):
  wide=' '.join('fn2-wide-'+str(i) for i in range(30))
  with self.assertRaises(ValueError):transform(self.source().replace('(fn2-checkpoint-root1-read fn2-checkpoint-root1)',f'(fn2-checkpoint-root1-read {wide})'))
if __name__=='__main__':unittest.main()
