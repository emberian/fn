from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from cns_next_observation_frames import transform,pairs,declaration
class Frames(unittest.TestCase):
 def test_exact_sequence_and_idempotence(self):
  s=(ROOT/'books/cns-source-raw.lisp').read_text();ps=pairs(s)
  self.assertEqual(len(ps),14)
  self.assertEqual(set(ps),{(r,w) for r,ws in [('unit-index',['offset','unit-copied']),('manifest-index',['offset','unit-copied','unit-index']),('manifest-loaded-index',['offset','unit-copied','unit-index','manifest-index']),('total',['offset','unit-copied','unit-index','manifest-index','manifest-stage'])] for w in ws})
  self.assertEqual(transform(s),(s,0))
  bare=s
  for pair in ps:bare=bare.replace(declaration(*pair)+'\n','')
  made,n=transform(bare);self.assertEqual(n,14);self.assertEqual(pairs(made),ps)
 def test_missing_and_wrong_pair_refused(self):
  s=(ROOT/'books/cns-source-raw.lisp').read_text();pair=pairs(s)[0]
  with self.assertRaises(AssertionError):transform(s.replace(declaration(*pair)+'\n',''))
  with self.assertRaises(AssertionError):transform(s.replace(declaration(*pair),declaration(pair[0],'phase')))
if __name__=='__main__':unittest.main()
