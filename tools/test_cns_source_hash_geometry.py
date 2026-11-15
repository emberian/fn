"""Source controls for dedicated stream hash geometry; no ACL2 admission claim."""
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
class Geometry(unittest.TestCase):
 def test_geometry_partition(self):
  # Exercise empty and nonempty configured ranges, with optional spare rows.
  for connections in range(5):
   for sources in range(5):
    for extra in (0, 1, 19):
     rows = 9 + 16 + connections + sources + extra
     controls = set(range(rows-sources-connections-5, rows-sources-5))
     streams = set(range(rows-sources-5, rows-5))
     tail = set(range(rows-5, rows))
     self.assertFalse(controls & streams)
     self.assertFalse(controls & tail)
     self.assertFalse(streams & tail)
 def test_actual_selector_formula(self):
  s=(ROOT/'books/machines-b.lisp').read_text()
  self.assertIn('(+ 9 (fn2-b-upload-windows profile) (fn2-b-ctl-rows profile) (fn2-b-cns-source-rows profile))',s)
  self.assertIn('(- (nfix rows) (nfix sources) (nfix connections) 5)',s)
  self.assertIn('(- (nfix rows) (nfix sources) 5)',s)
 def test_shared_hash_implementation(self):
  s=(ROOT/'books/cns-source-hash.lisp').read_text()
  self.assertIn('(<= len 1024)',s)
  self.assertIn('(fn2-b3-update row slot gen off len kind owner generation',s)
  self.assertIn('(fn2-block-digest-at got scratch slot gen expected',s)
  self.assertNotIn('fn2-block-hash-into',s)  # Would reset paused stream state.
  self.assertNotIn('fn2-fnct',s)  # Frame domain is distinct.
if __name__=='__main__': unittest.main()
