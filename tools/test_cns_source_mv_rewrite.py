from pathlib import Path
import json,unittest
import cns_source_mv_rewrite as m
ROOT=Path(__file__).resolve().parents[1]
class Rewrite(unittest.TestCase):
 def test_actual_class(self):
  f=json.loads((ROOT/'tests/fixtures/cns_source_mv_returns.json').read_text())
  actual,count=m.rewrite(f['before']);self.assertEqual(count,7);self.assertEqual(actual,f['after'])
  self.assertEqual(actual,(ROOT/'books/cns-source-manifest.lisp').read_text())
 def test_idempotent(self):
  s=(ROOT/'books/cns-source-manifest.lisp').read_text();self.assertEqual(m.rewrite(s),(s,0))
 def test_abi_refusal(self):
  with self.assertRaises(ValueError):m.rewrite('(mv :bad (fn2-cns-sources-set-phase s p other))')
if __name__=='__main__':unittest.main()
