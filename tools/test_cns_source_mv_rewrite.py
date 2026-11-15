from pathlib import Path
import json,unittest
import cns_source_mv_rewrite as m
ROOT=Path(__file__).resolve().parents[1]
class Rewrite(unittest.TestCase):
 def test_actual_class(self):
  f=json.loads((ROOT/'tests/fixtures/cns_source_mv_returns.json').read_text())
  actual,count=m.rewrite(f['before']);self.assertEqual(count,7);self.assertEqual(actual,f['after'])
  current=(ROOT/'books/cns-source-manifest.lisp').read_text()
  # Later guard changes need not repeat this whole-book rewrite. Retain each
  # exact rewritten return arm in the actual source, with no direct MV setter.
  cases=[]
  def visit(n):
   if not isinstance(n,m.lr.Lst):return
   if m.head(n)=='let' and len(n.items)==3 and m.head(n.items[2])=='mv':
    bindings=n.items[1]
    if isinstance(bindings,m.lr.Lst) and len(bindings.items)==1 and isinstance(bindings.items[0],m.lr.Lst):
     b=bindings.items[0]
     if len(b.items)==2 and m.head(b.items[1])=='fn2-cns-sources-set-phase':cases.append(actual[n.start:n.end])
   for x in n.items:visit(x)
  for form in m.lr.parse(actual).forms:visit(form)
  self.assertEqual(len(cases),7)
  for case in cases:self.assertIn(case,current)
 def test_idempotent(self):
  s=(ROOT/'books/cns-source-manifest.lisp').read_text();self.assertEqual(m.rewrite(s),(s,0))
 def test_abi_refusal(self):
  with self.assertRaises(ValueError):m.rewrite('(mv :bad (fn2-cns-sources-set-phase s p other))')
if __name__=='__main__':unittest.main()
