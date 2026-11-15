"""Preserve physical query ownership through the actual cleanup wrapper class."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import successor_resolve_owner_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def tree(n):return n.low if hasattr(n,'low') else tuple(tree(x) for x in n.items)
class Owner(unittest.TestCase):
 def test_rewrite_is_exact_and_idempotent(self):
  before=(ROOT/'tools/fixtures/successor-resolve-owner-before.lisp').read_text()
  after,count=rw.transform(before)
  self.assertEqual(count,6)
  actual=(ROOT/'books/machines-c-successor.lisp').read_text()
  for f in lr.parse(after).forms:
   matches=lr.match('('+f.items[0].low+' '+f.items[1].low+' ?*rest)',lr.parse(actual).forms,deep=False)
   self.assertEqual(len(matches),1)
   self.assertEqual(tree(f),tree(matches[0].node))
  self.assertEqual(rw.transform(after),(after,0))
 def test_actual_owner_flows_to_physical_cursor(self):
  s=(ROOT/'books/machines-c-successor.lisp').read_text()
  for caller,callee in [('fn2-succ-resolve','fn2-succ-resolve-raw'),('fn2-succ-resolve-raw','fn2-succ-resolve-step'),('fn2-succ-resolve-step','fn2-succ-resolve-next')]:
   f=lr.match('(defun '+caller+' ?*body)',lr.parse(s).forms,deep=False)[0].node
   calls=lr.match('('+callee+' ?*args)',[f.items[-1]])
   self.assertEqual(len(calls),1)
   self.assertEqual([x.low for x in calls[0].node.items[4:7]],['qk','qs','qg'])
  core=(ROOT/'books/machines-c-bind.lisp').read_text()
  self.assertEqual(len(lr.match('(fn2-succ-resolve tx budget b0 qk qs qg ?*rest)',lr.parse(core).forms)),1)
 def test_missing_owner_and_cleanup_are_not_substituted(self):
  s=(ROOT/'books/machines-c-successor.lisp').read_text()
  self.assertEqual(len(lr.match('(fn2-run-cursor-start-installed tx r (+ b0 *fn2-idc-rb*) qk qs qg ?*rest)',lr.parse(s).forms)),1)
  self.assertIn('(fn2-succ-source-values-scalar-p nv nk sid)',s)
  self.assertIn('(fn2-succ-clear-ref-rows *fn2-run-reader-fields* (+ b0 *fn2-idc-rb*) fn2-fields)',s)
  with self.assertRaises(ValueError):rw.transform(s.replace('(defun fn2-succ-resolve-raw (tx budget b0 qk qs qg fn2-succ-txns','(defun fn2-succ-resolve-raw (tx budget b0 0 0 0 fn2-succ-txns',1))
if __name__=='__main__':unittest.main()
