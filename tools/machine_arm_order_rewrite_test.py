from pathlib import Path
import unittest
import lisp_rewrite as lr
import machine_arm_order_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def canon(n):return n.low if hasattr(n,'low') else tuple(canon(x) for x in n.items)
def bodies(s):
 n=lr.match('(defmachine-arms x ?*body)',lr.parse(s).forms)[0].node
 return {x.items[0].low:canon(x) for x in rw.arms_of(n).items}
class Rewrite(unittest.TestCase):
 def test_body_identity_and_comments(self):
  d='(defmachine x :states (:a :b :c) :arms ((:a) (:b) (:c)))'
  i='(defmachine-arms x :declare :arms (\n ; B body\n (:b (:next :c))\n ; A body\n (:a (:next :b))\n (:c (:idle))))'
  out=rw.align(d,i,'x');self.assertEqual(bodies(out),bodies(i));self.assertIn('; B body',out);self.assertIn('; A body',out)
  self.assertEqual([x.items[0].low for x in rw.arms_of(lr.parse(out).forms[0]).items],[':a',':b',':c'])
 def test_missing_body_refused(self):
  with self.assertRaises(ValueError):rw.align('(defmachine x :states (:a :b))','(defmachine-arms x :arms ((:a)))','x')
 def test_actual_master_is_aligned(self):
  d=(ROOT/'books/checkpoint-master-state.lisp').read_text();i=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
  self.assertEqual(i,rw.align(d,i,'fn2-checkpoint-master'))
if __name__=='__main__':unittest.main()
