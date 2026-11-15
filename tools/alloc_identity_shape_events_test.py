import unittest
import lisp_rewrite as lr
from alloc_identity_shape_events import rewrite,PATTERN
class Shape(unittest.TestCase):
 def test_same_order_and_signatures_with_per_operation_events(self):
  old="(make-event (cons 'progn (fn2-alloc-identity-shape-events '((f (x)) (g (y))))))"
  new=rewrite(old)
  forms=lr.parse(new).forms
  self.assertEqual(len(forms),2)
  self.assertTrue(lr.match("(make-event (cons 'progn (fn2-alloc-identity-shape-events '((f (x))))))",forms))
  self.assertTrue(lr.match("(make-event (cons 'progn (fn2-alloc-identity-shape-events '((g (y))))))",forms))
  self.assertEqual(rewrite(new),new)
 def test_no_unrelated_edit(self):
  src='; retained\n(defun f (x) x)'
  self.assertEqual(rewrite(src),src)
 def test_mixed_package_refuses(self):
  one="(make-event (cons 'progn (fn2-alloc-identity-shape-events '((f (x)) (g (y))))))"
  with self.assertRaises(ValueError):rewrite(one+'\n'+one)
if __name__=='__main__':unittest.main()
