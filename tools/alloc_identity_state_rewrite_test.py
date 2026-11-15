import unittest
from alloc_identity_state_rewrite import rewrite
class Rewrite(unittest.TestCase):
 def test_formal_and_quoted_signature(self):
  self.assertEqual(rewrite('(defun f (state) state) \'(f state)'), '(defun f (row-state) row-state) \'(f row-state)')
 def test_comments_strings_and_other_identifiers_preserved(self):
  source='; state\n(defun stateful (old-state) (list "state" old-state))'
  self.assertEqual(rewrite(source),source)
 def test_local_bindings_and_idempotence(self):
  once=rewrite('(let ((state 1)) (= state 1))')
  self.assertEqual(once,'(let ((row-state 1)) (= row-state 1))')
  self.assertEqual(rewrite(once),once)
if __name__=='__main__':unittest.main()
