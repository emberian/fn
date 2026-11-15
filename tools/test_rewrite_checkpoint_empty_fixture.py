#!/usr/bin/env python3
import unittest
from rewrite_checkpoint_empty_fixture import rewrite
class RewriteFixture(unittest.TestCase):
    def test_exact_scope(self):
        s='(in-package "ACL2")\n(defun x (p) (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication))\n; tail\n'
        out=rewrite(s)
        self.assertIn('(fn2-checkpoint-test-empty-publication fn2-checkpoint-publication)',out)
        self.assertTrue(out.endswith('; tail\n'))
        self.assertEqual(out,rewrite(out))
    def test_zero_and_quotes(self):
        s='''(in-package "ACL2")
(defun z (p) (fn2-checkpoint-publication-init 0 fn2-checkpoint-publication))
'(fn2-checkpoint-publication-init 1 fn2-checkpoint-publication)
(quote (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication))
'''
        self.assertEqual(s,rewrite(s))
if __name__=='__main__':unittest.main()
