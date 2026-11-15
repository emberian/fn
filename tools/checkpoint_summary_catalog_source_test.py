"""Active/pending catalog metadata and nonce controls, without ACL2 execution."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class Catalog(unittest.TestCase):
 def test_actual_two_controls_one_source_directory(self):
  forms=lr.parse(ROOT/'books/boot-kind.lisp').forms
  self.assertTrue(lr.match('(fn2-checkpoint-summary-init (if (fn2-profile-get :image-boot profile) 2 0) fn2-checkpoint-summary)',forms))
  decl=lr.match('(defcolumns fn2-checkpoint-summary ?*body)',lr.parse(ROOT/'books/checkpoint-summary-state.lisp').forms)[0].node
  self.assertTrue(lr.match('(array (unsigned-byte 8) (64))',[decl]))
 def test_cold_constructor_consumes_monotone_tag(self):
  forms=lr.parse(ROOT/'books/checkpoint-summary-catalog.lisp').forms
  fn=lr.match('(defun fn2-checkpoint-summary-begin ?*body)',forms)[0].node
  self.assertTrue(lr.match('(tag (fn2-checkpoint-summary-fresh-tag fn2-checkpoint-summary))',[fn]))
  self.assertTrue(lr.match('(update-fn2-checkpoint-summary-next-tag tag fn2-checkpoint-summary)',[fn]))
  self.assertTrue(lr.match('((unless (unsigned-byte-p 60 tag)) (mv :tag-exhausted fn2-checkpoint-summary))',[fn]))
 def test_both_controls_and_frontier_constrain_nonce(self):
  fn=lr.match('(defun fn2-checkpoint-summary-fresh-tag ?*body)',lr.parse(ROOT/'books/checkpoint-summary-state.lisp').forms)[0].node
  for pattern in ['(fn2-checkpoint-summary-next-tag fn2-checkpoint-summary)',
                  '(fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary)',
                  '(fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary)']:
   self.assertTrue(lr.match(pattern,[fn]))
 def test_descriptor_rows_are_disjoint(self):
  fn=lr.match('(defun fn2-checkpoint-summary-descriptor-word ?*body)',lr.parse(ROOT/'books/checkpoint-summary-state.lisp').forms)[0].node
  self.assertTrue(lr.match('(at (+ (* 32 r) (* 4 i)))',[fn]))
  self.assertTrue(lr.match('(< r 2)',[fn]));self.assertTrue(lr.match('(< i 8)',[fn]))
if __name__=='__main__':unittest.main()
