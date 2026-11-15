from pathlib import Path
import unittest
import lisp_rewrite as lr
from checkpoint_event_catalog_subject_rewrite import rewrite_catalog_subject
ROOT=Path(__file__).resolve().parents[1]
def shape(n):
 return [shape(x) for x in n.items] if hasattr(n,'items') else n.low
def definition(s,name):
 return lr.match('(defun ?name ?*rest)',lr.parse(s).forms,name=name)[0].node
class Rewrite(unittest.TestCase):
 def test_actual_subject_derives_from_prior_active_reader(self):
  before=(ROOT/'tools/fixtures/event-catalog-active0-before.lisp').read_text()
  transformed=rewrite_catalog_subject(before)
  actual=(ROOT/'books/event-catalog.lisp').read_text()
  for name in ['fn2-event-catalog-subject-descriptor-p','fn2-event-catalog-descriptor-p','fn2-event-catalog-subject-p','fn2-event-catalog-current-p']:
   self.assertEqual(shape(definition(actual,name)),shape(definition(transformed,name)))
 def test_parameter_is_not_a_literal_active_record(self):
  actual=(ROOT/'books/event-catalog.lisp').read_text()
  n=definition(actual,'fn2-event-catalog-subject-p')
  self.assertTrue(lr.match('(fn2-checkpoint-summary-authority-row-complete-p r ?*args)',[n]))
  self.assertTrue(lr.match('(fn2-event-catalog-subject-descriptor-p r 0 ?*args)',[n]))
 def test_active_wrapper_keeps_actual_runtime_base(self):
  n=definition((ROOT/'books/event-catalog.lisp').read_text(),'fn2-event-catalog-current-p')
  self.assertTrue(lr.match('(fn2-event-catalog-subject-p 0 ?*args)',[n]))
  self.assertTrue(lr.match('(= (fn2-checkpoint-restore-events-cut-commit 1 fn2-checkpoint-restore-events) (fn2-commit-root-base-batch 0 fn2-commit-root))',[n]))
if __name__=='__main__':unittest.main()
