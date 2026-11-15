from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class Support(unittest.TestCase):
 def test_existing_driver_observations_byte_unchanged(self):
  old=(ROOT/'tools/fixtures/checkpoint-live-catalog-before-publication-support.lisp').read_text()
  new=(ROOT/'tests/checkpoint-live-publication-support.lisp').read_text()
  for name in ['fn2-clc-published-held-p','fn2-clc-drive-published-held']:
   a=lr.match('(defun '+name+' ?*body)',lr.parse(old).forms,deep=False)[0].node
   b=lr.match('(defun '+name+' ?*body)',lr.parse(new).forms,deep=False)[0].node
   self.assertEqual(old[a.start:a.end],new[b.start:b.end])
 def test_shared_constructor_demands_whole_actual_authorizer(self):
  s=(ROOT/'tests/checkpoint-live-publication-support.lisp').read_text()
  self.assertIn('(fn2-checkpoint-summary-authority-live-source-p ',s)
  self.assertIn('(fn2-clc-full-live-source-p fn2-core)) :held',s)
  self.assertIn('(fn2-commit-admit-keyed ',s)
  self.assertIn('(fn2-ccp-maintenance-entry fn2-core)',s)
 def test_no_seeded_authority_or_assertions(self):
  s=(ROOT/'tests/checkpoint-live-publication-support.lisp').read_text()
  for name in ['assert-event','fn2-csnapshot-put','fn2-checkpoints-put','fn2-checkpoint-publication-put','fn2-checkpoint-selected-source-put']:
   self.assertNotIn('('+name+' ',s)
if __name__=='__main__':unittest.main()
