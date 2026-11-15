#!/usr/bin/env python3
"""Existing upload storage result branches retain ownership on ambiguity."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class UploadUncertainty(unittest.TestCase):
 def test_issued_failures_never_enter_sealed_drain(self):
  p=lr.parse(ROOT/'books/assembly-callbacks-d-upload.lisp')
  for phase in ['stream-wrote','stream-fenced','stream-root-wrote','stream-root-fenced','stream-refuse-fenced']:
   node=lr.match('(:'+phase+' :on-refusal ?*body)',p.forms)[0].node
   failed=lr.match('((not (and ?*conditions)) (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain) ?*tail)',[node])
   self.assertEqual(len(failed),1,phase)
   body=p.text[failed[0].start:failed[0].end]
   self.assertIn('*fn2-outcome-done*',body)
   self.assertNotIn('(:next :sealed)',body)
   self.assertNotIn('fn2-core-release',body)
  self.assertEqual(len(lr.match('(:uncertain (:stop :upload-uncertain))',p.forms)),1)
 def test_kind_retains_all_resources_and_stop(self):
  s=(ROOT/'books/upload-kind.lisp').read_text()
  self.assertIn(':stops (:upload-uncertain)',s)
  self.assertIn('(:uncertain :upload-row :chunk-window (:storage-window :while (lease :held)))',s)
  self.assertEqual(s.count('(:uncertain)'),1)
  self.assertTrue(lr.match('(defconst *fn2-upload-word-uncertain* ?v)',lr.parse(ROOT/'books/upload.lisp').forms))
  self.assertFalse(lr.match('(defconst *fn2-upload-word-uncertain* ?v)',lr.parse(ROOT/'books/txn.lisp').forms))
 def test_fault_controls_use_real_issued_packets(self):
  p=lr.parse(ROOT/'tests/upload-uncertainty-served-unit.lisp')
  for name in ['fn2-uui-target','fn2-cw-adapter-one','fn2-turn','fn2-sim-take-prefix',
               'fn2-sim-native-stage','fn2-sim-native-post','fn2-uui-ownedp','fn2-uui-resources']:
   self.assertTrue(lr.match('('+name+' ?*args)',p.forms),name)
  text=p.text
  self.assertNotIn('fn2-upload-put-core',text)
  self.assertNotIn('fn2-cw-post ',text)
  for fault in ['*fn2-fault-write-io*','*fn2-fault-short-write*','*fn2-fault-flush-io*']:
   self.assertIn(fault,text)
 def test_preissue_refusals_still_distinct(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-init :on-refusal');b=s.index('(:stream-receiving :on-refusal',a);s=s[a:b]
  self.assertIn('*fn2-upload-word-unaffordable*',s)
  self.assertIn('fn2-upload-start-discard',s)
  self.assertNotIn('*fn2-upload-word-uncertain*',s)
if __name__=='__main__':unittest.main()
