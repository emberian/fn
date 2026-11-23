#!/usr/bin/env python3
"""Pin actual split consumers under the original upload run declaration."""
from pathlib import Path
import unittest,lisp_rewrite as lr
R=Path(__file__).resolve().parents[1]
class Split(unittest.TestCase):
 def test_original_budget_and_no_hash_lf_retraversal(self):
  s=(R/'books/upload-kind.lisp').read_text()
  self.assertIn(':budget (:bytes 4096',s);self.assertNotIn(':budget (:bytes 6144',s)
  p=lr.parse(R/'books/upload.lisp');m=lr.match('(defun fn2-upload-hash-run ?*body)',p.forms)[0]
  self.assertNotIn('fn2-txn-count-loop',p.text[m.start:m.end])
  f=(R/'books/upload-feed.lisp').read_text()
  self.assertIn('fn2-feed-emitted-lf',f);self.assertIn('fn2-upload-feed-counted',f)
 def test_private_keep_store_phase_connection(self):
  s=(R/'books/assembly-callbacks-d-upload.lisp').read_text()
  self.assertIn('(fn2-upload-block-private-op-events)',s)
  for phase,names in [('stream-block',['fn2-upload-block-hash-keep','fn2-upload-block-cv-keep','fn2-upload-private-result-store']),
                      ('stream-root-write',['fn2-upload-root-hash-keep','fn2-upload-private-result-store'])]:
   m=lr.match('(:'+phase+' :on-refusal ?*body)',lr.parse(s).forms)[0];p=s[m.start:m.end]
   for name in names:self.assertIn(name,p)
   self.assertNotIn('*fn2-upload-block-work-bytes*',p)
   self.assertNotIn('fn2-upload-block-hash row-lslot',p)
 def test_private_frame_and_interference_controls(self):
  s=(R/'books/upload-block-private.lisp').read_text()
  for x in ['*fn2-fc-result*','fn2-upload-b3-update-preserves-private-result',
            'fn2-upload-scratch-hash-preserves-other-digest-stripe','fn2-upload-hash-private-preserves-source-b3-columns']:
   self.assertIn(x,s)
  t=(R/'tests/upload-block-private-unit.lisp').read_text()
  for x in ['fn2-upload-hash-private-children','fn2-block-hash-into','fn2-upload-cv-private-children']:
   self.assertIn(x,t)
 def test_old_producer_is_unreachable_stop_not_second_implementation(self):
  s=(R/'books/assembly-callbacks-d-upload.lisp').read_text();p=lr.parse(s)
  for phase in ['store','stored-hash','location-hash','store-write','store-wrote','store-fence','store-fenced']:
   self.assertEqual(len(lr.match('(:'+phase+' (:stop :machine-phase))',p.forms)),1)
   self.assertNotIn('(:next :'+phase+')',s)
  self.assertIn('unreachable-in-composition',s)
 def test_namespace_capacity_uses_real_slot_and_name_bounds(self):
  s=(R/'books/txn-kind.lisp').read_text()
  self.assertIn('(* *fn2-txn-groups-max* *fn2-txn-name-span-max*)',s)
  self.assertIn('(<= *fn2-txn-names-bytes-max* *fn2-upload-body-window-bytes*)',s)
  self.assertIn('(unsigned-byte-p 8 nlen)',(R/'books/txn.lisp').read_text())
if __name__=='__main__':unittest.main()
