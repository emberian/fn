#!/usr/bin/env python3
"""Source controls for the connected rolling path; not runtime qualification."""
from pathlib import Path
import subprocess
import unittest
import lisp_rewrite as lr
from upload_stream_schema_rewrite import transform
ROOT=Path(__file__).resolve().parents[1]
class RollingSource(unittest.TestCase):
 def test_schema_is_single_checked_generator_expansion(self):
  old=subprocess.check_output(['git','show','bd3eff96a:books/upload-kind.lisp'],cwd=ROOT,text=True)
  self.assertEqual(transform(old),(ROOT/'books/upload-kind.lisp').read_text())
 def test_actual_identity_routes_to_controller(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  self.assertIn('((:ok) (:set (txn tid) (txn-gen tgen)) (:next :stream-init)',s)
  for phase in ['stream-init','stream-receiving','stream-stage','stream-write','stream-wrote','stream-block',
                'stream-fence','stream-fenced','stream-final','stream-repack','stream-root-write',
                'stream-root-wrote','stream-root-fence','stream-root-fenced']:
   self.assertEqual(len(lr.match(f'(:{phase} :on-refusal ?*body)',lr.parse(ROOT/'books/assembly-callbacks-d-upload.lisp').forms)),1)
 def test_reset_follows_actual_covering_fence_and_return(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-fenced :on-refusal');b=s.index('(:stream-final :on-refusal',a);s=s[a:b]
  for p in ['*fn2-event-fence-result*','*fn2-outcome-done*','row-pending 0','fn2-upload-stream-page-ready-p','fn2-upload-stream-reset']:
   self.assertIn(p,s)
  self.assertLess(s.index('row-pending 0'),s.index('fn2-upload-stream-reset'))
  self.assertLess(s.index('fn2-upload-stream-page-ready-p'),s.index('fn2-upload-stream-reset'))
 def test_no_input_capacity_ceiling_or_context_alias(self):
  p=lr.parse(ROOT/'books/upload.lisp');m=lr.match('(defun fn2-upload-bound ?*body)',p.forms)[0]
  body=p.text[m.start:m.end];self.assertNotIn('min',body);self.assertIn('(nfix max)',body)
  s=(ROOT/'books/upload-stream-stage.lisp').read_text()
  self.assertIn('(length (min *fn2-upload-hash-bytes*',s)
  self.assertIn('(fn2-upload-stored-hasher id fn2-core)',s)
  self.assertIn('(- stream-end body-fill)',s)
 def test_original_identity_and_root_are_distinct(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-init :on-refusal');b=s.index('(:stream-receiving :on-refusal',a)
  self.assertIn('fn2-upload-put-mid row-lslot row-lgen row-pepoch row-palloc',s[a:b])
  a=s.index('(:stream-final :on-refusal');b=s.index('(:stream-repack :on-refusal',a)
  self.assertIn('(rootext e) (rootepoch ep) (rootalloc al)',s[a:b]);self.assertNotIn('(pext e)',s[a:b])
  t=(ROOT/'books/txn.lisp').read_text();self.assertEqual(t.count('(fn2-upload-location-tuple row-upload row-upload-gen)'),2)
 def test_stream_issued_failures_retain_resources(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  for phase,nextphase in [('stream-wrote','stream-block'),('stream-fenced','stream-final'),
                          ('stream-root-wrote','stream-root-fence'),('stream-root-fenced','retired')]:
   a=s.index('(:'+phase+' :on-refusal');b=s.index('\n  (:',a+4);part=s[a:b]
   self.assertIn('*fn2-upload-word-uncertain*',part);self.assertIn('(:next :uncertain)',part)
   self.assertNotIn('fn2-core-release',part);self.assertNotIn('payload-settle',part)
 def test_bounded_drain_uses_provisional_leaders_then_distinct_handles(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-drain :on-refusal');b=s.index('(:retired (:idle))',a);s=s[a:b]
  self.assertIn('fn2-upload-stream-settle-next',s)
  self.assertIn('fn2-upload-payload-settle row-cext row-cepoch row-calloc',s)
  self.assertIn('fn2-upload-payload-settle row-rootext row-rootepoch row-rootalloc',s)
  self.assertNotIn('fn2-upload-payload-settle row-pext',s)
  self.assertLess(s.index('fn2-upload-stream-settle-next'),s.index('fn2-upload-payload-settle row-cext'))
  self.assertLess(s.index('fn2-upload-payload-settle row-rootext'),s.index('fn2-upload-page-release'))
 def test_definite_refusal_fences_before_any_cleanup(self):
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-refuse-fence :on-refusal');b=s.index('(:stream-drain :on-refusal',a);s=s[a:b]
  for token in ['fn2-issue-fence','*fn2-event-fence-result*','*fn2-outcome-done*','row-pending 0',
                'fn2-upload-stream-page-ready-p','(:next :uncertain)']:
   self.assertIn(token,s)
  self.assertNotIn('payload-settle',s)
 def test_actual_repeated_window_controls_have_no_state_setters(self):
  s=(ROOT/'tests/upload-rolling-served-unit.lisp').read_text()
  for token in ['fn2-turn','fn2-cw-adapter-one','fn2-upload-state-stream-fenced*',
                'fn2-upload-row-stream-resets','fn2-pool-out-count','32768','12288','12289']:
   self.assertIn(token,s)
  self.assertNotIn('fn2-machine-write-',s)
  self.assertNotIn('fn2-upload-put ',s)
 def test_new_books_parse(self):
  for name in ['upload-stream','upload-stream-stage','upload-stream-reset','upload-stream-manifest','upload-stream-settle']:
   self.assertTrue(lr.parse(ROOT/'books'/f'{name}.lisp').forms)
if __name__=='__main__': unittest.main()
