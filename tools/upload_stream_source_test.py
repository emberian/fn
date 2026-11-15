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
  from compose_rolling_upload_current import upper_cut,consts,replace,fragment,window_profile_guard
  lower={}
  for path in ['books/source-manifest-codec.lisp','books/upload-page-geometry.lisp','books/upload-window-geometry.lisp']:
   lower.update(consts((ROOT/path).read_text()))
  expected=upper_cut(transform(old),lower)
  original=subprocess.check_output(['git','show','9dd52af42:books/upload-kind.lisp'],cwd=ROOT,text=True)
  for name in ['fn2-input-config-profilep','fn2-input-config-from']:
   expected=replace(expected,'defun',name,fragment(original,'defun',name))
  expected=expected.replace('(include-book "upload-window-geometry")',
     '(include-book "upload-window-geometry")\n(include-book "upload-page-geometry")')
  expected=window_profile_guard(expected)
  expected=expected.replace('(+ (* 2 *fn2-upload-hash-bytes*) *fn2-upload-scan-bytes*)',
                            '(+ *fn2-upload-hash-bytes* *fn2-upload-scan-bytes*)')
  expected=expected.replace('(equal *fn2-upload-run-bytes* 6144)','(equal *fn2-upload-run-bytes* 4096)')
  expected=expected.replace(':budget (:bytes 6144',':budget (:bytes 4096')
  expected=expected.replace(';; and *fn2-upload-scan-bytes* of header scanned per run; each hashed span\n;; is also counted once for LF octets before its source window can roll.',
    ';; and *fn2-upload-scan-bytes* of header scanned per run. LF octets are\n;; counted at confirmed source emission, with no second pool traversal.')
  self.assertEqual(expected,(ROOT/'books/upload-kind.lisp').read_text())
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
  body=p.text[m.start:m.end];self.assertNotIn('min',body)
  self.assertIn('(fn2-upload-input-bound max cap0 cap1)',body)
  lower=lr.parse(ROOT/'books/upload-page-geometry.lisp')
  helper=lr.match('(defun fn2-upload-input-bound ?*body)',lower.forms)[0]
  h=lower.text[helper.start:helper.end];self.assertIn('(nfix article-max)',h);self.assertNotIn('(min ',h)
  s=(ROOT/'books/upload-stream-stage.lisp').read_text()
  self.assertIn('(length (min *fn2-upload-stream-stage-quantum*',s)
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
 def test_fault_controls_follow_reachable_rolling_operations(self):
  s=(ROOT/'tests/upload-uncertainty-served-unit.lisp').read_text()
  self.assertIn('*fn2-upload-state-stream-wrote*',s)
  self.assertIn('*fn2-upload-state-stream-fenced*',s)
  for field in ['rootext','rootepoch','rootalloc','stream-end','stream-resets','stream-stage-used',
                'stream-eof','stream-stored-finalized','stream-provisional','stream-repack']:
   self.assertIn('fn2-upload-row-'+field,s)
  self.assertEqual(s.count('(assert-event (fn2-uui-run '),3)
 def test_actual_stage_byte_accounting_fits_existing_budget(self):
  s=(ROOT/'books/upload-stream-stage.lisp').read_text()
  for token in ['(floor (nfix (- *fn2-upload-run-bytes* *fn2-upload-stream-stage-overhead*)) 3)',
                '(* 3 *fn2-upload-stream-stage-quantum*)', ':bytes *fn2-upload-stream-stage-work*']:
   self.assertIn(token,s)
  self.assertIn('(<= *fn2-upload-stream-stage-work* *fn2-upload-run-bytes*)',s)
  source=(ROOT/'books/pool-ranges.lisp').read_text()
  self.assertIn('(update-fn2-pool-datai dst (fn2-pool-datai src fn2-pool)',source)
 def test_block_cost_class_is_checked_program_transformation(self):
  import upload_block_cost_rewrite as rw
  old=subprocess.check_output(['git','show','522e12181:books/assembly-callbacks-d-upload.lisp'],cwd=ROOT,text=True)
  expected=rw.arm_charges(old)
  expected=expected.replace('(:charge :bytes (+ (* 2 *fn2-upload-hash-bytes*) *fn2-upload-digest-octets* 4)',
                            '(:charge :bytes *fn2-upload-stream-stage-work*')
  expected=expected.replace('(:set (location-hashed (+ block 1)) (mstep 2)) (:charge :bytes 32',
                            '(:set (location-hashed (+ block 1)) (mstep 2)) (:charge :bytes *fn2-upload-digest-copy-bytes*')
  from upload_verdict_cost_rewrite import arm_charge
  self.assertEqual(arm_charge(expected),subprocess.check_output(['git','show','af3ab4c00:books/assembly-callbacks-d-upload.lisp'],cwd=ROOT,text=True))
  with self.assertRaises(AssertionError):
   rw.arm_charges(old.replace('fn2-upload-block-cv row-lslot','fn2-removed-call row-lslot',1))
 def test_verdict_is_bounded_and_separate_from_stream_hash(self):
  s=(ROOT/'books/upload.lisp').read_text()
  self.assertIn('(<= (fn2-upload-row-ml id fn2-core) *fn2-upload-line-max*)',s)
  self.assertIn('(<= (fn2-upload-row-pl id fn2-core) *fn2-upload-line-max*)',s)
  self.assertIn('(assert-event (<= *fn2-upload-verdict-work-bytes* *fn2-upload-run-bytes*))',s)
  s=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=s.index('(:stream-init :on-refusal');b=s.index('(:stream-receiving :on-refusal',a)
  self.assertEqual(s[a:b].count(':bytes *fn2-upload-verdict-work-bytes*'),2)
 def test_new_books_parse(self):
  for name in ['upload-stream','upload-stream-stage','upload-stream-reset','upload-stream-manifest','upload-stream-settle']:
   self.assertTrue(lr.parse(ROOT/'books'/f'{name}.lisp').forms)
if __name__=='__main__': unittest.main()
