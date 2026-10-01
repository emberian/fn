"""Genuine PRS-issued registered job and actual bounded count caller."""
from tests.test_operation_diagnostics_boundary import pr, ROOT
from pathlib import Path
import shutil, subprocess, tempfile, unittest
TAIL='''
(let* ((pool (setup)) (original '(a b c d))
       (cursor (fn-orc-count-begin original)))
 (multiple-value-bind (word token pool state)
  (fn-orc-reserve-internal '(request) nil :status *capture* cursor 0 33 :paid-body pool *state*)
  (assert (eq word :report-reserved))
  (multiple-value-bind (word count state) (fn-owner-report-count-tick token 1 state)
   (assert (eq :yield word)) (assert (null count))
   (let ((current (nth 6 (fn-orc-job state))))
    (assert (fn-orc-countp current))
    (assert (equal original '(a b c d)))
    (assert (= (+ (nth 2 current) (len (nth 1 current))) (len original))))
   (assert (not (= (nth 2 (nth 6 (fn-orc-job state))) (len original)))))
  (multiple-value-bind (word count state) (fn-owner-report-count-tick token 5 state)
   (assert (eq :report-counted word)) (assert (= count (len original)))
   (assert (null (nth 1 (nth 6 (fn-orc-job state)))))))
 (fn-orc-writer-enter *state*)
 (assert (eq :snapshot-changed (fn-owner-report-count-tick '(:owner-report 1) 5 *state*)))
 (assert (eq :report-stale (fn-owner-report-count-tick '(:owner-report 2) 5 *state*))))
(format t "PASS registered bounded report count~%")
'''
class ReportCount(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_current_job_complete_and_hypothesis_removal(self): self.run_fixture()
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_count_increment_mutation_refuted(self): self.run_fixture(('(+ 1 count)', 'count'))
    def run_fixture(self, mutation=None):
        names=('page-read-resources','owner-report-capture','owner-report-reservation','owner-report-count','owner-report-count-host')
        source='\n'.join(f for name in names for f in pr.forms((ROOT/f'books/{name}.lisp').read_text()) if f.lower().startswith('(defun '))
        if mutation:
            old,new=mutation;self.assertEqual(source.count(old),1);source=source.replace(old,new)
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);(d/'source.lisp').write_text(source)
            driver=(ROOT/'tests/fixtures/owner_report_reservation_boundary.lisp').read_text().replace('__SOURCE_FILE__',str(d/'source.lisp'))+TAIL
            (d/'driver.lisp').write_text(driver)
            r=subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'driver.lisp')],capture_output=True,text=True,timeout=30)
        if mutation: self.assertNotEqual(r.returncode,0);self.assertIn('assertion',r.stderr.lower())
        else: self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('PASS registered bounded report count',r.stdout)
