"""Image-free SBCL checks of the real native HPI action wrapper.

The core return and positional executor are test doubles. These checks cover
scheduling, retained observations and locks, not ACL2 or physical I/O truth.
"""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class HistoryImageScheduleTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL needed for native wrapper check")
    def test_one_core_step_and_at_most_one_unlocked_effect(self):
        source = ROOT / "host/native/history-image-writer.lisp"
        program = r'''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "test extent"))
(defvar *word*) (defvar *effect*) (defvar *answer*)
(defvar *core-calls* 0) (defvar *io-calls* 0)
(defvar *seen-observation*) (defvar *throw-io* nil)
(defun fnn-core-page-read-pool (name cursor observation &rest buffers)
  (assert (eq name 'fn-owner-history-image-tick))
  (assert (eq cursor :old-cursor))
  (assert (equal buffers '(:q0 :q1 :q2 :q3 :pool :digest)))
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*))
  (incf *core-calls*)
  (setq *seen-observation* observation)
  (list *word* *effect* :next-cursor :next-q0 :next-q1 :next-q2 :next-q3
        :next-pool :next-digest :same-read-pool))
(load "__SOURCE__")
(defun fnn-hpi-execute-effect (writer stage effect)
  (assert (not (sb-thread:holding-mutex-p *fnn-extent-lock*)))
  (assert (eq stage :retained-stage))
  (assert (eq effect *effect*))
  (assert (eq (fnn-hpi-writer-cursor writer) :next-cursor))
  (assert (eq (fnn-hpi-writer-pool writer) :next-pool))
  (incf *io-calls*)
  (when *throw-io* (error "uncertain syscall return"))
  *answer*)
(defun run-case (word answer issued)
  (let* ((*word* word) (*effect* (list :issued 17)) (*answer* answer)
         (*core-calls* 0) (*io-calls* 0) (*seen-observation* nil)
         (input (list :previous-observation 16))
         (writer (fnn-hpi-retain :old-cursor :q0 :q1 :q2 :q3 :pool :digest)))
    (multiple-value-bind (got effect observation)
        (fnn-hpi-action writer :retained-stage input)
      (assert (eq got word)) (assert (eq effect *effect*))
      (assert (eq observation (if issued answer nil)))
      (assert (eq *seen-observation* input))
      (assert (= *core-calls* 1))
      (assert (= *io-calls* (if issued 1 0)))
      (assert (equal (list (fnn-hpi-writer-cursor writer)
                          (fnn-hpi-writer-q0 writer) (fnn-hpi-writer-q1 writer)
                          (fnn-hpi-writer-q2 writer) (fnn-hpi-writer-q3 writer)
                          (fnn-hpi-writer-pool writer) (fnn-hpi-writer-digest writer))
                     '(:next-cursor :next-q0 :next-q1 :next-q2 :next-q3
                       :next-pool :next-digest))))))
(run-case :write (list :written :source 17 :ok) t)
(run-case :io (list :image-read :source 17 :uncertain nil) t)
(run-case :io (list :retained :image-effect-observation) t)
(run-case :write (list :refused :image-effect) t)
(dolist (word '(:need-row :need-byte :row-done :funded :continue :prepared :stale))
  (run-case word nil nil))
(let* ((*word* :write) (*effect* (list :issued 17)) (*core-calls* 0)
       (*io-calls* 0) (*throw-io* t)
       (writer (fnn-hpi-retain :old-cursor :q0 :q1 :q2 :q3 :pool :digest))
       (escaped nil))
  (handler-case (fnn-hpi-action writer :retained-stage nil)
    (error () (setq escaped t)))
  (assert escaped) (assert (= *core-calls* 1)) (assert (= *io-calls* 1))
  (assert (eq (fnn-hpi-writer-cursor writer) :next-cursor))
  (assert (not (sb-thread:holding-mutex-p *fnn-extent-lock*))))
(defvar *prep-word*) (defvar *prep*) (defvar *prepared-writer*)
(defun fnn-call (name cursor)
  (assert (eq name 'fn-hpip-tick))
  (assert (eq cursor :installed-preparation))
  (list *prep-word* *prep* *prepared-writer*))
(dolist (word '(:continue :refused :prepared))
  (let* ((*prep-word* word) (*prep* (list :retained-preparation))
         (*prepared-writer* (list :need-growth))
         (writer (fnn-hpi-retain :installed-preparation :q0 :q1 :q2 :q3 :pool :digest)))
    (assert (eq (fnn-hpi-preparation-step writer) word))
    (assert (eq (fnn-hpi-writer-cursor writer)
                (if (eq word :prepared) *prepared-writer* *prep*)))
    (assert (eq (fnn-hpi-writer-q0 writer) :q0))
    (assert (eq (fnn-hpi-writer-digest writer) :digest))))
(format t "~%HPI-SCHEDULE-PASSED~%")
'''.replace("__SOURCE__", str(source))
        with tempfile.TemporaryDirectory(prefix="fn-hpi-schedule-") as directory:
            script = Path(directory) / "schedule.lisp"
            script.write_text(program)
            result = subprocess.run(
                [shutil.which("sbcl"), "--dynamic-space-size", "128",
                 "--noinform", "--disable-debugger", "--script", str(script)],
                text=True, capture_output=True, timeout=20,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("HPI-SCHEDULE-PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
