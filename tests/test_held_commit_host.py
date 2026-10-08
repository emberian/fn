"""Execute the real held macro/receipt helpers with controlled I/O outcomes.

The stubs supply ACL2's proved words; this checks lock placement, exception
transport, one submission, multiple values and a refused second entry.
"""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tools import lisp_source

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL is required')
class HeldCommitHost(unittest.TestCase):
    def test_frames_batch_failure_and_refused_entry(self):
        names = ('fnn-owner-held-commit', 'fnn-owner-held-frames-wait',
                 'fnn-owner-held-frames-complete', 'fnn-owner-held-finish',
                 'fnn-owner-job-word')
        forms = lisp_source.forms((ROOT / 'host/native/owner.lisp').read_text())
        actual = '\n'.join(f for f in forms
                           if any(f.startswith(f'({kind} {name} ')
                                  for name in names for kind in ('defun', 'defmacro')))
        fixture = r'''
(define-condition fnn-store-indeterminate (error) ())
(define-condition fnn-os-error (error) ())
(defvar *owner* nil)
(defvar *kind* :frames)
(defvar *failure* nil)
(defvar *refuse* nil)
(defvar *calls* nil)
(defvar *held* nil)
(defvar *lock* (sb-thread:make-mutex))
(defvar *ready* (sb-thread:make-waitqueue))
(defun fnn-err (&rest args) (declare (ignore args)))
(defun fnn-fault (&rest args) (declare (ignore args)) (error "fault"))
(defun fnn-refuse (&rest args) (declare (ignore args)) (error "refused"))
(defun fnn-owner-service-commit-lock (s) (declare (ignore s)) *lock*)
(defun fnn-owner-service-commit-ready (s) (declare (ignore s)) *ready*)
(defun section (s cid thunk &optional class)
  (declare (ignore s cid))
  (when (and *refuse* (eq class :commit)) (error "entry refused"))
  (let ((*owner* t)) (funcall thunk)))
(defmacro fnn-owner-gated ((s class) &body body)
  (declare (ignore s class)) `(let ((*owner* t)) ,@body))
(defun fnn-owner-held-start (s)
  (declare (ignore s)) (assert *owner*) (push :start *calls*) (setq *held* t)
  (if (eq *kind* :frames) '(:frames job ((:off . :intents))) '(:held members)))
(defun fnn-owner-frames-job (s job)
  (declare (ignore s job)) (assert (not *owner*)) (push :frames *calls*)
  (when *failure* (error *failure*)))
(defun fnn-owner-held-wait (s pending)
  (declare (ignore s pending)) (assert (not *owner*)) (push :batch *calls*)
  '(members deferred :fenced nil))
(defun fnn-owner-held-complete (s members deferred word condition thunk)
  (declare (ignore s members deferred word condition)) (assert *owner*)
  (push :complete *calls*) (setq *held* nil) (when thunk (funcall thunk)))
(defun fnn-owner-held-event (s event)
  (declare (ignore s)) (assert *owner*) (push event *calls*)
  (case event
    (:frames-fenced (setq *held* nil) :submit)
    (:frames-failed :stop)
    (:frames-fault :fault)
    (:completed (setq *held* nil) :none)))
(defun fnn-core (name &rest args)
  (case name
    (fn-oqw-step (case (third args) (:ok :done) (:uncertain :uncertain) (t :fault)))
    (fn-och-frames-event
     (case (first args) (:done :frames-fenced) (:uncertain :frames-failed) (t :frames-fault)))
    (fn-och-caller-answer
     (case (first args) (:submit :submitted) ((:none :stop) :stopping) (t :fault)))))
'''
        assertions = r'''
(defun trial (kind failure refuse)
  (let ((*kind* kind) (*failure* failure) (*refuse* refuse)
        (*calls* nil) (*held* nil) (submits 0) (caught nil) (answer nil))
    (handler-case
        (setq answer (multiple-value-list
                      (fnn-owner-held-commit (section nil nil)
                        (assert *owner*) (assert (not *held*))
                        (incf submits) (values :answer 42))))
      (error (e) (setq caught e)))
    (assert (not *held*))
    (assert (equal (reverse *calls*)
                   (if (eq kind :held) '(:start :batch :complete)
                     (cond ((typep failure 'fnn-store-indeterminate)
                            '(:start :frames :frames-failed :completed))
                           (failure '(:start :frames :frames-fault :completed))
                           (t '(:start :frames :frames-fenced))))))
    (if (or failure refuse)
        (progn (assert caught) (assert (= submits 0)))
      (progn (assert (not caught)) (assert (= submits 1))
             (assert (equal answer '(:answer 42)))))
  t))
(trial :frames nil nil)
(trial :held nil nil)
(trial :frames (make-condition 'fnn-store-indeterminate) nil)
(trial :frames (make-condition 'simple-error) nil)
(trial :frames nil t)
(trial :held nil t)
(write-line "held commit host: 6 scenarios passed")
'''
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'held.lisp'
            path.write_text(fixture + actual + assertions)
            result = subprocess.run(['sbcl', '--script', str(path)], text=True,
                                    capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('6 scenarios passed', result.stdout)

    def test_committer_plan_state_effects_and_waiter_counts(self):
        """The real host wrappers forward fn-otm-held-plan's state/effects and
        fn-otm-held-committer-wake's decision, including the waiting counts.
        ACL2's plan-barrier-trace and plan-budget-trace in owner-time-held-tests
        supply the semantic trace; these stubs isolate the host transport.
        """
        names = ('fnn-owner-held-event', 'fnn-owner-commit-wake')
        forms = lisp_source.forms((ROOT / 'host/native/owner.lisp').read_text())
        actual = '\n'.join(f for f in forms
                           if any(f.startswith(f'(defun {name} ') for name in names))
        fixture = r'''
(defstruct fnn-owner-gate mutex sched waiting)
(defun fnn-owner-service-gate (service) service)
(defun fnn-fault (&rest args) (error "host fault: ~s" args))
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-err (&rest args) (declare (ignore args)))
(defvar *expected*)
(defun fnn-core (name &rest args)
  (assert *expected*)
  (destructuring-bind (expected-name expected-args result) (pop *expected*)
    (assert (eq name expected-name))
    (assert (equal args expected-args))
    result))
(defun fnn-call (name &rest args) (apply #'fnn-core name args))
'''
        assertions = r'''
(let* ((waiting '(1 0 0 0 1 0))
       (gate (make-fnn-owner-gate :mutex (sb-thread:make-mutex)
                                 :sched :initial :waiting (coerce waiting 'vector)))
       (*expected*
        '((fn-otm-held-plan (:initial :started) (:sync :staged ((:off . :append))))
          (fn-otm-held-committer-wake (:staged nil t (1 0 0 0 1 0)) :wait)
          (fn-otm-held-plan (:staged :fenced) (:complete :fenced ((:owner . :complete))))
          (fn-otm-held-committer-wake (:fenced t t (1 0 0 0 1 0)) :collect)
          (fn-otm-held-plan (:fenced :completed) (:none :idle nil)))))
  (assert (equal (multiple-value-list (fnn-owner-held-event gate :started))
                 '(:sync ((:off . :append)))))
  (assert (eq (fnn-owner-gate-sched gate) :staged))
  (assert (eq (fnn-owner-commit-wake gate nil t) :wait))
  (assert (equal (multiple-value-list (fnn-owner-held-event gate :fenced))
                 '(:complete ((:owner . :complete)))))
  (assert (eq (fnn-owner-commit-wake gate t t) :collect))
  (assert (equal (multiple-value-list (fnn-owner-held-event gate :completed))
                 '(:none nil)))
  (assert (eq (fnn-owner-gate-sched gate) :idle))
  (assert (null *expected*)))
(write-line "committer plan transport passed")
'''
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'committer.lisp'
            path.write_text(fixture + actual + assertions)
            result = subprocess.run(['sbcl', '--script', str(path)], text=True,
                                    capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('committer plan transport passed', result.stdout)
            # Host implementation mutation: discard the plan's returned state.
            mutant = actual.replace('(setf (fnn-owner-gate-sched gate) sched)',
                                    '(identity sched)')
            self.assertNotEqual(mutant, actual)
            path.write_text(fixture + mutant + assertions)
            rejected = subprocess.run(['sbcl', '--script', str(path)], text=True,
                                      capture_output=True, timeout=30)
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
