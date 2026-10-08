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
