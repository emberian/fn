"""Isolated native measurement test using the actual owner macro and callback."""
import shutil
import subprocess
from pathlib import Path

import pytest
from tools.proof_repl import forms, head_and_name

ROOT = Path(__file__).resolve().parents[1]


def test_commit_complete_allocation_overlaps_commit(tmp_path):
    sbcl = shutil.which("sbcl")
    if not sbcl:
        pytest.skip("SBCL is required for the native measurement macro")
    wanted = {
        "*fnn-owner-measure*", "*fnn-owner-measure-label*",
        "*fnn-owner-measure-table*",
        "fnn-owner-measure-now", "fnn-owner-measure-note", "fnn-owner-measured",
        "fnn-owner-finish-submission",
    }
    selected = []
    for form in forms((ROOT / "host/native/owner.lisp").read_text()):
        _head, name = head_and_name(form)
        if name in wanted:
            selected.append(form)
            wanted.remove(name)
    assert not wanted, wanted
    script = tmp_path / "measure.lisp"
    script.write_text("""
(defvar *fnn-trace-state* nil)
(defvar *fnn-trace-operation* nil)
(defvar *fnn-trace-connection-generation* nil)
(defvar *measurement-payload* nil)
(defun fnn-trace-now () (get-internal-real-time))
(defmacro fnn-trace-span (options &body body)
  (declare (ignore options)) `(progn ,@body))
(defun fnn-owner-core (name)
  (assert (eq name 'fn-owner-finish-submission))
  (setq *measurement-payload* (make-array 1048576 :element-type '(unsigned-byte 8)))
  :finished)
""" + "\n".join(selected) + """
(let ((*fnn-owner-measure* t) (*fnn-owner-measure-label* :commit))
 (dotimes (i 2)
  (assert (eq (fnn-owner-measured (:commit) (fnn-owner-finish-submission)) :finished)))
 (let ((commit (gethash :commit *fnn-owner-measure-table*))
       (complete (gethash :commit-complete *fnn-owner-measure-table*)))
  (assert (= (first commit) 2))
  (assert (= (first complete) 2))
  (assert (>= (fifth complete) 1048576))
  (assert (>= (fifth commit) (fifth complete)))
  (assert (>= (fourth commit) (fourth complete)))
  (assert (eq *fnn-owner-measure-label* :commit))
  (format t "commit=~s complete=~s~%" commit complete)))
""")
    result = subprocess.run(
        [sbcl, "--noinform", "--no-userinit", "--no-sysinit", "--script", str(script)],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "complete=" in result.stdout
