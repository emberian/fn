"""host/store-open-host.lisp closes every handle it opens, except a segment's (sweep S041).

The extracted read-only open runs these functions over the host primitives
(tools/extract/hostio.scm), whose handle table keeps an fd until fn-hx-close.
Here the real definitions of fn-xo-read-bounded and fn-xo-filesystem-observation
are read out of the host file and run in SBCL over a counting stand-in for the
primitives: after each call, on each of its paths, no handle may stay open.
Only the host primitives (and ACL2's fn-smid-* observation fold, which the
functions under test call into) are stand-ins.
"""
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HOST = ROOT / "host" / "store-open-host.lisp"

DRIVER = r'''
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(declaim (declaration xargs))
(defun len (l) (if (consp l) (1+ (len (cdr l))) 0))
(defun take (n l) (subseq l 0 n))
(defvar *open* nil)
(defvar *next* 0)
(defvar *files* (make-hash-table :test 'equal))
(defvar *fail-pread* nil)
(defun fn-hx-open (path)
  (let ((f (gethash path *files*)))
    (if (null f) (list :error 2 "open")
      (let ((h (incf *next*)))
        (push h *open*)
        (list :ok h (length (cdr f)) (eq (car f) :regular))))))
(defun fn-hx-pread (h off n)
  (declare (ignorable h))
  (if *fail-pread* (list :error "pread")
    (list :ok (let ((l (cdr (gethash "cur" *files*)))) (subseq l (min off (length l)) (min (length l) (+ off n)))))))
(defun fn-hx-close (h) (setf *open* (remove h *open*)) :ok)
(defun fn-hx-statfs (path) (declare (ignore path)) (make-list 4096 :initial-element 0))
(defun fn-hx-realpath (path) (if (equal path "/gone") nil path))
(defun fn-hx-os () :linux)
(defun fn-smid-mountinfo-line-max () 4096)
(defun fn-smid-mountinfo-step (best line path) (declare (ignore line path)) best)
(defun fn-smid-linux-observation (raw best) (list :observed (length raw) best))

(defun load-host-defuns (path wanted)
  (with-open-file (in path)
    (let ((*package* (find-package "ACL2")) (found nil))
      (loop for form = (read in nil :eof) until (eq form :eof)
            do (when (and (consp form) (eq (car form) 'defun) (member (string (cadr form)) wanted :test #'string=))
                 (push (string (cadr form)) found)
                 (eval form)))
      (dolist (w wanted) (assert (member w found :test #'string=) () "~a is not defined in the host file" w)))))
(load-host-defuns (car (last sb-ext:*posix-argv*))
  '("FN-XO-FAULT" "FN-XO-OKP" "FN-XO-READ-BOUNDED" "FN-XO-READ-PROC" "FN-XO-MOUNTINFO-FOLD"
    "FN-XO-FILESYSTEM-OBSERVATION"))

(defun file! (path kind octets)
  (setf (gethash path *files*) (cons kind octets)))
(defvar *failures* nil)
(defun check (label result expect-open)
  (declare (ignorable result))
  (unless (= (length *open*) expect-open)
    (push (format nil "~a: ~a handle(s) still open" label (length *open*)) *failures*))
  (setf *open* nil))

(file! "cur" :regular '(1 2 3))
(file! "/reg" :regular '(1 2 3))
(file! "/dir" :other '(1 2 3))
(file! "/proc/self/mountinfo" :regular '(10 10))
(let ((r (fn-xo-read-bounded "/reg" 100)))
  (unless (equal r '(:ok (1 2 3))) (push (format nil "read result ~s" r) *failures*))
  (check "read ok" r 0))
(check "read overbound" (fn-xo-read-bounded "/reg" 2) 0)
(check "read non-regular" (fn-xo-read-bounded "/dir" 100) 0)
(check "read missing" (fn-xo-read-bounded "/nope" 100) 0)
(let ((*fail-pread* t)) (check "read pread error" (fn-xo-read-bounded "/reg" 100) 0))
(let ((r (fn-xo-filesystem-observation "/reg")))
  (unless (eq (car r) :observed) (push (format nil "observation result ~s" r) *failures*))
  (check "mountinfo" r 0))
(check "mountinfo, root unresolved" (fn-xo-filesystem-observation "/gone") 0)
(if *failures*
    (progn (format t "FAIL~%") (dolist (f (reverse *failures*)) (format t "~a~%" f)) (sb-ext:exit :code 1))
    (format t "PASS~%"))
'''


class StoreOpenHostHandleTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_every_non_segment_handle_is_closed(self):
        with tempfile.TemporaryDirectory() as d:
            driver = Path(d) / "driver.lisp"
            driver.write_text(DRIVER)
            r = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                "--script", str(driver), str(HOST)],
                               capture_output=True, text=True, timeout=60)
        out = r.stdout + r.stderr
        leaks = [line for line in out.splitlines() if "handle(s) still open" in line]
        if leaks:
            self.fail("the extracted read-only open leaves handles open")
        self.assertEqual(r.returncode, 0, out)
        self.assertIn("PASS", r.stdout)


if __name__ == "__main__":
    unittest.main()
