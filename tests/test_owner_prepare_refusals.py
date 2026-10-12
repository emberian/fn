"""Execute the actual prepare adapters with already-decided core replies.

The constructor and recognizer are fixture seams, not models of their policy.
Entering the interner, prepare, or install on a refusal fails this probe. The
constructor's codec decisions have separate ACL2 teeth in store-node-tests.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_all


def actual(path, name, kind="defun"):
    matches = [form for form in forms((ROOT / path).read_text())
               if re.match(r"\(" + kind + r"\s+" + re.escape(name) + r"\s", form, re.I)]
    if len(matches) != 1:
        raise AssertionError((path, name, len(matches)))
    # ACL2's declaration describes its stobjs/mode; the adapter body is exact.
    form = matches[0]
    if kind == "defun":
        declaration = next((node for node in read_all(form)[0].items
                            if form[node.start:node.end].startswith("(declare (xargs")), None)
        if declaration:
            form = form[:declaration.start] + form[declaration.end:]
    return form


@unittest.skipUnless(shutil.which("sbcl"), "SBCL needed for host adapter probe")
class OwnerPrepareRefusals(unittest.TestCase):
    def test_constructor_refusals_return_by_name_without_interning(self):
        sources = "\n".join([
            actual("books/store-node.lisp", "*fn-sn-article-record-refusals*", "defconst"),
            actual("host/owner-host.lisp", "fn-owner-prepare"),
            actual("host/owner-host.lisp", "fn-owner-prepare-buffer"),
            actual("host/store-node-host.lisp", "fn-store-sn-prepare"),
            actual("host/native/owner.lisp", "fnn-owner-prepare-refusal-word"),
        ])
        prefix = r'''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defmacro defconst (name value) `(defparameter ,name ,value))
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars form &body body) `(multiple-value-bind ,vars ,form ,@body))
(defun len (x) (length x))
'''
        prefix += r'''
(defvar *reply*)
(defvar *expected-charge*)
(defvar *constructor-calls* 0)
(defvar *interns* 0)
(defvar *prepares* 0)
(defvar *installs* 0)
(defun fn-record-p (x) (equal x '(:record)))
(defun fn-sn-article-record (s obs mid payload groups id subject evidence charge)
 (declare (ignore s obs mid payload groups id subject evidence))
 (assert (= charge *expected-charge*))
 (incf *constructor-calls*) *reply*)
(defun fn-store-octets->string (xs) (coerce (mapcar #'code-char xs) 'string))
(defun fn-store-groups-from-codes (codes domain) (declare (ignore codes domain)) '("fn.test"))
(defun fn-octet-listp (xs) (and (listp xs) (every (lambda (x) (typep x '(unsigned-byte 8))) xs)))
(defun fn-pfld-article-inputsp (&rest args) (declare (ignore args)) t)
(defun fn-store-existing-action (&rest args) (declare (ignore args)) nil)
(defun fn-pidx-existing-action-cat (&rest args) (declare (ignore args)) nil)
(defun fn-adm-handle-room-p (&rest args) (declare (ignore args)) t)
(defun fn-octets-list (buffer) (declare (ignore buffer)) '(65))
(defun fn-octets-len (buffer) (declare (ignore buffer)) 1)
(defun fn-owner-record-octets (hist state) (values 0 hist state))
(defun fn-owner-record-debt (hist state) (values 0 hist state))
(defun fn-owner-record-totals (hist state) (values nil hist state))
(defun fn-owner-memory-gate (state) (declare (ignore state)) '(0 0 0))
(defun fn-apc-intern-row-at (record &rest args)
 (declare (ignore args)) (assert (fn-record-p record)) (incf *interns*) :row)
(defun fn-pout-prepare-article (&rest args)
 (declare (ignore args)) (incf *prepares*) (values :prepared :next))
(defun fn-ppc-pout-prepare-article-cat (&rest args)
 (declare (ignore args)) (incf *prepares*) (values :prepared :next))
(defun fn-owner-install-ocfg (next state)
 (declare (ignore next)) (incf *installs*) state)
(defun fn-psrv-store-prepare-next (&rest args)
 (declare (ignore args)) (incf *prepares*) :next)
(defun f-put-global (key next state)
 (declare (ignore key next)) (incf *installs*) state)
(defun f-get-global (key state) (declare (ignore key state)) :store)
(defun fn-adm-article-word (word &rest args) (declare (ignore args)) word)
(defun fn-owner-retain-carry-put (carry state) (declare (ignore carry)) state)
(defun fn-record-payload (record) (assert (fn-record-p record)) '(65))
(defun fnn-fault (&rest args) (error "Unknown prepare word: ~s" args))
'''
        for name in ("fn-owner-store", "fn-state-groups", "fn-node-acceptance", "fn-sn-node",
                     "fn-own-clock", "fn-owner-core", "fn-pvc-article-budget-carried",
                     "fn-owner-profile-carry", "fn-owner-store-profile", "fn-sf-records-count",
                     "fn-sn-files", "fn-owner-ocfg", "fn-sn-keyring", "fn-sn-keyring-generation",
                     "fn-arena-count", "fn-owner-parse-carry", "fn-adm-memory-admitp", "fn-prc-refresh",
                     "fn-owner-retain-carry", "fn-node-retention", "fn-sbud-count", "fn-store-sn-domain"):
            prefix += f"(defun {name} (&rest args) (declare (ignore args)) 0)\n"
        suffix = r'''
(defun probe (reply charge)
 (let ((*reply* reply) (*expected-charge* charge)
       (*constructor-calls* 0) (*interns* 0) (*prepares* 0) (*installs* 0))
   (let ((results
          (list
           (multiple-value-list (fn-owner-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) charge :arena :hist :state))
           (multiple-value-list (fn-owner-prepare-buffer '(60 97 64 120 62) '(0) '(105) '(115) '(101) charge :octets :arena :cat :hist :state))
           (multiple-value-list (fn-store-sn-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) charge :clock :arena :state)))))
     (assert (= *constructor-calls* 3))
     (if (fn-record-p reply)
         (progn
          (assert (equal (mapcar #'second results) '((:seal (65)) :seal-buffer (:seal (65)))))
          (assert (= *interns* 2)) (assert (= *prepares* 3)) (assert (= *installs* 4)))
         (progn
          (assert (equal results (list (list nil reply :arena :hist :state)
                                       (list nil reply :arena :hist :state)
                                       (list nil reply :arena :state))))
          (assert (eq (fnn-owner-prepare-refusal-word reply) reply))
          (assert (zerop *interns*)) (assert (zerop *prepares*)) (assert (zerop *installs*))
          (format t "NAMED-NOT-INTERNED ~s charge=~d~%" reply charge))))))
(dolist (word *fn-sn-article-record-refusals*) (probe word (expt 2 64)))
(probe '(:record) 1)
(assert (eq (fnn-owner-prepare-refusal-word :invalid) :malformed))
(assert (eq (fnn-owner-prepare-refusal-word :unaffordable) :unaffordable))
(assert (handler-case (progn (fnn-owner-prepare-refusal-word :unknown) nil) (error () t)))
(write-line "OWNER-PREPARE-REFUSALS-PASS")
'''
        path = ROOT / "build/codex/l-seq/host-refusal-unit-probe.lisp"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(prefix + sources + suffix)
        completed = subprocess.run(
            ["sbcl", "--noinform", "--disable-debugger", "--script", str(path)],
            cwd=ROOT, capture_output=True, text=True, timeout=30)
        (path.parent / "host-refusal-unit-sbcl.log").write_text(completed.stdout + completed.stderr)
        self.assertEqual(completed.returncode, 0, completed.stderr[-12000:])
        self.assertIn("NAMED-NOT-INTERNED :CHARGE-INVALID charge=18446744073709551616", completed.stdout)
        self.assertIn("OWNER-PREPARE-REFUSALS-PASS", completed.stdout)


if __name__ == "__main__":
    unittest.main()
