"""Execute actual native early refusals after helper extraction.

Core replies are already-decided fixture inputs. No Store, owner quantum or
logical decision is simulated; entering any later mutation path fails the probe.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from proof_repl import forms


def actual(path, name):
    matches = [form for form in forms((ROOT / path).read_text())
               if re.match(r'\(def(?:un|macro)\s+' + re.escape(name) + r'\s', form, re.I)]
    if len(matches) != 1:
        raise AssertionError((path, name, len(matches)))
    return matches[0]


@unittest.skipUnless(shutil.which('sbcl'), 'SBCL needed for native source probe')
class NativeLexicalExitTests(unittest.TestCase):
    def test_actual_transit_and_receipt_preflight_refuse_before_mutation(self):
        sources = '\n'.join([
            actual('host/native/owner.lisp', 'fnn-owner-attempt-handlers'),
            actual('host/native/owner.lisp', 'fnn-owner-transit-refused'),
            actual('host/native/owner.lisp', 'fnn-owner-attempt-filled'),
            actual('host/native/bp-node.lisp', 'fnn-bpnode-receipt-result'),
        ])
        prefix = '''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *fnn-owner-payload-list*)
(defvar *fnn-owner-transit-detail*)
(defvar *observations* 0)
(defvar *release-lines* 0)
(defun fnn-core-buffer-state (subject &rest args)
 (declare (ignore args))
 (assert (eq subject 'fn-owner-control-filing-buffer))
 '(:refused :groups))
(defun fnn-bpnode-source-decision (view) (declare (ignore view)) (incf *observations*))
(defun fnn-bpnode-receipt-observations (view) (declare (ignore view)) :observations)
(defun fnn-bpnode-release-line (view obs) (declare (ignore view obs)) (incf *release-lines*))
(defun fnn-owner-core (subject &rest args)
 (declare (ignore args))
 (assert (eq subject 'fn-owner-bp-receipt-gatep)) nil)
(defun fnn-bpnode-receipt-detail (view obs) (declare (ignore view obs)) '(7 9))
(defun fnn-quantum-bp (&rest args) (declare (ignore args)) (error "Refusal entered owner quantum"))
'''
        suffix = '''
(assert (eq (fnn-owner-attempt-filled :owner :mid :payload nil :evidence) :refused))
(assert (eq *fnn-owner-transit-detail* :groups))
(assert (equal (multiple-value-list
                (fnn-bpnode-receipt-result :owner :root :view :peer))
               '(:receipt-refused (7 9))))
(assert (= *observations* 1))
(assert (= *release-lines* 1))
(write-line "NATIVE-LEXICAL-REFUSALS-PASS")
'''
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'probe.lisp'
            path.write_text(prefix + sources + suffix)
            completed = subprocess.run(
                ['sbcl', '--noinform', '--disable-debugger', '--script', str(path)],
                capture_output=True, text=True, timeout=30)
        self.assertEqual(completed.returncode, 0, completed.stderr[-12000:])
        self.assertIn('NATIVE-LEXICAL-REFUSALS-PASS', completed.stdout)


if __name__ == '__main__':
    unittest.main()
