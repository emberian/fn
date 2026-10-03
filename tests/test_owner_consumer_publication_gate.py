"""Actual owner I/O gate consumes the all-record preservation safety set.

This executes source predicate bodies; it does not model Store transitions.
The matching image consumer/bootstrap fixture supplies the durability check.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.test_operation_diagnostics_boundary import selected, ROOT


class ConsumerPublicationGate(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_nonarticle_order_and_file_observations(self):
        owner = Path(os.environ.get('FN_OWNER_GATE_SOURCE', ROOT / 'host/owner-host.lisp'))
        source = '\n'.join((
            selected(ROOT / 'books/config-store-steps.lisp', ['fn-cstp-reserve-opp']),
            selected(ROOT / 'books/owner-prepare-served-ocl.lisp', ['fn-psrv-io-safep']),
            selected(owner, ['fn-owner-io-safep']),
        ))
        driver = '''(proclaim '(declaration xargs))
(defun member-equal (x xs) (member x xs :test #'equal))
; An actual consumer candidate is not a held article. The old gate's
; article-only predicates decline it; no Store transition is simulated.
(defun fn-lgoc-article-stagedp (st) (declare (ignore st)) nil)
(defun fn-lgoc-io-safep (st op result) (declare (ignore st op result)) nil)
'''
        driver += source
        driver += '''
(dolist (kind '(:consumer :retention :identity :topic :article))
 (assert (fn-owner-io-safep kind :log-order :ok)))
(dolist (op '(:log-reserve :start-frontier :frontier-file :frontier-replace
             :frontier-directory :recovery-barrier :record-file :record-link
             :record-directory))
 (assert (fn-owner-io-safep :consumer op :ok)))
(dolist (op '(:unknown :close :record-completing nil))
 (assert (not (fn-owner-io-safep :consumer op :ok))))
(format t "PASS actual all-record publication gate~%")
'''
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'driver.lisp'
            path.write_text(driver)
            result = subprocess.run([shutil.which('sbcl'), '--noinform',
                                     '--disable-debugger', '--script', str(path)],
                                    capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('PASS actual all-record publication gate', result.stdout)
