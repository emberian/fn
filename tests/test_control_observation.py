"""Actual control exchange and read loop with a deterministic socket/clock adapter."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('diag', ROOT/'tests/test_operation_diagnostics_boundary.py')
diag = importlib.util.module_from_spec(spec); spec.loader.exec_module(diag)

class ControlObservation(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_delayed_reply_explicit_wait_and_uncertainty(self):
        source = '\n'.join([
            '\n'.join(f for f in diag.pr.forms((ROOT/'books/control-observation.lisp').read_text()) if f.lower().startswith(('(in-package ', '(defconst ', '(defun '))),
            diag.selected(ROOT/'books/native-control.lisp', ['fn-native-control-transport-outcome']),
            diag.selected(ROOT/'host/native-control-host.lisp', ['fn-native-control-host-reply-seconds']),
            diag.selected(ROOT/'host/native/control-transport.lisp', ['fnn-control-exchange', 'fnn-control-read-frame', 'fnn-control-join-chunks']),
        ])
        fixture = (ROOT/'tests/fixtures/control_observation-mock.lisp').read_text()
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            (d/'source.lisp').write_text(source)
            (d/'run.lisp').write_text(fixture.replace('__SOURCE__', str(d/'source.lisp')))
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(d/'run.lisp')], text=True, capture_output=True, timeout=15)
        self.assertEqual(run.returncode, 0, run.stdout+run.stderr)
        self.assertIn('PASS control observation', run.stdout)


class ControlReceipt(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_ack_precedes_work_and_status_outlives_reply_deadline(self):
        def definitions(path):
            return '\n'.join(f for f in diag.pr.forms((ROOT/path).read_text())
                             if f.lower().startswith(('(in-package ', '(defconst ', '(defun ')))
        source = '\n'.join([
            definitions('books/control-observation.lisp'),
            definitions('books/outcome-class.lisp'),
            diag.selected(ROOT/'books/records-shape.lisp', [
                'fn-record-string-octets-rev', 'fn-record-string-octets-aux', 'fn-record-string-octets']),
            "(defconst *fn-nctrl-max-reason-octets* 512)\n"
            "(defconst *fn-nctrl-no-reason-word* '(78 79 78 69))\n"
            "(defconst *fn-nctrl-unnamed-reason-word* '(117 110 110 97 109 101 100))",
            diag.selected(ROOT/'books/native-control-reason.lisp', ['fn-nctrl-word-chars-octets', 'fn-nctrl-reason-word']),
            definitions('books/control-receipt-wire.lisp'),
            diag.selected(ROOT/'host/native/io.lisp', ['fnn-core', 'fnn-core-state']),
            diag.selected(ROOT/'host/native/owner.lisp', ['fnn-owner-core']),
            diag.selected(ROOT/'books/native-admin-shape.lisp', ['fn-native-admin-result']),
            diag.selected(ROOT/'books/native-admin.lisp', ['fn-native-admin-arg', 'fn-native-admin-control-plan']),
            diag.selected(ROOT/'books/owner-compact-request.lisp', ['fn-ock-request-status']),
            diag.selected(ROOT/'host/native/owner.lisp', [
                'fnn-owner-maybe-publish', 'fnn-owner-maybe-publish-quantum']),
            diag.selected(ROOT/'host/native/admin.lisp', ['fnn-owner-compaction-request']),
            diag.selected(ROOT/'host/native/control.lisp', [
                'fnn-control-receipt-step', 'fnn-control-receipt-work', 'fnn-control-handle-client']),
            diag.selected(ROOT/'host/native/control-transport.lisp', ['fnn-control-admin']),
        ])
        fixture = (ROOT/'tests/fixtures/control_receipt-mock.lisp').read_text()
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            (d/'source.lisp').write_text(source)
            (d/'run.lisp').write_text(fixture.replace('__SOURCE__', str(d/'source.lisp')))
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(d/'run.lisp')], text=True, capture_output=True, timeout=30)
        self.assertEqual(run.returncode, 0, run.stdout+run.stderr)
        self.assertIn('PASS control receipt', run.stdout)

if __name__ == '__main__': unittest.main()
