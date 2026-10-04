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
            (ROOT/'books/control-observation.lisp').read_text(),
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

if __name__ == '__main__': unittest.main()
