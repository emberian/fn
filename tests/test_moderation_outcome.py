"""Run the literal multi-quantum moderation consumer with recorded publications."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('diag', ROOT/'tests/test_operation_diagnostics_boundary.py')
diag = importlib.util.module_from_spec(spec); spec.loader.exec_module(diag)
class ModerationOutcome(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_partial_publication_remains_visible(self):
        source = '\n'.join([(ROOT/'books/moderation-outcome.lisp').read_text(),
            diag.selected(ROOT/'host/native-control-host.lisp', ['fn-native-control-host-withdraw-result']),
            diag.selected(ROOT/'host/native/owner.lisp', ['fnn-owner-moderation-serialized'])])
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory); (d/'source.lisp').write_text(source)
            (d/'run.lisp').write_text((ROOT/'tests/fixtures/moderation_outcome.lisp').read_text().replace('__SOURCE__', str(d/'source.lisp')))
            run = subprocess.run([shutil.which('sbcl'),'--noinform','--disable-debugger','--script',str(d/'run.lisp')], text=True,capture_output=True,timeout=15)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertIn('PASS moderation combined outcome', run.stdout)
if __name__ == '__main__': unittest.main()
