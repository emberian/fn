"""Exact RX source export/projection component, without activation claims."""
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'planning/evidence/receiver-provider-extraction-2026-09-30'
sys.path.insert(0, str(ROOT / 'tools'))
import proof_repl


class ReceiverProviderTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_exact_export_and_same_provider_projection(self):
        names = {'fnn-receiver-backing', 'fnn-receiver-publish-fill'}
        actual = [f for f in proof_repl.forms((ROOT / 'host/native/io.lisp').read_text())
                  if proof_repl.head_and_name(f)[1] in names]
        frozen = [f for f in proof_repl.forms((EVIDENCE / 'native-projection.lisp').read_text())
                  if proof_repl.head_and_name(f)[1] in names]
        self.assertEqual(actual, frozen)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            generated = target / 'provider.lisp'
            compile_run = subprocess.run(
                [sys.executable, str(ROOT / 'tools/extract/cl.py'),
                 str(EVIDENCE / 'receiver-provider-v2.json'), '--out', str(generated),
                 '--inventory', str(target / 'inventory.json')],
                capture_output=True, text=True, timeout=30)
            self.assertEqual(compile_run.returncode, 0, compile_run.stdout + compile_run.stderr)
            driver = (EVIDENCE / 'projection-driver.lisp').read_text()
            replacements = {
                'tools/extract/clruntime.lisp': ROOT / 'tools/extract/clruntime.lisp',
                'build/receiver-provider-export/build/receiver-provider.lisp': generated,
                'build/receiver-provider-export/build/receiver-provider.fasl': target / 'provider.fasl',
                'build/receiver-provider-export/build/provider-constants.lisp': EVIDENCE / 'provider-constants.lisp',
                'build/receiver-provider-export/build/native-projection.lisp': EVIDENCE / 'native-projection.lisp',
            }
            for old, new in replacements.items():
                driver = driver.replace('"' + old + '"', '"' + str(new) + '"')
            path = target / 'driver.lisp'
            path.write_text(driver)
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                  '--script', str(path)], capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('PASS actual extracted RX provider/genuine reservation/SAME projection', run.stdout)


if __name__ == '__main__':
    unittest.main()
