"""Actual exported callback table; source/world admission remains separate."""
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'tests/fixtures/evidence/extracted-callback-world-2026-09-30'
sys.path.insert(0, str(ROOT / 'tools'))
import proof_repl


class CallbackWorldTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_metadata_installer_and_refusers(self):
        names = {'fnn-install-raw-dispatch', 'fnn-fixed-raw-callback'}
        def selected(path):
            return [f for f in proof_repl.forms(path.read_text())
                    if proof_repl.head_and_name(f)[1] in names]
        self.assertEqual(selected(ROOT / 'host/native/io.lisp'),
                         selected(EVIDENCE / 'metadata-native.lisp'))
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            command = [sys.executable, str(ROOT / 'tools/extract/cl.py'),
                       str(EVIDENCE / 'guarded-core.json'),
                       '--packages', str(EVIDENCE / 'guarded-packages.json'),
                       '--packages-out', str(target / 'guarded-packages.lisp'),
                       '--out', str(target / 'guarded-core.lisp'),
                       '--inventory', str(target / 'inventory.json')]
            emitted = subprocess.run(command, capture_output=True, text=True, timeout=30)
            self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
            for name in ('guarded-world.lisp', 'metadata-native.lisp'):
                shutil.copyfile(EVIDENCE / name, target / name)
            original = '/Users/ember/dev/fn/build/lanes/gpt61-extracted-product'
            script = (EVIDENCE / 'metadata-driver.lisp').read_text()
            script = script.replace(original + '/build/receiver-provider-export/build', str(target))
            script = script.replace(original + '/tools/extract/clruntime.lisp',
                                    str(ROOT / 'tools/extract/clruntime.lisp'))
            driver = target / 'driver.lisp'
            driver.write_text(script)
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                  '--script', str(driver)], capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('PASS actual exported table/validator/installer/fixed creator', run.stdout)
            self.assertIn('PASS missing abstract metadata refused', run.stdout)
            self.assertIn('PASS quiet same validation', run.stdout)


if __name__ == '__main__':
    unittest.main()
