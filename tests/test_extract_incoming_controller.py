"""Actual paired ACL2 export: fixed layout/MVs/effects, not native activation."""
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/extract'))
import cl
EVIDENCE = ROOT / 'tests/fixtures/evidence/incoming-controller-extraction-2026-09-30'
ORIGINAL = '/Users/ember/dev/fn/build/lanes/gpt61-extracted-product'

class IncomingControllerExtractionTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_paired_scalar_values_layout_and_fault_effects(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for ir_name in ('incoming-controller', 'incoming-controller-test'):
                source, inventory = cl.CL(json.loads((EVIDENCE / (ir_name + '.json')).read_text())).program()
                self.assertEqual(inventory['host-defined'], [])
                self.assertEqual(inventory['blocker'], [])
                (directory / (ir_name + '.lisp')).write_text(source)
            for name in ('driver', 'driver-test', 'driver-fault'):
                text = (EVIDENCE / (name + '.lisp')).read_text()
                text = text.replace(ORIGINAL + '/build/incoming-controller-export/build', str(directory))
                text = text.replace(ORIGINAL + '/tools/extract/clruntime.lisp', str(ROOT / 'tools/extract/clruntime.lisp'))
                driver = directory / (name + '.lisp')
                driver.write_text(text)
                run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(driver)],
                                     capture_output=True, text=True, timeout=30)
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                self.assertIn('PASS', run.stdout)
if __name__ == '__main__':
    unittest.main()
