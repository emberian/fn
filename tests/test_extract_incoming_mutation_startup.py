"""Actual compiled pool predicate and central gate, without RX activation."""
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
OLD = '/Users/ember/dev/fn/build/lanes/gpt61-extracted-product'
PRIOR = ROOT / 'planning/evidence/incoming-controller-extraction-2026-09-30'
EVIDENCE = ROOT / 'planning/evidence/incoming-controller-mutation-startup-2026-09-30'

class IncomingMutationStartupTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_real_export_predicate_selects_once_and_excludes_held_job(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name, location in [('incoming-controller-test', PRIOR), ('incoming-mutation-predicate', EVIDENCE)]:
                text, inventory = cl.CL(json.loads((location / (name + '.json')).read_text())).program()
                self.assertEqual(inventory['host-defined'], [])
                self.assertEqual(inventory['blocker'], [])
                (directory / (name + '.lisp')).write_text(text)
            text = (EVIDENCE / 'driver-mutation.lisp').read_text()
            text = text.replace(OLD + '/build/incoming-controller-export/build', str(directory))
            text = text.replace(OLD + '/tools/extract/clruntime.lisp', str(ROOT / 'tools/extract/clruntime.lisp'))
            driver = directory / 'driver-mutation.lisp'
            driver.write_text(text)
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(driver)],
                                 capture_output=True, text=True, timeout=30)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('PASS actual exported predicate startup', run.stdout)
if __name__ == '__main__':
    unittest.main()
