"""Exact native constructor/retention component; not an admission test."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'planning/evidence/native-connection-constructors-2026-09-30'


class ConnectionConstructorFamilyTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_current_family_positive_fault_and_retiring_overlap(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for name in ('subjects.lisp', 'measure.lisp', 'cases.lisp', 'run.lisp',
                         'collector-subject.lisp', 'collector-driver.lisp',
                         'collector-binding-subject.lisp', 'collector-binding-driver.lisp'):
                shutil.copyfile(EVIDENCE / name, target / name)
            for driver in ('run.lisp', 'collector-driver.lisp', 'collector-binding-driver.lisp'):
                run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                      '--script', driver], cwd=target,
                                     capture_output=True, text=True, timeout=30)
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                if driver == 'run.lisp':
                    self.assertIn('PASS exact service/node/mux intrusive live-retiring-release effects', run.stdout)
                    self.assertIn('PASS injected before/after-constructor escape preserves raw token', run.stdout)
                    self.assertIn('PASS exact scalar fault/escape tags preserve cause without rendering', run.stdout)
                    self.assertIn('HASH-DEFAULT-BACKING shared=T', run.stdout)
                    self.assertIn('PASS actual fixed fault paths measured', run.stdout)
                elif driver == 'collector-driver.lisp':
                    self.assertIn('PASS installation-only collector constructor', run.stdout)
                else:
                    self.assertIn('PASS collector binding factory/selection-fault object scope', run.stdout)


if __name__ == '__main__':
    unittest.main()
