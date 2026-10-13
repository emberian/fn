"""Real host OVER lease code with controlled book boundary decisions."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

class OverLeaseRawTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL absent')
    def test_pool_lease_call_sequence(self):
        result = subprocess.run(['sbcl', '--noinform', '--disable-debugger', '--script',
                                 'tests/native_over_lease_raw.lisp'], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout[-6000:])
        self.assertIn('OVER pool lease host sequence: PASS', result.stdout)
        self.assertIn('OVER false routing uses generic entry: PASS', result.stdout)
        self.assertIn('OVER false routing retains ARTICLE entry: PASS', result.stdout)
        self.assertIn('OVER refused window faults before a send: PASS', result.stdout)
