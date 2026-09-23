"""Current BP config must authorize at the serialized publication decision."""
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpNodeAdmissionLockTests(unittest.TestCase):
    def test_revocation_between_preflight_and_lock_refuses_both_classes(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_bp_node_admission_lock_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native BP serialized admission: PASS", output)
