"""Check the shipped TCPCL-to-ACL2 composed admission boundary."""
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpChannelAdmissionTests(unittest.TestCase):
    def test_raw_eid_and_acl2_ingress_result(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_bp_channel_admission_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native BP parsed channel admission: PASS", output)
