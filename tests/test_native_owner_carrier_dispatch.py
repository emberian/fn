"""Execute native wrapper ABI checks; no image or semantic owner claim."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class OwnerCarrierDispatchTests(unittest.TestCase):
    def test_actual_native_stobj_routing(self):
        sbcl = os.environ.get("FN_SBCL") or shutil.which("sbcl")
        if not sbcl:
            raise unittest.SkipTest("SBCL is not available")
        result = subprocess.run(
            [sbcl, "--noinform", "--script", "tests/native_owner_carrier_dispatch_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native_owner_carrier_dispatch: PASS", output)
