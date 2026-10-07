"""The TLS library probe runs before, never under, the initialization lock."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent.parent


class NativeTlsProbeOffLockTests(unittest.TestCase):
    def test_probe_is_not_under_the_initialization_lock(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script", "tests/native_tls_probe_off_lock_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=60, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output[-4000:])
        self.assertIn("native TLS probe off lock: PASS", output)
