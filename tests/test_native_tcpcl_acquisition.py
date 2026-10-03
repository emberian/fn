"""Real trace streams close when spool admission or socket cleanup fails."""
import shutil
import subprocess
import unittest


class TcpclAcquisitionTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_acquisition_escapes_and_independent_cleanup(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_tcpcl_acquisition_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("TCPCL command acquisition cleanup passed (8 paths)", result.stdout)
