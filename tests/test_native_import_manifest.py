"""Real FIFO substitution cannot block streamed import MANIFEST admission."""
import shutil
import subprocess
import unittest


class ImportManifestTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_manifest_descriptor_admission(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_import_manifest_raw.lisp"],
            text=True, capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("regular/FIFO ingress passed (3 paths)", result.stdout)
