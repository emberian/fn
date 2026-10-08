"""Compare actual decoded span/scalar realizers over two authenticated windows.

FN_XC2_NATIVE_CORE selects a warm developer core containing the decoded
controller and extent slot table. The fixture loads this tree's native span
functions into that core; it does not claim a rebuilt full-node image.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import zlib

ROOT = Path(__file__).resolve().parents[1]
CORE = os.environ.get("FN_XC2_NATIVE_CORE")
SBCL = os.environ.get("FN_XC2_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(CORE and SBCL, "needs FN_XC2_NATIVE_CORE and matching SBCL")
class NativeExtentDecodedSpanTests(unittest.TestCase):
    def test_actual_compressed_extent_span_matches_scalar_across_window(self):
        with tempfile.TemporaryDirectory(prefix="fn-xc2-span-") as directory:
            root = Path(directory)
            payload = bytes(i % 251 for i in range(20000))
            (root / "payload").write_bytes(payload)
            (root / "compressed").write_bytes(zlib.compress(payload, wbits=-15))
            result = subprocess.run(
                [SBCL, "--tls-limit", "20480", "--dynamic-space-size", "2048",
                 "--control-stack-size", "8192KB", "--core", CORE,
                 "--noinform", "--disable-debugger", "--load",
                 "tests/native_extent_decoded_span.lisp"],
                cwd=ROOT, env=dict(os.environ, FN_XC2_FIXTURE=directory),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stdout[-12000:])
            self.assertIn("native_extent_decoded_span: PASS", result.stdout)
