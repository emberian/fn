"""Real staged files and deployed host/ACL2 forms; recorded snapshot/frame seams.

No saved-image claim: run test_native_state_checkpoint for the composed image.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which(os.environ.get("FN_SBCL", "sbcl")), "SBCL required")
class CheckpointImageReadback(unittest.TestCase):
    def test_stage_custody_and_readback(self):
        for mode in ("good", "page", "zero-page", "header", "raw-exit", "deferred"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory(prefix="fn-image-readback-") as directory:
                result = subprocess.run(
                    [os.environ.get("FN_SBCL", "sbcl"), "--noinform", "--script",
                     "tests/native_checkpoint_image_readback_raw.lisp", directory, mode],
                    cwd=ROOT, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("CHECKPOINT_IMAGE_READBACK_PASS " + mode, result.stdout)


if __name__ == "__main__":
    unittest.main()
