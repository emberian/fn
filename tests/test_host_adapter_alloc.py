"""host/adapter.lisp's per-turn reuse: op reset, scratch vectors, boundary fast path.

The SBCL tier runs the real adapter forms with a stand-in TLS table. The ACL2
tier includes the certified books/tls-record-state and checks the reset against
the real fn2-tls-record stobj; it needs FN_ACL2 and that book's certificate.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = "tests/native-adapter-alloc.lsp"
MARKERS = ("ALLOC-SCRATCH-OK", "ALLOC-BOUNDARY-OK")


def acl2_launcher():
    configured = os.environ.get("FN_ACL2", "")
    if not configured:
        return None
    path = Path(configured).expanduser() if os.sep in configured else shutil.which(configured)
    return str(path) if path and os.access(path, os.X_OK) else None


class HostAdapterAllocTests(unittest.TestCase):
    def check(self, output, record):
        self.assertIn(f"ALLOC-RESET-OK {record}", output)
        for marker in MARKERS:
            self.assertIn(marker, output)

    def test_sbcl_tier(self):
        result = subprocess.run(["sbcl", "--script", FIXTURE], cwd=ROOT,
                                env=dict(os.environ, FN2_ALLOC_REAL_STOBJ="0"),
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.check(result.stdout, "stand-in-record")

    def test_real_stobj_tier(self):
        launcher = acl2_launcher()
        if launcher is None:
            self.skipTest("FN_ACL2 is not set to an executable ACL2")
        if not (ROOT / "books/tls-record-state.cert").is_file():
            self.skipTest("books/tls-record-state is not certified in this tree")
        driver = ('(include-book "books/tls-record-state")\n'
                  '(defttag :fn-alloc-test)\n'
                  f'(progn! (set-raw-mode t) (load "{FIXTURE}"))\n'
                  '(good-bye)\n')
        result = subprocess.run([launcher], cwd=ROOT, input=driver,
                                env=dict(os.environ, FN2_ALLOC_REAL_STOBJ="1"),
                                capture_output=True, text=True, timeout=600)
        self.assertNotIn("ACL2 Error", result.stdout, result.stdout[-4000:])
        self.check(result.stdout, "real-stobj")


if __name__ == "__main__":
    sys.exit(unittest.main())
