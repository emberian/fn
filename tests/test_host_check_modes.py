"""tools/host_check.py: a check that did not run is never a pass.

Batch AY's obstruction report: plain `host_check` printed SKIPPED and exited
0 without FN_ACL2 (every make check so far).  Without an ACL2 each ACL2 mode
must exit 2 (NOT RUN), which make check's step table counts as failed.
"""
import os
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(*args):
    env = {k: v for k, v in os.environ.items() if k != "FN_ACL2"}
    env["FN_ACL2"] = ""
    env["PATH"] = "/usr/bin:/bin"  # no acl2 here
    return subprocess.run([sys.executable, str(ROOT / "tools/host_check.py"), *args],
                          cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)


class NotRunIsNotAPassTests(unittest.TestCase):
    def test_the_default_build_order_check_without_acl2_is_not_run(self):
        result = run()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("NOT RUN host/native/build.lisp", result.stdout)
        self.assertIn("NOT RUN host/native/build-dtn.lisp", result.stdout)

    def test_alone_without_acl2_is_not_run(self):
        result = run("--alone", "host/store-host.lisp")
        self.assertEqual(result.returncode, 2)
        self.assertIn("NOT RUN", result.stderr)

    def test_load_without_acl2_is_not_run(self):
        result = run("--load")
        self.assertEqual(result.returncode, 2)
        self.assertIn("FN_ACL2", result.stderr)

    def test_files_without_a_mode_are_a_usage_error(self):
        result = run("host/store-host.lisp")
        self.assertEqual(result.returncode, 2)
        self.assertIn("--alone", result.stderr)


if __name__ == "__main__":
    unittest.main()
