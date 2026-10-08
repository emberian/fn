"""tools/host_check.py: a check that did not run is never a pass; --loaded (Q7k).

Batch AY's obstruction report: plain `host_check` printed SKIPPED and exited
0 without FN_ACL2 (every make check so far).  Without an ACL2 each ACL2 mode
must exit 2 (NOT RUN), which make check's step table counts as failed.
"""
import os
import subprocess
import sys
import unittest
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import host_check  # noqa: E402


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


def tree(tmp: str) -> Path:
    root = Path(tmp)
    (root / "host" / "native").mkdir(parents=True)
    (root / "host/native/build.lisp").write_text('(ld "host/served-host.lisp")\n')
    (root / "host/native/build-store-test.lisp").write_text('(ld "host/test-image-host.lisp")\n')
    (root / "host/served-host.lisp").write_text("(defun s () 1)\n")
    (root / "host/test-image-host.lisp").write_text("(defun t1 () 1)\n")
    return root


class HostLoadedTests(unittest.TestCase):
    def test_every_loaded_file_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(host_check.loaded_findings(tree(tmp), {}), [])

    def test_an_unloaded_host_file_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = tree(tmp)
            (root / "host/native/proto-thing.lisp").write_text("(defun p () 1)\n")
            found = host_check.loaded_findings(root, {})
            self.assertEqual(len(found), 1)
            self.assertTrue(found[0].startswith("host/native/proto-thing.lisp: no build loads it"))
            self.assertEqual(host_check.loaded_findings(
                root, {"host/native/proto-thing.lisp": "why"}), [])

    def test_known_only_shrinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = tree(tmp)
            found = host_check.loaded_findings(
                root, {"host/served-host.lisp": "why", "host/gone.lisp": "why"})
            self.assertEqual(sorted(f.split(":")[0] for f in found),
                             ["host/gone.lisp", "host/served-host.lisp"])
            self.assertTrue(any("a build loads it now" in f for f in found))
            self.assertTrue(any("it is gone" in f for f in found))

    def test_the_tree_is_clean(self):
        self.assertEqual(host_check.loaded_findings(), [])


if __name__ == "__main__":
    unittest.main()
