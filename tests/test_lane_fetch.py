"""tools/lane_fetch.py: named branches only, and a stale ref lock named and cleared."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lane_fetch  # noqa: E402


def sh(cwd, *args):
    subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                   env=dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
                            GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t"))


class LaneFetchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.origin, self.clone = base / "origin", base / "clone"
        self.origin.mkdir()
        sh(self.origin, "init", "-q", "-b", "dev")
        sh(self.origin, "commit", "-q", "--allow-empty", "-m", "one")
        sh(self.origin, "branch", "lane/a")
        sh(base, "clone", "-q", str(self.origin), str(self.clone))
        sh(self.origin, "commit", "-q", "--allow-empty", "-m", "two")
        sh(self.origin, "branch", "-f", "lane/a", "dev")
        self.lock = self.clone / ".git/refs/remotes/origin/lane/a.lock"
        self.lock.parent.mkdir(parents=True, exist_ok=True)
        self.lock.write_text("")

    def tearDown(self):
        self.tmp.cleanup()

    def run_fetch(self, *branches, **kwargs):
        err = io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
            code = lane_fetch.fetch(list(branches), self.clone, **kwargs)
        return code, err.getvalue()

    def head(self, ref):
        return subprocess.run(["git", "rev-parse", ref], cwd=self.clone, text=True,
                              capture_output=True).stdout.strip()

    def test_a_named_branch_fetches_past_another_refs_stale_lock(self):
        code, err = self.run_fetch("dev")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.head("origin/dev"),
                         subprocess.run(["git", "rev-parse", "dev"], cwd=self.origin, text=True,
                                        capture_output=True).stdout.strip())

    def test_the_lock_is_named_and_cleared_only_when_stale(self):
        code, err = self.run_fetch("lane/a")
        self.assertNotEqual(code, 0)
        self.assertIn(str(self.lock), err)
        self.assertIn("--clear-stale", err)
        # Recent: --clear-stale leaves it.
        code, err = self.run_fetch("lane/a", clear_stale=True)
        self.assertNotEqual(code, 0)
        self.assertIn("recent", err)
        self.assertTrue(self.lock.exists())
        old = time.time() - 3600
        os.utime(self.lock, (old, old))
        code, err = self.run_fetch("lane/a", clear_stale=True)
        self.assertEqual(code, 0, err)
        self.assertFalse(self.lock.exists())
        self.assertIn("removed stale", err)


if __name__ == "__main__":
    unittest.main()
