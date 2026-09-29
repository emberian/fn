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


class RevertCheckTests(unittest.TestCase):
    """obstructions-8 item 69: a merge of dev that brings in a revert of the
    lane's own work is named, and --merge refuses it without --allow-revert."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        r = self.repo
        sh(r, "init", "-q", "-b", "dev")
        sh(r, "config", "user.name", "t")
        sh(r, "config", "user.email", "t@t")
        sh(r, "config", "commit.gpgsign", "false")
        (r / "base").write_text("base\n")
        sh(r, "add", "base")
        sh(r, "commit", "-q", "-m", "base")
        sh(r, "checkout", "-q", "-b", "lane/mine")
        (r / "mine").write_text("work\n")
        sh(r, "add", "mine")
        sh(r, "commit", "-q", "-m", "my work")
        sh(r, "checkout", "-q", "-b", "lane/other", "dev")
        (r / "other").write_text("theirs\n")
        sh(r, "add", "other")
        sh(r, "commit", "-q", "-m", "their work")
        sh(r, "checkout", "-q", "dev")
        sh(r, "merge", "-q", "--no-ff", "-m", "Merge lane/mine", "lane/mine")
        sh(r, "merge", "-q", "--no-ff", "-m", "Merge lane/other", "lane/other")
        sh(r, "checkout", "-q", "lane/mine")
        (r / "mine2").write_text("more work\n")
        sh(r, "add", "mine2")
        sh(r, "commit", "-q", "-m", "more of my work")

    def tearDown(self):
        self.tmp.cleanup()

    def revert(self, subject):
        sha = subprocess.run(["git", "log", "-1", "--format=%H", "--grep", subject, "dev"],
                             cwd=self.repo, text=True, capture_output=True).stdout.strip()
        sh(self.repo, "checkout", "-q", "dev")
        sh(self.repo, "revert", "--no-edit", "-m", "1", sha)
        sh(self.repo, "checkout", "-q", "lane/mine")

    def merge(self, allow=False):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = lane_fetch.merge("dev", self.repo, allow)
        return code, out.getvalue() + err.getvalue()

    def test_no_revert_merges_and_says_so(self):
        code, text = self.merge()
        self.assertEqual(code, 0, text)
        self.assertIn("no revert commit in HEAD..dev", text)

    def test_a_revert_of_another_lane_is_listed_and_merged(self):
        self.revert("Merge lane/other")
        found = lane_fetch.incoming_reverts("dev", self.repo)
        self.assertEqual([(r["subject"], r["ours"]) for r in found],
                         [('Revert "Merge lane/other"', False)])
        code, text = self.merge()
        self.assertEqual(code, 0, text)
        self.assertIn('Revert "Merge lane/other"', text)
        self.assertNotIn("REVERTS THIS LANE", text)

    def test_a_revert_of_this_lanes_merge_is_refused_then_allowed(self):
        self.revert("Merge lane/mine")
        found = lane_fetch.incoming_reverts("dev", self.repo)
        self.assertEqual(len(found), 1)
        self.assertTrue(found[0]["ours"])
        before = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, text=True,
                                capture_output=True).stdout
        code, text = self.merge()
        self.assertEqual(code, 4)
        self.assertIn("REVERTS THIS LANE'S WORK", text)
        self.assertIn("refusing to merge dev", text)
        self.assertEqual(subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, text=True,
                                        capture_output=True).stdout, before)
        code, text = self.merge(allow=True)
        self.assertEqual(code, 0, text)

    def test_ownership_by_the_first_parent_chain_without_a_branch_name(self):
        self.revert("Merge lane/mine")
        found = lane_fetch.incoming_reverts("dev", self.repo, branch="lane/renamed")
        self.assertTrue(found[0]["ours"])  # the merged commit is on HEAD's first-parent chain


if __name__ == "__main__":
    unittest.main()
