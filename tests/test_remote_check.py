"""tools/remote_check.sh: bundle a worktree, check it out on a box, run make there.

The box is a local directory and the ssh a local shell (FN_REMOTE_CHECK_SSH),
so these run anywhere; the real path differs only in the transport.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "remote_check.sh"
GIT_ENV = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
           "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}


def git(tree, *words):
    subprocess.run(["git", "-C", str(tree), *words], check=True, capture_output=True,
                   env={**os.environ, **GIT_ENV})


class RemoteCheckTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        base = Path(self.scratch.name)
        self.lane = base / "lanes" / "my-lane"
        self.box = base / "box"
        self.box.mkdir()
        self.lane.mkdir(parents=True)
        git(self.lane, "init", "-q")
        (self.lane / "Makefile").write_text(
            "check-lane:\n\t@cat marker.txt\n\t@test \"$$(cat marker.txt)\" != red\n"
            "gen:\n\t@mkdir -p out && echo generated > out/file.txt\n")
        (self.lane / "marker.txt").write_text("one\n")
        git(self.lane, "add", ".")
        git(self.lane, "commit", "-q", "-m", "base")
        fake_ssh = base / "fake-ssh"
        fake_ssh.write_text("#!/bin/sh\nshift\nexec sh -c \"$1\"\n")
        fake_ssh.chmod(0o755)
        self.env = {**os.environ, **GIT_ENV, "FN_REMOTE_CHECK_SSH": str(fake_ssh),
                    "FN_REMOTE_CHECK_BASE": str(self.box), "FN_REMOTE_CHECK_WRAP": "",
                    "FN_ACL2": "/nonexistent/acl2"}
        self.env.pop("FN_LANE", None)

    def tearDown(self):
        self.scratch.cleanup()

    def run_check(self, *words):
        return subprocess.run(["sh", str(SCRIPT), "hbox", *words], cwd=self.lane,
                              env=self.env, capture_output=True, text=True, timeout=120)

    def test_committed_head_runs_there_and_make_status_is_the_exit(self):
        done = self.run_check()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        tree = self.box / "my-lane-check"
        self.assertEqual((tree / "marker.txt").read_text(), "one\n")
        self.assertIn("exit 0", done.stdout)
        self.assertTrue((self.lane / "build/remote-check/hbox-check-lane.log").exists())
        # A red make is the script's exit, and the second run ships only the new commit.
        (self.lane / "marker.txt").write_text("red\n")
        git(self.lane, "commit", "-q", "-am", "red")
        done = self.run_check()
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertEqual((tree / "marker.txt").read_text(), "red\n")

    def test_dirty_changes_ride_on_top_and_a_dirty_box_tree_is_reset(self):
        self.assertEqual(self.run_check().returncode, 0)
        tree = self.box / "my-lane-check"
        (tree / "marker.txt").write_text("left over by a regeneration\n")
        (tree / "stray.txt").write_text("untracked\n")
        (self.lane / "marker.txt").write_text("edited, not committed\n")
        done = self.run_check()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual((tree / "marker.txt").read_text(), "edited, not committed\n")
        self.assertFalse((tree / "stray.txt").exists())
        self.assertIn("applying 1 uncommitted", done.stdout)
        done = self.run_check("--no-dirty")
        self.assertEqual((tree / "marker.txt").read_text(), "one\n")

    def test_fetch_brings_a_generated_path_back(self):
        done = self.run_check("--target", "gen", "--fetch", "out/file.txt")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual((self.lane / "out/file.txt").read_text(), "generated\n")

    def test_unknown_box_and_option_are_usage(self):
        done = subprocess.run(["sh", str(SCRIPT), "nobox"], cwd=self.lane, env=self.env,
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 2)
        self.assertEqual(self.run_check("--bogus").returncode, 2)


if __name__ == "__main__":
    unittest.main()
