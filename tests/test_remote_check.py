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
    # No signing in the temporary repository: on the laptop a signing agent
    # hung each commit for 60 s (batch AZ, 2026-09-28).
    subprocess.run(["git", "-C", str(tree), "-c", "commit.gpgsign=false", *words],
                   check=True, capture_output=True,
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
                    "FN_ACL2": "/nonexistent/acl2", "FN_REMOTE_CHECK_POLL": "0.2"}
        self.env.pop("FN_LANE", None)

    def tearDown(self):
        self.scratch.cleanup()

    def run_check(self, *words):
        return subprocess.run(["sh", str(SCRIPT), "hbox", *words], cwd=self.lane,
                              env=self.env, capture_output=True, text=True, timeout=120)

    def test_committed_head_runs_there_and_make_status_is_the_exit(self):
        done = self.run_check()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertNotIn("dirty", done.stdout)  # a fresh clone is not a dirty tree
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
        self.assertIn("the box tree was dirty; discarding:", done.stdout)
        self.assertIn("stray.txt", done.stdout)
        done = self.run_check("--no-dirty")
        self.assertEqual((tree / "marker.txt").read_text(), "one\n")

    def test_fetch_brings_a_generated_path_back(self):
        done = self.run_check("--target", "gen", "--fetch", "out/file.txt")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual((self.lane / "out/file.txt").read_text(), "generated\n")

    def test_fetch_keeps_a_file_changed_here_while_the_box_ran(self):
        # A fetch clobbered a lane's newer ledger files (2026-09-28).
        (self.lane / "Makefile").write_text(
            "check-lane:\n\t@true\n"
            "gen:\n\t@mkdir -p out && echo box > out/a.txt && echo box > out/b.txt\n")
        (self.lane / "out").mkdir()
        (self.lane / "out/a.txt").write_text("shipped\n")
        git(self.lane, "add", ".")
        git(self.lane, "commit", "-q", "-m", "gen")
        # The box's make edits this worktree's out/a.txt mid-run, as a lane's
        # merge or commit would; out/b.txt was absent when shipped.
        self.env["FN_REMOTE_CHECK_WRAP"] = f"echo newer > {self.lane}/out/a.txt;"
        done = self.run_check("--target", "gen", "--fetch", "out")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual((self.lane / "out/a.txt").read_text(), "newer\n")
        self.assertEqual((self.lane / "build/remote-check/fetched/out/a.txt").read_text(),
                         "box\n")
        self.assertIn("kept this worktree's out/a.txt", done.stderr)
        self.assertEqual((self.lane / "out/b.txt").read_text(), "box\n")

    def test_cmd_runs_one_command_in_the_box_tree(self):
        done = self.run_check("--cmd", "cat marker.txt; echo \"it's $((1 + 1))\"")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("it's 2", done.stdout)
        self.assertTrue((self.lane / "build/remote-check/hbox-cmd.log").is_file())
        failed = self.run_check("--cmd", "exit 7")
        self.assertEqual(failed.returncode, 7, failed.stdout + failed.stderr)

    def test_ship_carries_an_untracked_helper_with_the_run(self):
        # obstructions-5 item 38.
        (self.lane / "tools").mkdir()
        (self.lane / "tools" / "helper.sh").write_text("echo helper-ran\n")
        without = self.run_check("--cmd", "sh tools/helper.sh")
        self.assertNotEqual(without.returncode, 0, without.stdout)
        self.assertIn("NOT shipped", without.stdout)
        self.assertIn("  tools/helper.sh", without.stdout)
        done = self.run_check("--ship", "tools/helper.sh", "--cmd", "sh tools/helper.sh")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("helper-ran", done.stdout)
        self.assertIn("shipped tools/helper.sh", done.stdout)
        self.assertNotIn("  tools/helper.sh", done.stdout)  # not in the NOT-shipped list
        refused = self.run_check("--ship", "../outside", "--cmd", "true")
        self.assertEqual(refused.returncode, 2)

    def test_attach_recovers_a_run_whose_local_side_died(self):
        # obstructions-5 item 41: the box run kept going after the local side
        # died; attach re-reads its log to the end without re-running.
        done = self.run_check("--cmd", "echo first-run")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        log = self.box / "my-lane-check.log"
        self.assertEqual((self.box / "my-lane-check.log.head").read_text().split()[1], "cmd")
        # The box's log as a run left it that exited 5, and nothing reruns it.
        log.write_text("== remote_check x\nstep output\n== make exit 5\n")
        (self.box / "my-lane-check.log.run.sh").write_text("echo SHOULD-NOT-RUN\n")
        attached = subprocess.run(["sh", str(SCRIPT), "attach", "hbox"], cwd=self.lane,
                                  env=self.env, capture_output=True, text=True, timeout=60)
        self.assertEqual(attached.returncode, 5, attached.stdout + attached.stderr)
        self.assertIn("attach: the run of", attached.stdout)
        self.assertIn("step output", (self.lane / "build/remote-check/hbox-cmd.log").read_text())
        self.assertNotIn("SHOULD-NOT-RUN", log.read_text())

    def test_attach_without_a_run_says_so(self):
        attached = subprocess.run(["sh", str(SCRIPT), "attach", "hbox"], cwd=self.lane,
                                  env=self.env, capture_output=True, text=True, timeout=60)
        self.assertEqual(attached.returncode, 3)
        self.assertIn("no run of lane my-lane", attached.stderr)

    def test_ship_carries_an_untracked_helper_with_its_mode(self):
        helper = self.lane / "build" / "helpers" / "probe.sh"
        helper.parent.mkdir(parents=True)
        helper.write_text("#!/bin/sh\necho probe-ran\n")
        helper.chmod(0o755)
        (self.lane / "notes.txt").write_text("left here\n")
        done = self.run_check("--no-install-certs", "--ship", "build/helpers/probe.sh",
                              "--cmd", "./build/helpers/probe.sh; test ! -e notes.txt")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("shipped build/helpers/probe.sh", done.stdout)
        self.assertIn("probe-ran", done.stdout)
        self.assertIn("notes.txt", done.stdout.split("NOT shipped")[1])
        for bad in ("/etc/passwd", "../x", "missing.sh"):
            refused = self.run_check("--ship", bad, "--cmd", "true")
            self.assertEqual(refused.returncode, 2, bad)

    def test_certificates_install_by_default_and_regen_fetches_the_generated_files(self):
        (self.lane / "tools").mkdir()
        (self.lane / "tools/certs.py").write_text("print('  installed 3')\n")
        (self.lane / "tools/ledger.py").write_text(
            "import pathlib\nfor n in ('ledger.json', 'ledger.md', 'proofs.json'):\n"
            "    pathlib.Path('planning', n).write_text('regen ' + n)\n")
        (self.lane / "tools/current_view.py").write_text(
            "import pathlib\npathlib.Path('planning/current.md').write_text('regen current')\n")
        (self.lane / "planning").mkdir()
        for name in ("ledger.json", "ledger.md", "proofs.json", "current.md"):
            (self.lane / "planning" / name).write_text("old\n")
        git(self.lane, "add", ".")
        git(self.lane, "commit", "-q", "-m", "tools")
        done = self.run_check("--regen")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        log = (self.lane / "build/remote-check/hbox-regen.log").read_text()
        self.assertIn("== certs install:   installed 3", log)
        self.assertEqual((self.lane / "planning/current.md").read_text(), "regen current")
        self.assertEqual((self.lane / "planning/proofs.json").read_text(), "regen proofs.json")
        skipped = self.run_check("--no-install-certs", "--cmd", "true")
        self.assertNotIn("certs install", (self.lane / "build/remote-check/hbox-cmd.log")
                         .read_text())
        self.assertEqual(skipped.returncode, 0)
        self.assertEqual(self.run_check("--regen", "--cmd", "true").returncode, 2)

    def test_unknown_box_and_option_are_usage(self):
        done = subprocess.run(["sh", str(SCRIPT), "nobox"], cwd=self.lane, env=self.env,
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 2)
        bogus = self.run_check("--bogus")
        self.assertEqual(bogus.returncode, 2)
        self.assertIn("--log BOXPATH", bogus.stderr)
        self.assertIn("a path ON THE BOX", bogus.stderr)


if __name__ == "__main__":
    unittest.main()
