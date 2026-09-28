"""tools/deploy_gate.py against a local fake host: no ssh, no image, no network.

The gate's own logic is what is under test here -- the order of the phases,
the port it parses out of the owner's LISTENING line, a reader held live
across another connection's POST, the SIGKILL cut and the reread after the
restart, the three outcomes staying distinct in the exit codes, and the
evidence it renders.  `--dry-run --home DIR` runs every script the gate would
send over ssh through bash on this machine with HOME pointed at DIR, and the
native image is the stand-in tests/inn_lab_fake/native/fn-host.  A green run
here says the harness works; it says nothing about fn.
"""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import deploy_gate  # noqa: E402

class Recorder(deploy_gate.Host):
    """A host that answers nothing and remembers every script it was given."""

    label = "recorder"

    def __init__(self, replies=None):
        self.scripts = []
        self.replies = replies or {}

    def sh(self, script, timeout):
        self.scripts.append(script)
        for needle, (rc, out) in self.replies.items():
            if needle in script:
                return subprocess.CompletedProcess([], rc, out.encode(), b"")
        return subprocess.CompletedProcess([], 0, b"", b"")


class DeployIdentityTests(unittest.TestCase):
    def gate(self, host, tree="dev"):
        return deploy_gate.DeployGate(host, ROOT, "a" * 40, "abc1234", tree)

    def test_tree_and_revision_name_both_the_directory_and_lock(self):
        first = self.gate(Recorder(), "dev")
        second = self.gate(Recorder(), "release")
        self.assertEqual(first.deploy, "$HOME/fn-deploy/dev-abc1234")
        self.assertEqual(first.deploy_lock,
                         "$HOME/fn-deploy/.locks/dev-abc1234.lock")
        self.assertNotEqual(first.deploy, second.deploy)
        self.assertNotEqual(first.deploy_lock, second.deploy_lock)


class StepAccountingTests(unittest.TestCase):
    def test_an_expected_nonzero_code_is_not_a_failure(self):
        refusal = deploy_gate.Step("refused", "cmd", 1, "", 0.0, expect=1)
        self.assertFalse(refusal.failed)
        self.assertTrue(deploy_gate.Step("accepted", "cmd", 1, "", 0.0).failed)
        probe = deploy_gate.Step("probe", "cmd", 1, "", 0.0, expect=None)
        self.assertFalse(probe.failed, "a probe the gate falls back from is not a pass")

    def test_a_skipped_step_is_never_a_pass(self):
        gate = deploy_gate.DeployGate(Recorder(), ROOT, "a" * 40, "abc1234", "dev")
        gate.skip("slrn", "slrn batch", "not installed")
        self.assertIsNone(gate.steps[0].rc)
        self.assertFalse(gate.steps[0].exercised)
        self.assertIn("slrn: not installed", gate.gaps)


class UncertainArmTests(unittest.TestCase):
    def test_without_a_developer_image_the_distinctness_is_not_exercised(self):
        gate = deploy_gate.DeployGate(Recorder(), ROOT, "a" * 40, "abc1234", "dev",
                                      native_image="/box/fn-host")
        gate.three_outcomes()
        found = [one for one in gate.found if one.key == "outcomes-distinct"]
        self.assertEqual([one.verdict for one in found], [deploy_gate.NOT_EXERCISED])
        self.assertIn("NativeOperatorUncertainOutcomeTests", found[0].blocker)


class DryRunTests(unittest.TestCase):
    """The whole gate, end to end, against a stand-in image in a temporary HOME."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-deploy-gate-")
        cls.home = Path(cls.temp.name) / "home"
        cls.home.mkdir()
        # The ship step is `git archive <commit>` (LocalHost.deploy): a tree
        # with no repository cannot be deployed, so skip on that structural
        # condition rather than error.
        try:
            commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    check=True).stdout.decode().strip()
        except (subprocess.CalledProcessError, FileNotFoundError) as error:
            cls.temp.cleanup()
            raise unittest.SkipTest(
                "the deploy gate dry run needs a git repository at {} ({})".format(
                    ROOT, error))
        cls.rev = commit[:7]
        cls.evidence = Path(cls.temp.name) / "deploy-evidence.md"
        image = str(ROOT / "tests/inn_lab_fake/native/fn-host")
        with contextlib.redirect_stdout(io.StringIO()):
            cls.code = deploy_gate.main([
                commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
                "--native-image", image, "--developer-image", image,
                "--nntplib-python", "none", "--evidence", str(cls.evidence), "--keep"])
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def named(self, fragment):
        return [line for line in self.text.splitlines()
                if line.startswith("| ") and fragment in line]

    def test_the_gate_completed(self):
        self.assertEqual(self.code, 0, self.text[-3000:])
        self.assertNotIn("gate error", self.text)

    def test_the_owner_reached_listening(self):
        rows = self.named("start server (owner, main)")
        self.assertTrue(rows and "| 0 |" in rows[0], rows)
        rows = self.named("entry-point-listening")
        self.assertTrue(rows and "| held |" in rows[0], rows)

    def test_the_three_outcomes_stay_distinct(self):
        self.assertIn("accepted=0 refused=1 uncertain=3", self.text)

    def test_every_phase_ran(self):
        for phase in ("ship archive", "operator init", "outcome accepted",
                      "outcome refused", "outcome uncertain", "the owner fenced itself",
                      "drive transcript", "drive concurrent", "kill -9 mid-session",
                      "reread after recovery"):
            self.assertTrue(self.named(phase), "{} is missing from the evidence".format(phase))

    def test_the_reader_survived_the_post_and_the_reread_found_everything(self):
        store = self.home / "fn-deploy/dev-{}/node/store/fake-native.json".format(self.rev)
        ids = set(json.loads(store.read_text())["articles"])
        self.assertIn(deploy_gate.SEED_ID, ids)
        self.assertIn(deploy_gate.POSTED_ID, ids, "the POST over the socket did not commit")
        self.assertNotIn("<interrupted@example.invalid>", ids,
                         "the POST the SIGKILL interrupted must not be durable")

    def test_the_kill_actually_killed_the_server(self):
        rows = self.named("server is gone")
        self.assertTrue(rows and "GONE" in rows[0], rows)

    def test_the_gaps_are_written_out(self):
        self.assertIn("## What was NOT exercised", self.text)
        self.assertIn("nntplib", self.text)
        self.assertTrue("no news client is installed on the host" in self.text
                        or self.named("scripted slrn session")
                        or self.named("scripted tin session"), self.text[-2000:])
        self.assertIn("not a power loss", self.text)

    def test_the_evidence_records_versions_and_commands(self):
        self.assertIn("| python3 |", self.text)
        self.assertIn("| native image |", self.text)
        self.assertIn("### Commands in full", self.text)


class RepoRootTests(unittest.TestCase):
    """Evidence goes to the tree the command was invoked from.

    The defect: a lane working in `build/lanes/w6-peering-inbound-2` ran
    a two-node gate and `planning/evidence/twonode-<rev>-<date>.md`
    was written into the MAIN checkout `/Users/ember/dev/fn`, where it sat
    untracked and blocked a merge.  The cause is that every harness anchored
    its evidence on `Path(__file__).resolve().parents[1]` -- the tree the
    SCRIPT lives in -- so running the main checkout's copy of a harness from
    a lane writes into the main checkout.  A relative `--evidence` was worse
    still: it followed the process's working directory.

    This builds a real repository with a real secondary `git worktree` and
    resolves from inside it, because that is the shape that broke: a
    `git rev-parse --show-toplevel` from a worktree answers the worktree, and
    nothing about the two trees' contents distinguishes them.
    """

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        base = Path(self.directory.name).resolve()
        self.main = base / "main"
        for marker in deploy_gate.FN_TREE_MARKERS:
            (self.main / marker).mkdir(parents=True)
            # git tracks files, not directories, so a marker directory that
            # holds nothing does not reach the secondary worktree at all.
            (self.main / marker / "kept").write_text("# a stand-in\n")
        self.git("init", "-q", "-b", "dev", cwd=self.main)
        self.git("add", "-A", cwd=self.main)
        # `commit.gpgsign` in the developer's global config makes this commit
        # block on a signing agent, which a unit test must never depend on.
        self.git("-c", "user.email=t@example.invalid", "-c", "user.name=t",
                 "-c", "commit.gpgsign=false", "-c", "gpg.format=openpgp",
                 "commit", "-qm", "tree", cwd=self.main)
        self.lane = base / "lane"
        self.git("worktree", "add", "-q", "-b", "lane", str(self.lane), "dev",
                 cwd=self.main)

    def git(self, *arguments, cwd):
        # A bounded wait: git that blocks on a prompt is a hung test suite,
        # not a slow one.
        subprocess.run(["git", "-C", str(cwd), *arguments], check=True,
                       stdin=subprocess.DEVNULL, timeout=60,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def test_a_secondary_worktree_is_the_root_not_the_checkout_it_came_from(self):
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(deploy_gate.repo_root(self.lane), self.lane)
            self.assertEqual(deploy_gate.repo_root(self.main), self.main)
        # The same answer with no argument, which is how the harnesses call
        # it: the process's working directory decides, not this file's path.
        with contextlib.chdir(self.lane / "books"), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(deploy_gate.repo_root(), self.lane)

    def test_two_fn_trees_in_play_are_announced_on_every_run(self):
        """Three blocked merges came from an ambiguity nothing printed.

        The lane's tree and the harness file's tree hold the same file
        names, so a record written to the wrong one looks right until git
        refuses the merge. Saying which was chosen makes the next occurrence
        readable in the log.
        """
        printed, out = io.StringIO(), io.StringIO()
        with contextlib.redirect_stderr(printed), contextlib.redirect_stdout(out):
            chosen = deploy_gate.repo_root(self.lane)
        self.assertEqual(chosen, self.lane)
        # stdout belongs to the harness's own report, which a caller parses.
        self.assertEqual(out.getvalue(), "")
        said = printed.getvalue()
        self.assertIn(str(self.lane), said)
        self.assertIn(str(deploy_gate.ROOT), said)
        self.assertIn("INVOKED from", said)
        # Nothing to announce when the two are the same tree.
        quiet = io.StringIO()
        with contextlib.redirect_stderr(quiet):
            deploy_gate.repo_root(deploy_gate.ROOT)
        self.assertEqual(quiet.getvalue(), "")

    def test_a_directory_outside_any_fn_tree_falls_back_to_this_file_s_tree(self):
        outside = Path(self.directory.name).resolve() / "elsewhere"
        outside.mkdir()
        self.assertEqual(deploy_gate.repo_root(outside), deploy_gate.ROOT)
        # A real repository that is not an fn tree is a fallback too: only a
        # tree with this project's directories in it can be meant.
        stranger = Path(self.directory.name).resolve() / "stranger"
        stranger.mkdir()
        self.git("init", "-q", cwd=stranger)
        self.assertEqual(deploy_gate.repo_root(stranger), deploy_gate.ROOT)

    def test_the_default_and_a_relative_evidence_path_both_land_in_that_tree(self):
        self.assertEqual(
            deploy_gate.evidence_path(None, self.lane, "twonode-abc-2026-09-20.md"),
            self.lane / "planning" / "evidence" / "twonode-abc-2026-09-20.md")
        self.assertEqual(
            deploy_gate.evidence_path("planning/evidence/x.md", self.lane, "d.md"),
            self.lane / "planning" / "evidence" / "x.md")
        # An absolute path is still taken as given: writing outside the tree
        # on purpose stays possible.
        self.assertEqual(
            deploy_gate.evidence_path("/tmp/elsewhere.md", self.lane, "d.md"),
            Path("/tmp/elsewhere.md"))

    def test_every_harness_anchors_its_evidence_on_the_invoking_tree(self):
        """No harness may reintroduce `--repo default=str(ROOT)`."""
        tools = Path(__file__).resolve().parent.parent / "tools"
        for name in ("deploy_gate", "inn_lab", "verdict"):
            text = (tools / f"{name}.py").read_text()
            self.assertNotIn('"--repo", default=str(ROOT)', text, name)
            self.assertIn("if args.repo else repo_root()", text, name)
            self.assertIn("evidence_path(args.evidence, repo", text, name)


if __name__ == "__main__":
    unittest.main()
