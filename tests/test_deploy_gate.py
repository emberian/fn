"""tools/deploy_gate.py against a local fake host: no ssh, no ACL2, no network.

The gate's own logic is what is under test here -- the order of the phases,
the choice between a host gate's certificates and certifying on the host, the
port it parses out of the server's first line, a reader held live across
another connection's POST, the SIGKILL cut and the reread after recovery, the
three outcomes staying distinct in the exit codes, and the evidence it
renders.  `--dry-run --home DIR` runs every script the gate would send over
ssh through bash on this machine with HOME pointed at DIR, and `--overlay`
puts the fake entry points in `tests/deploy_gate_fake/` over the deployed
tree.  A green run here says the harness works; it says nothing about fn.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import deploy_gate  # noqa: E402

FAKE_ACL2 = "#!/bin/sh\necho 'ACL2 Version 8.7 fake'\ncat > /dev/null\nexit 0\n"


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


class CertificateChoiceTests(unittest.TestCase):
    """The host's own gate is preferred; its absence is a certification run."""

    def gate(self, host, tree="dev"):
        return deploy_gate.DeployGate(host, ROOT, "a" * 40, "abc1234", tree)

    def test_a_host_gate_supplies_the_certificates(self):
        host = Recorder({"if [ -d": (0, "GATE /home/x/fn-gates/dev-abc1234\n"),
                         "certpick.py": (0, "matched=171 mismatched=0 absent=3\n")})
        gate = self.gate(host)
        gate.certificates()
        self.assertIn("certpick.py /home/x/fn-gates/dev-abc1234", host.scripts[-1])
        self.assertIn("matched=171", gate.facts["certificates"])
        self.assertTrue(any("foreign-local" in gap for gap in gate.gaps),
                        "the origin-root hazard of a copied pair must be recorded")

    def test_a_neighbouring_gate_is_used_only_for_the_books_that_match(self):
        host = Recorder({"if [ -d": (0, "NEIGHBOUR /home/x/fn-gates/dev-9999999\n"),
                         "certpick.py": (0, "matched=160 mismatched=4 absent=1\n")})
        gate = self.gate(host)
        gate.certificates()
        self.assertIn("neighbour", gate.facts["certificates"])
        self.assertTrue(any("did not hash to this revision" in gap for gap in gate.gaps),
                        "a book whose pair was left behind must be named as a gap")

    def test_no_host_gate_certifies_on_the_host(self):
        host = Recorder({"if [ -d": (0, "NOGATE\n")})
        gate = self.gate(host)
        gate.certificates()
        self.assertIn("make certify FN_CERTIFY_JOBS=16", host.scripts[-1])
        self.assertIn("make certify", gate.facts["certificates"])


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


class DryRunTests(unittest.TestCase):
    """The whole gate, end to end, against a fake host in a temporary HOME."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-deploy-gate-")
        cls.home = Path(cls.temp.name) / "home"
        acl2 = cls.home / "fn-tools/acl2-8.7"
        acl2.mkdir(parents=True)
        (acl2 / "saved_acl2").write_text(FAKE_ACL2)
        (acl2 / "saved_acl2").chmod(0o755)
        # A farm gate runs from a `git archive` tree with no repository; the
        # fake-host run needs only a revision string, so fall back to a fixed one.
        try:
            commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    check=True).stdout.decode().strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            commit = "0123456789abcdef0123456789abcdef01234567"
        cls.rev = commit[:7]
        # A host gate for exactly this revision, so the certificate branch that
        # copies pairs is the one the run takes.
        books = cls.home / "fn-gates/dev-{}/books".format(cls.rev)
        books.mkdir(parents=True)
        (books / "acceptance.cert").write_text("(:CERT fake)\n")
        (books / "acceptance.port").write_text("()\n")
        cls.evidence = Path(cls.temp.name) / "deploy-evidence.md"
        cls.code = deploy_gate.main([
            commit, "--dry-run", "--home", str(cls.home), "--repo", str(ROOT),
            "--overlay", str(ROOT / "tests/deploy_gate_fake"),
            "--nntplib-python", "none", "--evidence", str(cls.evidence), "--keep"])
        cls.text = cls.evidence.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def named(self, fragment):
        return [line for line in self.text.splitlines()
                if line.startswith("| ") and fragment in line]

    def test_the_gate_completed(self):
        self.assertIn(self.code, (0, 1), self.text[-3000:])
        self.assertNotIn("gate error", self.text)

    def test_the_three_outcomes_stay_distinct(self):
        self.assertIn("accepted=0 refused=1 uncertain=3", self.text)

    def test_every_phase_ran(self):
        for phase in ("ship archive", "install certificates", "store init",
                      "outcome accepted", "outcome refused", "outcome uncertain",
                      "drive transcript", "drive concurrent", "kill -9 mid-session",
                      "recover after the kill", "reread after recovery"):
            self.assertTrue(self.named(phase), "{} is missing from the evidence".format(phase))

    def test_the_reader_survived_the_post_and_the_reread_found_everything(self):
        store = self.home / "fn-deploy/{}/gate-run/store/store.json".format(self.rev)
        state = json.loads(store.read_text())
        ids = {article["msgid"] for article in state["articles"]}
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
        # slrn or tin may be installed on the machine running the dry run; either
        # the session ran or its absence is written out, never silence.
        self.assertTrue("no news client is installed on the host" in self.text
                        or self.named("scripted slrn session")
                        or self.named("scripted tin session"), self.text[-2000:])
        self.assertIn("not a power loss", self.text)

    def test_the_evidence_records_versions_and_commands(self):
        self.assertIn("ACL2 Version 8.7 fake", self.text)
        self.assertIn("| python3 |", self.text)
        self.assertIn("### Commands in full", self.text)


if __name__ == "__main__":
    unittest.main()
