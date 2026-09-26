"""Two sleeping agents exchange a signed report and a reply through one node.

Each agent is a separate `tools/fn_consumer.py` process with its own SQLite
database; the node is one developer image's owner.  The six ownership-boundary
cuts of specs/consumer-progress.md run in one exchange, and every uncertain
fact is settled by its owner: the consumer's database, fn's `position`, and a
re-POST of the identical signed source (D25).  The test reads outcomes from
the consumer databases (their owner) and from native `consumer status` and
`store inspect` (fn's), never from an ack standing in for either.

Opt-in: FN_RUN_CONSUMER_EXCHANGE=1 and FN_NATIVE_DEVELOPER_HOST naming a
source-matched developer image (its control stop cut is developer-only).
"""
import json
import os
from pathlib import Path
import re
import signal
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
ENABLED = os.environ.get("FN_RUN_CONSUMER_EXCHANGE") == "1"
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
CONSUMER = ROOT / "tools" / "fn_consumer.py"
VERIFIER = ROOT / "tools" / "fn_verify.py"
APP = "fn-e1"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(ENABLED and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_RUN_CONSUMER_EXCHANGE=1 and a source-matched "
                     "FN_NATIVE_DEVELOPER_HOST")
class NativeConsumerExchangeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-consumer-x-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_NATIVE_CONTROL_FAULT",
                     "FN_NATIVE_CONTROL_TEST_STOP", "FN_CONSUMER_CUT"):
            self.env.pop(name, None)
        self.log = []

    def native(self, *words, expected=0):
        result = subprocess.run([str(IMAGE), "--fn", *map(str, words)],
                                cwd=ROOT, env=self.env, capture_output=True,
                                timeout=300, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected,
                             (result.stdout + result.stderr).decode("utf-8", "replace"))
        return result

    def start_owner(self, *, stop_after_submit=False):
        env = dict(self.env)
        if stop_after_submit:
            env["FN_NATIVE_CONTROL_TEST_STOP"] = "after-submit"
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(proc, b"LISTENING ", timeout=120)
        return proc

    @staticmethod
    def reap(proc):
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=10)
        for stream in (proc.stdout, proc.stderr):
            if stream and not stream.closed:
                stream.close()

    def stop_owner(self, proc):
        diagnostics = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostics)

    def signer(self, label, principal_byte, generation):
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric import ed25519
        key = ed25519.Ed25519PrivateKey.generate()
        seed = key.private_bytes(serialization.Encoding.Raw,
                                 serialization.PrivateFormat.Raw,
                                 serialization.NoEncryption())
        public = key.public_key().public_bytes(serialization.Encoding.Raw,
                                               serialization.PublicFormat.Raw)
        base = self.root / label
        base.mkdir()
        keys = {name: str(base / name) for name in
                ("principal", "ed_public", "ed_secret", "ml_private", "ml_public")}
        Path(keys["principal"]).write_bytes(bytes([principal_byte]) * 32)
        Path(keys["ed_public"]).write_bytes(public)
        Path(keys["ed_secret"]).write_bytes(seed + public)
        for args in (["genpkey", "-algorithm", "ML-DSA-65", "-out", keys["ml_private"]],
                     ["pkey", "-in", keys["ml_private"], "-pubout", "-out",
                      keys["ml_public"]]):
            made = subprocess.run([OPENSSL, *args], capture_output=True, timeout=60)
            self.assertEqual(made.returncode, 0, made.stderr)
        self.native("hybrid-enroll", self.control, generation, keys["principal"],
                    keys["ed_public"], keys["ml_public"])
        return keys, (bytes([principal_byte]) * 32).hex()

    def agent(self, label, principal_byte, generation):
        keys, principal_hex = self.signer(label, principal_byte, generation)
        self.principals = getattr(self, "principals", {})
        self.principals[label] = (keys, principal_hex, generation)
        config = self.root / label / "consumer.json"
        config.write_text(json.dumps({
            "image": str(IMAGE), "control": str(self.control),
            "consumer": label, "group": "fn.test", "application_id": APP,
            "from": "%s@example.invalid" % label, "db": str(self.root / label / "state.db"),
            "work": str(self.root / label / "work"), "keys": keys,
            "principal_hex": principal_hex, "generation": str(generation),
            "keyring": str(self.root / label / "trusted.json"), "claims": []}),
            encoding="utf-8")
        return config

    def trust(self, config, labels, claims):
        """The consumer's own trust context: a keyring of the authors it was
        given (made from their public key files, never read from the node) and
        the application's rule for who may claim which operation identity."""
        entries = []
        for label in labels:
            keys, _, generation = self.principals[label]
            made = subprocess.run(
                [sys.executable, str(VERIFIER), "keyring-entry", keys["principal"],
                 keys["ed_public"], keys["ml_public"], "--generation", str(generation)],
                capture_output=True, timeout=60, check=False)
            self.assertEqual(made.returncode, 0, made.stderr)
            entries.append(json.loads(made.stdout))
        data = json.loads(config.read_text(encoding="utf-8"))
        Path(data["keyring"]).write_text(json.dumps(
            {"format": "fn-verify-keyring-v1", "principals": entries}), encoding="utf-8")
        data["claims"] = [[APP, prefix, self.principals[label][1]]
                          for prefix, label in claims]
        config.write_text(json.dumps(data), encoding="utf-8")

    def register(self, label):
        self.native("consumer", "register", self.control, label, "fn.test",
                    self.root / label / "registered.fncu")

    def consumer(self, config, *words, cut=None, expected=0, background=False):
        env = dict(self.env)
        if cut:
            env["FN_CONSUMER_CUT"] = cut
        argv = [sys.executable, str(CONSUMER), str(config), *words]
        if background:
            proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
            self.addCleanup(self.reap, proc)
            return proc
        result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True,
                                timeout=900, check=False)
        self.log.append((config.parent.name, words, cut, result.returncode,
                         result.stderr.decode("utf-8", "replace")[-2000:]))
        if expected is not None:
            self.assertEqual(result.returncode, expected,
                             (result.stdout + result.stderr).decode("utf-8", "replace"))
        if cut:
            self.assertIn(("CONSUMER-CUT " + cut).encode(), result.stderr)
        return result

    def summary(self, config):
        result = self.consumer(config, "summary")
        return json.loads(result.stdout)

    def status(self, label):
        out = self.native("consumer", "status", self.control, label).stdout
        match = re.search(rb"committed-ack=(\d+) committed-journal-frontier=(\d+)", out)
        self.assertIsNotNone(match, out)
        return int(match.group(1)), int(match.group(2))

    def cut_at_owner(self, config, *words):
        """Run the consumer against an owner that stops after completing the
        consumer's first control request, then dies before replying."""
        self.stop_owner(self.owner)
        cut_owner = self.start_owner(stop_after_submit=True)
        proc = self.consumer(config, *words, background=True)
        wait_for_announcement(cut_owner, b"CONTROL-SUBMITTED", timeout=300)
        cut_owner.kill()
        cut_owner.wait(timeout=10)
        stdout, stderr = proc.communicate(timeout=300)
        self.log.append((config.parent.name, words, "owner-after-submit",
                         proc.returncode, stderr.decode("utf-8", "replace")[-2000:]))
        self.assertEqual(proc.returncode, 3, (stdout + stderr).decode("utf-8", "replace"))
        self.owner = self.start_owner()
        return json.loads(stdout)

    def test_two_sleeping_agents_exchange_across_every_ownership_cut(self):
        base = self.root / "node"
        base.mkdir()
        self.store, self.control = base / "store", base / "control.sock"
        self.config = base / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                self.store, free_port(), self.control, base / "service.log"),
            encoding="ascii")
        self.native("store", self.store, "init", "fn.test")
        self.owner = self.start_owner()
        self.native("consumer", "bootstrap", self.control)
        a = self.agent("agent-a", 0xA1, 1)
        b = self.agent("agent-b", 0xB2, 2)
        m = self.agent("agent-m", 0xC3, 3)  # a third author reusing A's operation id
        for label in ("agent-a", "agent-b"):
            self.register(label)
        # Both consumers trust A, B and M as authors; the application gives
        # report ids to A and reply ids to B, so M is trusted but entitled
        # to neither.
        for config in (a, b):
            self.trust(config, ("agent-a", "agent-b", "agent-m"),
                       (("r", "agent-a"), ("reply-", "agent-b")))

        # A authors report R and goes to sleep.
        self.consumer(a, "report", "r1", "dregg-receipt-0001")
        self.assertEqual(self.summary(a)["outbox"][0]["state"], "stored",
                         self.summary(a)["outbox"])

        # Cut 1: B dies inside its transaction.  B's database, the owner of
        # that fact, holds nothing; fn's position did not move.
        self.consumer(b, "wake", cut="in-transaction", expected=97)
        s = self.summary(b)
        self.assertEqual((s["operations"], s["outbox"], s["transitions"],
                          s["pending_ack"]), ([], [], [], None))
        self.assertEqual(self.status("agent-b")[0], 0)

        # Cut 2: B commits (inbox + decision + transition + outbox + cursor to
        # declare) and dies before acking.  fn still records position 0.
        self.consumer(b, "wake", cut="after-commit", expected=97)
        s = self.summary(b)
        self.assertEqual(s["transitions"], [[APP, "r1"]])
        self.assertEqual([o["state"] for o in s["outbox"]], ["pending"])
        self.assertEqual(s["pending_ack"], "unsent")
        self.assertEqual(self.status("agent-b")[0], 0)

        # Cut 3: the ack is durable at the owner but its reply is lost.
        s = self.cut_at_owner(b, "wake")
        self.assertEqual(s["pending_ack"], "uncertain")
        acked = self.status("agent-b")[0]
        self.assertGreater(acked, 0)  # fn's owner says the declaration committed

        # Cut 4: durable ack before the reply POST.  B settles the uncertain
        # ack by position (no second ack), then dies before posting Q.
        self.consumer(b, "wake", cut="before-post", expected=97)
        s = self.summary(b)
        self.assertIsNone(s["pending_ack"])
        self.assertEqual([o["state"] for o in s["outbox"]], ["pending"])
        self.assertEqual(self.status("agent-b")[0], acked)

        # Cut 5: the reply POST completes at the owner but its answer is lost.
        s = self.cut_at_owner(b, "wake")
        self.assertEqual([o["state"] for o in s["outbox"]], ["uncertain"])
        q_sha = s["outbox"][0]["sha256"]

        # B re-POSTs the identical signed source.  D25 answers duplicate
        # (exit 0; PKT-166).  Were the answer lost again, B would settle by fn
        # serving the exact source back to its own poll.  Either way the
        # owner of the fact is fn's Store, not an ack.
        self.consumer(b, "wake")
        s = self.summary(b)
        self.assertEqual([(o["state"], o["attempts"], o["sha256"]) for o in s["outbox"]],
                         [("stored", 2, q_sha)])
        self.assertIn((s["outbox"][0]["last_exit"], s["outbox"][0]["settled_by"]),
                      ((0, "post-answer"), (1, "store-observation")))
        self.settlement = s["outbox"][0]["settled_by"]
        self.assertEqual(s["transitions"], [[APP, "r1"]])

        # Cut 6: Q was delivered while A slept.  A's position never moved.
        self.assertEqual(self.status("agent-a")[0], 0)
        self.consumer(a, "wake", cut="after-ack", expected=97)
        self.consumer(a, "wake")
        s = self.summary(a)
        self.assertEqual(s["transitions"], [[APP, "reply-r1"]])
        self.assertEqual(s["state"].get("replies"), "1")
        self.assertEqual([(o["operation_id"], o["result"]) for o in s["operations"]
                          if o["operation_id"] == "r1"], [("r1", "replied")])
        self.assertEqual([i["disposition"] for i in s["inbox"]], ["repeat", "applied"])

        # Same operation, changed source: M reuses r1.  Both consumers keep the
        # conflict evidence and neither performs a transition or a reply.
        self.consumer(m, "report", "r1", "a different receipt")
        for config, transitions in ((b, [[APP, "r1"]]), (a, [[APP, "reply-r1"]])):
            self.consumer(config, "wake")
            s = self.summary(config)
            self.assertEqual(s["transitions"], transitions)
            self.assertEqual(s["inbox"][-1]["disposition"], "conflict")
            self.assertEqual(s["inbox"][-1]["reason"], "unentitled")
            self.assertEqual(s["inbox"][-1]["own_verdict"], "verified")
            self.assertEqual(s["inbox"][-1]["operation_id"], "r1")
        self.assertEqual(len(self.summary(b)["outbox"]), 1)

        # Two consumers, two positions; each reached the frontier it polled.
        a_ack, b_ack = self.status("agent-a")[0], self.status("agent-b")[0]
        self.assertNotEqual(a_ack, b_ack)
        self.stop_owner(self.owner)
        q_id = self.summary(b)["outbox"][0]["message_id"]
        inspected = self.native("store", self.store, "inspect", q_id)
        self.assertIn(b"kind: reply", inspected.stdout)
        out = os.environ.get("FN_CONSUMER_EXCHANGE_EVIDENCE")
        if out:
            Path(out).write_text(json.dumps({
                "a": self.summary(a), "b": self.summary(b), "log": self.log,
                "positions": {"agent-a": a_ack, "agent-b": b_ack},
                "q_settlement": self.settlement},
                indent=1, sort_keys=True), encoding="utf-8")

    def node(self, *, log=True):
        """A fresh store and developer owner with a control socket."""
        base = self.root / "node"
        base.mkdir()
        self.store, self.control = base / "store", base / "control.sock"
        self.config = base / "fn.toml"
        text = ('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
                'port = {}\n[control]\npath = "{}"\n').format(
                    self.store, free_port(), self.control)
        if log:
            text += '[log]\npath = "{}"\n'.format(base / "service.log")
        self.config.write_text(text, encoding="ascii")
        self.native("store", self.store, "init", "fn.test")
        self.owner = self.start_owner()
        self.native("consumer", "bootstrap", self.control)

    def stored_message(self, message_id):
        """fn's Store, read with the owner stopped, then the owner restarted."""
        self.stop_owner(self.owner)
        inspected = self.native("store", self.store, "inspect", message_id,
                                expected=None)
        self.owner = self.start_owner()
        return inspected

    def lone_author(self):
        """A node and one registered author A who trusts itself and owns the
        report ids."""
        self.node()
        a = self.agent("agent-a", 0xA1, 1)
        self.register("agent-a")
        self.trust(a, ("agent-a",), (("r", "agent-a"),))
        return a

    def revoke(self, label):
        self.native("hybrid-revoke-next", self.control,
                    self.principals[label][0]["principal"])

    def assert_reconciled_by_observation(self, a, after_death):
        """The trace the review names, after the revocation and a restart."""
        woke = self.consumer(a, "wake", expected=None)
        final = self.summary(a)["outbox"]
        self.log.append(("trace", after_death, woke.returncode, final))
        self.assertNotIn("refused", [o["state"] for o in final],
                         "an accepted operation recorded refused: after death %r; "
                         "after revocation and restart %r" % (after_death, final))
        self.assertEqual(woke.returncode, 0, woke.stderr)
        self.assertEqual([(o["state"], o["settled_by"]) for o in final],
                         [("stored", "store-observation")], final)
        # The first attempt never got a durable answer; the reconciliation
        # resend of the saved artifact was refused (A is revoked) and settles
        # only itself; there is no third, blind attempt.
        self.assertEqual([(j["purpose"], j["state"], j["exit"]) for j in final[0]["journal"]],
                         [("submit", "unanswered", None), ("reconcile", "answered", 1)],
                         final)
        self.assertEqual(final[0]["sha256"], after_death[0]["sha256"])
        return final

    def test_death_after_acceptance_then_revocation_is_never_refused(self):
        """gpt-6's review, section 2: the node accepts R, the consumer dies
        after the answer arrives and before its result transaction, A's
        enrolment is revoked, and the restarted consumer's resend is refused.
        The refusal settles that resend only: R stays uncertain until fn's
        Store serves the exact artifact back, and is then stored."""
        a = self.lone_author()
        self.consumer(a, "report", "r1", "dregg-receipt-0001", cut="after-post",
                      expected=97)
        after_death = self.summary(a)["outbox"]
        self.assertEqual([(o["state"], o["attempts"]) for o in after_death],
                         [("uncertain", 1)], after_death)
        inspected = self.stored_message(after_death[0]["message_id"])
        self.assertEqual(inspected.returncode, 0,
                         (inspected.stdout + inspected.stderr).decode())
        self.assertIn(b"kind: report-receipt", inspected.stdout)
        self.revoke("agent-a")
        self.assert_reconciled_by_observation(a, after_death)
        self.stop_owner(self.owner)
        self.write_evidence("death-after-acceptance", {"a": self.summary(a)})

    def test_consumer_killed_after_the_owner_commits_then_revocation(self):
        """The review's cut exactly: the owner commits R and stops before it
        replies; the CONSUMER is killed then (not the owner), A is revoked,
        and the consumer restarts."""
        a = self.lone_author()
        self.stop_owner(self.owner)
        cut_owner = self.start_owner(stop_after_submit=True)
        env = dict(self.env)
        proc = subprocess.Popen([sys.executable, str(CONSUMER), str(a), "report", "r1",
                                 "dregg-receipt-0001"], cwd=ROOT, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                start_new_session=True)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(cut_owner, b"CONTROL-SUBMITTED", timeout=120)
        os.killpg(proc.pid, signal.SIGKILL)  # the group this test started
        proc.wait(timeout=30)
        self.assertEqual(proc.returncode, -signal.SIGKILL)
        cut_owner.kill()
        cut_owner.wait(timeout=10)
        self.owner = self.start_owner()
        after_death = self.summary(a)["outbox"]
        self.assertEqual([(o["state"], o["attempts"]) for o in after_death],
                         [("uncertain", 1)], after_death)
        self.revoke("agent-a")
        self.assert_reconciled_by_observation(a, after_death)
        self.stop_owner(self.owner)
        self.write_evidence("consumer-killed-after-commit", {"a": self.summary(a)})

    def test_death_while_recording_and_before_sending_are_reconciled(self):
        """Uncertainty during the answer's recording (death inside its BEGIN
        IMMEDIATE, rolled back) and death after the in-flight record but
        before anything was sent.  Both are potentially successful; each is
        reconciled by one resend of the saved artifact: the first is D25's
        duplicate, the second a first acceptance."""
        a = self.lone_author()
        journals = []
        for op, cut, status in (("r1", "in-result-transaction", "DUPLICATE"),
                                ("r2", "attempt-recorded", "ACCEPTED")):
            self.consumer(a, "report", op, "payload " + op, cut=cut, expected=97)
            after_death = self.summary(a)["outbox"][-1]
            self.assertEqual((after_death["state"], after_death["attempts"],
                              after_death["last_exit"]), ("uncertain", 1, None), after_death)
            self.consumer(a, "wake")
            final = self.summary(a)["outbox"][-1]
            self.log.append(("trace", cut, after_death, final))
            self.assertEqual((final["state"], final["settled_by"], final["sha256"]),
                             ("stored", "post-answer", after_death["sha256"]), final)
            self.assertEqual([(j["purpose"], j["state"], j["exit"], j["status"])
                              for j in final["journal"]],
                             [("submit", "unanswered", None, None),
                              ("reconcile", "answered", 0, status)], (cut, final))
            journals.append(final)
        self.stop_owner(self.owner)
        self.write_evidence("death-while-recording", {"a": self.summary(a)})

    def test_a_report_from_an_author_the_consumer_does_not_trust_is_not_consumed(self):
        """fn enrolled U and accepted U's signed report; B was never given U's
        keys, so B's own check cannot decide it.  B keeps the evidence beside
        fn's verdict and performs no operation, transition or reply."""
        self.node()
        a = self.agent("agent-a", 0xA1, 1)
        b = self.agent("agent-b", 0xB2, 2)
        u = self.agent("agent-u", 0xD4, 3)
        self.register("agent-b")
        claims = (("r", "agent-a"), ("u", "agent-u"), ("reply-", "agent-b"))
        self.trust(b, ("agent-a", "agent-b"), claims)
        self.trust(u, ("agent-u",), claims)
        self.trust(a, ("agent-a",), claims)
        self.consumer(u, "report", "u1", "from an untrusted author")
        self.consumer(a, "report", "r1", "from a trusted author")
        self.consumer(b, "wake")
        s = self.summary(b)
        by_op = {i["operation_id"]: i for i in s["inbox"]}
        u_row, a_row = by_op["u1"], by_op["r1"]
        self.assertEqual((u_row["disposition"], u_row["reason"], u_row["own_verdict"],
                          u_row["own_principal"]),
                         ("not-consumed", "undecided", "undecided", None), u_row)
        # fn's verdict, recorded beside B's own: fn verified U (it enrolled U).
        self.assertEqual(u_row["node_principal"], self.principals["agent-u"][1], u_row)
        self.assertTrue(u_row["node_verdict"], u_row)
        self.assertEqual((a_row["disposition"], a_row["own_verdict"], a_row["own_principal"]),
                         ("applied", "verified", self.principals["agent-a"][1]), a_row)
        self.assertEqual(s["transitions"], [[APP, "r1"]])
        self.assertNotIn("u1", [o["operation_id"] for o in s["operations"]])
        self.assertEqual([o["message_id"] for o in s["outbox"]],
                         ["<fn-e1.reply-r1@agent-b.invalid>"])
        self.assertGreater(self.status("agent-b")[0], 0)  # progressed past both
        self.stop_owner(self.owner)
        self.write_evidence("untrusted-author", {"b": s})

    def test_a_conflicting_claim_arrives_before_and_after_the_legitimate_one(self):
        """The application, not the signature, says who may claim an
        operation identity.  M (trusted, correctly signed) claims r1 BEFORE A
        does and r2 AFTER A does; in both orders A's operation is the one
        applied and M's is kept as conflict evidence with no transition."""
        self.node()
        a = self.agent("agent-a", 0xA1, 1)
        b = self.agent("agent-b", 0xB2, 2)
        m = self.agent("agent-m", 0xC3, 3)
        self.register("agent-b")
        claims = (("r", "agent-a"), ("reply-", "agent-b"))
        for config in (a, b, m):
            self.trust(config, ("agent-a", "agent-b", "agent-m"), claims)
        self.consumer(m, "report", "r1", "M first")
        self.consumer(a, "report", "r1", "A second")
        self.consumer(a, "report", "r2", "A first")
        self.consumer(m, "report", "r2", "M second")
        self.consumer(b, "wake")
        s = self.summary(b)
        rows = [(i["operation_id"], i["message_id"].split("@")[1], i["disposition"],
                 i["reason"], i["own_verdict"]) for i in s["inbox"]]
        self.assertEqual(rows, [
            ("r1", "agent-m.invalid>", "conflict", "unentitled", "verified"),
            ("r1", "agent-a.invalid>", "applied", None, "verified"),
            ("r2", "agent-a.invalid>", "applied", None, "verified"),
            ("r2", "agent-m.invalid>", "conflict", "unentitled", "verified")], s["inbox"])
        self.assertEqual(s["transitions"], [[APP, "r1"], [APP, "r2"]])
        self.assertEqual([(o["operation_id"], o["claimant"]) for o in s["operations"]
                          if o["kind"] == "report-receipt"],
                         [("r1", self.principals["agent-a"][1]),
                          ("r2", self.principals["agent-a"][1])])
        self.assertEqual(len(s["outbox"]), 2)
        self.stop_owner(self.owner)
        self.write_evidence("conflict-both-orders", {"b": s})

    def write_evidence(self, label, payload):
        out = os.environ.get("FN_CONSUMER_EXCHANGE_EVIDENCE")
        if out:
            path = Path(out).with_suffix("." + label + ".json")
            payload = dict(payload, log=self.log)
            path.write_text(json.dumps(payload, indent=1, sort_keys=True, default=str),
                            encoding="utf-8")

    def test_identical_signed_resend_answers_duplicate(self):
        """D25 on the local control route: a byte-identical resend of an
        accepted signed article is "already stored here" (exit 0), which is
        what lets a consumer settle an uncertain POST by re-POSTing."""
        base = self.root / "node"
        base.mkdir()
        self.store, self.control = base / "store", base / "control.sock"
        self.config = base / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                self.store, free_port(), self.control), encoding="ascii")
        self.native("store", self.store, "init", "fn.test")
        self.owner = self.start_owner()
        a = self.agent("agent-a", 0xA1, 1)
        self.consumer(a, "report", "r1", "dregg-receipt-0001")
        cfg = json.loads(a.read_text(encoding="utf-8"))
        db = __import__("sqlite3").connect(cfg["db"])
        source, ed_sig, ml_sig = db.execute(
            "SELECT source, ed_sig, ml_sig FROM submissions").fetchone()
        db.close()
        paths = [self.root / name for name in ("again.eml", "again.ed", "again.ml")]
        for path, octets in zip(paths, (source, ed_sig, ml_sig)):
            path.write_bytes(octets)
        again = subprocess.run(
            [str(IMAGE), "--fn", "hybrid-author", str(self.control), "1",
             *map(str, paths), cfg["keys"]["ml_public"]],
            cwd=ROOT, env=self.env, capture_output=True, timeout=300, check=False)
        self.stop_owner(self.owner)
        self.assertEqual(again.returncode, 0,
                         "identical resend answered %d, not D25 duplicate"
                         % again.returncode)

    def test_identical_operator_post_resend_answers_duplicate(self):
        """D25 on the operator post route (unsigned, same control socket)."""
        base = self.root / "node"
        base.mkdir()
        self.store, self.control = base / "store", base / "control.sock"
        self.config = base / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                self.store, free_port(), self.control), encoding="ascii")
        self.native("store", self.store, "init", "fn.test")
        self.owner = self.start_owner()
        msgid = "<operator-resend@example.invalid>"
        article = self.root / "plain.eml"
        article.write_bytes(b"From: author@example.invalid\r\n"
                            b"Date: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
                            b"Newsgroups: fn.test\r\nSubject: resend\r\n"
                            b"Message-ID: " + msgid.encode() + b"\r\n\r\nexact\r\n")
        words = ("operator", self.config, "post", "--message-id", msgid,
                 "--payload", article, "--group", "fn.test")
        self.native(*words)
        again = subprocess.run([str(IMAGE), "--fn", *map(str, words)], cwd=ROOT,
                               env=self.env, capture_output=True, timeout=300,
                               check=False)
        self.stop_owner(self.owner)
        self.assertEqual(again.returncode, 0,
                         "identical operator post resend answered %d: %s"
                         % (again.returncode, (again.stdout + again.stderr).decode()))


if __name__ == "__main__":
    unittest.main()
