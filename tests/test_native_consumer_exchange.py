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
        config = self.root / label / "consumer.json"
        config.write_text(json.dumps({
            "image": str(IMAGE), "control": str(self.control),
            "consumer": label, "group": "fn.test", "application_id": APP,
            "from": "%s@example.invalid" % label, "db": str(self.root / label / "state.db"),
            "work": str(self.root / label / "work"), "keys": keys,
            "principal_hex": principal_hex, "generation": str(generation)}),
            encoding="utf-8")
        return config

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
            "SELECT source, ed_sig, ml_sig FROM outbox").fetchone()
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
