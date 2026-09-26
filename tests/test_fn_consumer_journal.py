"""tools/fn_consumer.py's attempt journal, against a stand-in native image.

The stand-in answers `hybrid-sign` (fresh random signatures on every call, as
randomized ML-DSA signing does) and `hybrid-author` (the exit codes a test
queues), and records the exact bytes and key file each `hybrid-author` was
given.  What is checked is the consumer's own contract (CNS-003): the attempt
is durable before the native boundary is crossed; a later refusal never
settles an earlier attempt without a durable answer; retries send the saved
artifact and its saved key context, never a re-signed one.  fn's side is
tests/test_native_consumer_exchange.py on a real image.
"""
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import fn_consumer  # noqa: E402

FAKE = r'''#!/usr/bin/env python3
import hashlib, json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
words = sys.argv[2:]
if words[0] == "hybrid-sign":
    print("ed25519 " + os.urandom(64).hex())
    print("ml-dsa-65 " + os.urandom(3309).hex())
    sys.exit(0)
if words[0] == "hybrid-author":
    control, generation, q, ed, ml, mlpub = words[1:7]
    log = json.loads(state.read_text()) if state.exists() else {"queue": [], "seen": []}
    log["seen"].append({"generation": generation,
                        "q": hashlib.sha256(Path(q).read_bytes()).hexdigest(),
                        "ed": Path(ed).read_bytes().hex(),
                        "ml": hashlib.sha256(Path(ml).read_bytes()).hexdigest(),
                        "mlpub": Path(mlpub).read_text()})
    code = log["queue"].pop(0) if log["queue"] else 0
    state.write_text(json.dumps(log))
    word = {0: "accepted hybrid-author ACCEPTED", 1: "refused hybrid-author REFUSED",
            3: "uncertain hybrid-author UNCERTAIN"}.get(code, "fault hybrid-author FAULT")
    sys.stderr.write(word + "\n")
    sys.exit(code)
sys.exit(64)
'''


class JournalRules(unittest.TestCase):
    """The two pure rules, with a witness per clause."""

    def test_state_is_refused_only_when_every_attempt_was_refused(self):
        state = fn_consumer.submission_state
        self.assertEqual(state([], False), "pending")
        self.assertEqual(state([("answered", 1)], False), "refused")
        self.assertEqual(state([("answered", 1), ("answered", 1)], False), "refused")
        # The review's trace: an attempt without a durable answer, then a
        # refused retry.  Never refused.
        self.assertEqual(state([("unanswered", None), ("answered", 1)], False), "uncertain")
        self.assertEqual(state([("answered", 3), ("answered", 1)], False), "uncertain")
        self.assertEqual(state([("in-flight", None)], False), "uncertain")
        self.assertEqual(state([("answered", 4)], False), "uncertain")
        # An observation is the only thing that settles stored.
        self.assertEqual(state([("unanswered", None), ("answered", 1)], True), "stored")

    def test_one_reconciliation_per_open_attempt(self):
        due = fn_consumer.reconcile_due
        self.assertTrue(due([("unanswered", None)]))
        self.assertTrue(due([("answered", 3)]))
        self.assertFalse(due([("unanswered", None), ("answered", 1)]))
        self.assertTrue(due([("unanswered", None), ("answered", 1), ("answered", 3)]))
        self.assertFalse(due([("answered", 1)]))
        self.assertFalse(due([]))


class JournalAgainstAStandIn(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-consumer-journal-")
        self.addCleanup(temporary.cleanup)
        root = self.root = Path(temporary.name)
        image = root / "fake-image"
        image.write_text(FAKE)
        image.chmod(0o755)
        self.state = root / "fake.json"
        keys = {name: str(root / name) for name in
                ("principal", "ed_public", "ed_secret", "ml_private", "ml_public")}
        Path(keys["principal"]).write_bytes(b"\xa1" * 32)
        Path(keys["ed_public"]).write_bytes(b"\x01" * 32)
        Path(keys["ml_public"]).write_text("ORIGINAL ML PUBLIC KEY\n")
        self.keys = keys
        self.config = root / "consumer.json"
        self.config.write_text(json.dumps({
            "image": str(image), "control": str(root / "control.sock"),
            "consumer": "agent-a", "group": "fn.test", "application_id": "fn-e1",
            "from": "a@example.invalid", "db": str(root / "state.db"),
            "work": str(root / "work"), "keys": keys, "principal_hex": "a1" * 32,
            "generation": "1", "keyring": str(root / "k.json"), "claims": []}))

    def queue(self, *codes):
        log = json.loads(self.state.read_text()) if self.state.exists() else {"seen": []}
        log["queue"] = list(codes)
        self.state.write_text(json.dumps(log))

    def run_consumer(self, *words, cut=None):
        env = dict(os.environ, FAKE_STATE=str(self.state))
        env.pop("FN_CONSUMER_CUT", None)
        if cut:
            env["FN_CONSUMER_CUT"] = cut
        result = subprocess.run([sys.executable, str(ROOT / "tools" / "fn_consumer.py"),
                                 str(self.config), *words], env=env,
                                capture_output=True, timeout=120, check=False)
        return result

    def outbox(self):
        return json.loads(self.run_consumer("summary").stdout)["outbox"]

    def seen(self):
        return json.loads(self.state.read_text())["seen"]

    def test_the_attempt_is_durable_before_the_native_call(self):
        # Died with the in-flight record committed and nothing sent: the
        # next process finds it unanswered, i.e. potentially successful.
        result = self.run_consumer("report", "r1", "x", cut="attempt-recorded")
        self.assertEqual(result.returncode, 97, result.stderr)
        self.assertFalse(self.state.exists())       # nothing crossed the boundary
        [entry] = self.outbox()
        self.assertEqual((entry["state"], entry["journal"]),
                         ("uncertain", [{"purpose": "submit", "state": "unanswered",
                                         "exit": None, "status": None}]))

    def test_a_refused_retry_never_settles_an_unanswered_attempt(self):
        # The review's trace against the stand-in: accepted, the answer lost
        # with the process, then the retry refused.
        self.queue(0, 1)
        self.assertEqual(self.run_consumer("report", "r1", "x", cut="after-post").returncode, 97)
        self.assertEqual(self.run_consumer("report", "r1", "x").returncode, 0)
        [entry] = self.outbox()
        self.assertEqual(entry["state"], "uncertain")
        self.assertEqual([(j["purpose"], j["state"], j["exit"]) for j in entry["journal"]],
                         [("submit", "unanswered", None), ("reconcile", "answered", 1)])
        # No blind third attempt while nothing new is known.
        self.assertEqual(self.run_consumer("report", "r1", "x").returncode, 0)
        self.assertEqual(len(self.seen()), 2)
        # Teeth: without the unanswered attempt, the same refusal is terminal.
        self.queue(1)
        self.assertEqual(self.run_consumer("report", "r9", "y").returncode, 0)
        self.assertEqual([o["state"] for o in self.outbox()], ["uncertain", "refused"])

    def test_death_inside_the_answer_transaction_rolls_back_to_unanswered(self):
        self.queue(0, 0)
        self.assertEqual(self.run_consumer("report", "r1", "x",
                                           cut="in-result-transaction").returncode, 97)
        [entry] = self.outbox()
        self.assertEqual((entry["state"], entry["settled_by"]), ("uncertain", None))
        self.assertEqual(self.run_consumer("report", "r1", "x").returncode, 0)
        [entry] = self.outbox()
        self.assertEqual((entry["state"], entry["settled_by"], entry["attempts"]),
                         ("stored", "post-answer", 2))

    def test_retries_send_the_saved_artifact_and_key_context(self):
        self.queue(3, 0)
        self.assertEqual(self.run_consumer("report", "r1", "x").returncode, 3)
        # The configuration changes under the consumer: a new ML-DSA key file
        # and a new generation.  Neither reaches the saved artifact.
        Path(self.keys["ml_public"]).write_text("ROTATED ML PUBLIC KEY\n")
        data = json.loads(self.config.read_text())
        data["generation"] = "7"
        self.config.write_text(json.dumps(data))
        # A second report of the same operation signs afresh (randomized) and
        # the fresh signatures are discarded: the operation keeps its artifact.
        self.assertEqual(self.run_consumer("report", "r1", "x").returncode, 0)
        first, second = self.seen()
        self.assertEqual(first, second)
        self.assertEqual((second["generation"], second["mlpub"]),
                         ("1", "ORIGINAL ML PUBLIC KEY\n"))
        [entry] = self.outbox()
        self.assertEqual((entry["state"], entry["attempts"]), ("stored", 2))

    def test_the_artifact_is_immutable(self):
        self.queue(0)
        self.run_consumer("report", "r1", "x")
        db = sqlite3.connect(str(self.root / "state.db"))
        self.addCleanup(db.close)
        for statement in ("UPDATE submissions SET ml_sig = x'00'",
                          "DELETE FROM submissions"):
            with self.assertRaises(sqlite3.DatabaseError):
                db.execute(statement)


if __name__ == "__main__":
    unittest.main()
