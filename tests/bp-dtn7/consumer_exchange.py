"""Application half of the BP mission: real fn_consumer processes and records.

The mission owns transport. This adapter owns only test configuration,
process cuts and observations of the external application's database; it
never computes fn cursors, signatures, identities or admission decisions.
"""
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys


class ConsumerExchangeFailure(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise ConsumerExchangeFailure(message)


def digest(octets):
    return hashlib.sha256(octets).hexdigest()


class MissionConsumerExchange:
    application = "fn-e1"

    def __init__(self, mission, root, authors):
        self.mission, self.root = mission, Path(root)
        self.configs = {}
        self.observations = {}
        entries = []
        for label in ("author-a", "author-b"):
            keys = authors[label]
            result = subprocess.run(
                [sys.executable, str(self.root / "tools/fn_verify.py"), "keyring-entry",
                 str(keys / "principal"), str(keys / "ed25519.public"),
                 str(keys / "ml-dsa-65.public.pem"), "--generation",
                 "1" if label == "author-a" else "2"],
                capture_output=True, env=mission.lab.env, timeout=120)
            require(result.returncode == 0, "independent keyring creation failed: " +
                    result.stderr.decode(errors="replace"))
            entries.append(json.loads(result.stdout))
        principals = {label: (keys / "principal").read_bytes().hex()
                      for label, keys in authors.items()}
        for node, label, generation in (("a", "author-a", "1"), ("b", "author-b", "2")):
            directory = mission.lab.path("consumer-" + node)
            directory.mkdir()
            keys = authors[label]
            keyring = directory / "trusted.json"
            keyring.write_text(json.dumps({"format": "fn-verify-keyring-v1",
                                           "principals": entries}))
            config = directory / "consumer.json"
            config.write_text(json.dumps({
                "image": str(mission.owner_image),
                "control": str(mission.nodes[node]["control"]),
                "consumer": node + "-reader", "group": "fn.test",
                "application_id": self.application,
                "from": label + "@example.invalid",
                "db": str(directory / "state.db"), "work": str(directory / "work"),
                "keys": {"principal": str(keys / "principal"),
                         "ed_public": str(keys / "ed25519.public"),
                         "ed_secret": str(keys / "ed25519.secret"),
                         "ml_public": str(keys / "ml-dsa-65.public.pem"),
                         "ml_private": str(keys / "ml-dsa-65.private.pem")},
                "principal_hex": principals[label], "generation": generation,
                "keyring": str(keyring),
                "claims": [[self.application, "r", principals["author-a"]],
                           [self.application, "reply-", principals["author-b"]]]}))
            self.configs[node] = config

    def invoke(self, node, tag, *words, cut=None):
        env = dict(self.mission.lab.env)
        env.pop("FN_CONSUMER_CUT", None)
        env.pop("FN_CONSUMER_CUT_ACTION", None)
        if cut:
            env["FN_CONSUMER_CUT"] = cut
        argv = [sys.executable, str(self.root / "tools/fn_consumer.py"),
                str(self.configs[node]), *words]
        result = subprocess.run(argv, capture_output=True, env=env,
                                cwd=self.root, timeout=900)
        log = self.mission.lab.path(tag + ".log")
        log.write_bytes(result.stdout + result.stderr + b"\n# rc=%d\n" % result.returncode)
        self.mission.lab.logs[tag] = log
        require(result.returncode == (97 if cut else 0),
                "%s: consumer exit %s: %s" %
                (tag, result.returncode, result.stderr.decode(errors="replace")[-600:]))
        if cut:
            require(("CONSUMER-CUT " + cut).encode() in result.stderr,
                    tag + ": cut marker missing")
            return None
        return json.loads(result.stdout)

    def summary(self, node, tag):
        return self.invoke(node, tag, "summary")

    def database(self, node):
        config = json.loads(self.configs[node].read_text())
        return sqlite3.connect("file:" + config["db"] + "?mode=ro", uri=True)

    def submission(self, node, operation):
        with closing(self.database(node)) as database:
            row = database.execute(
                "SELECT message_id, source, ed_sig, ml_sig FROM submissions "
                "WHERE application_id=? AND operation_id=?",
                (self.application, operation)).fetchone()
        require(row is not None, node + ": immutable artifact missing for " + operation)
        message_id, source, ed, ml = row
        return {"operation": [self.application, operation], "message_id": message_id,
                "source_sha256": digest(source), "ed25519_sha256": digest(ed),
                "ml_dsa_65_sha256": digest(ml)}, source

    def received(self, node, operation):
        config = json.loads(self.configs[node].read_text())
        with closing(self.database(node)) as database:
            rows = database.execute(
                "SELECT history, incarnation, source_id, message_id, source, received, "
                "own_verdict, node_verdict, store_sequence, disposition FROM inbox "
                "WHERE application_id=? AND operation_id=? ORDER BY store_sequence",
                (self.application, operation)).fetchall()
        require(len(rows) == 1, "%s: expected one inbox record for %s, got %d" %
                (node, operation, len(rows)))
        history, incarnation, source_id, message_id, source, received, own, verdict, sequence, disposition = rows[0]
        path = self.configs[node].parent / (operation + "-received.eml")
        path.write_bytes(received)
        checked = subprocess.run(
            [sys.executable, str(self.root / "tools/fn_verify.py"), "check-article",
             str(path), message_id, "--keyring", config["keyring"]],
            capture_output=True, env=self.mission.lab.env, timeout=120)
        check = json.loads(checked.stdout)
        require(checked.returncode == 0 and check.get("outcome") == own == "verified",
                node + ": independent verification failed: " +
                str(check.get("reason", checked.stderr.decode(errors="replace"))))
        signatures = check.get("signatures", {})
        require(set(signatures) == {"ed25519", "ml-dsa-65"}, "both signatures must be recorded")
        return {"history": history, "incarnation": incarnation, "source_id": source_id,
                "operation": [self.application, operation], "message_id": message_id,
                "source_sha256": digest(source), "stored_projection_sha256": digest(received),
                "ed25519_sha256": digest(bytes.fromhex(signatures["ed25519"])),
                "ml_dsa_65_sha256": digest(bytes.fromhex(signatures["ml-dsa-65"])),
                "own_verdict": own, "node_verdict": verdict, "store_sequence": sequence,
                "disposition": disposition}, source

    def originate(self, payload):
        summary = self.invoke("a", "setup-a-application-report", "report", "r1", payload)
        require(len(summary["outbox"]) == 1 and summary["outbox"][0]["state"] == "stored",
                "A's report was not durably observed stored")
        self.observations["a_after_origination"] = summary
        return self.submission("a", "r1")

    def consume_report(self):
        self.invoke("b", "b-application-in-transaction", "wake", cut="in-transaction")
        empty = self.summary("b", "b-application-after-rollback")
        require(empty["transitions"] == [] and empty["outbox"] == [],
                "B's interrupted transaction did not roll back")
        self.invoke("b", "b-application-after-commit", "wake", cut="after-commit")
        committed = self.summary("b", "b-application-before-ack")
        require(committed["transitions"] == [[self.application, "r1"]]
                and committed["pending_ack"] == "unsent", "B's committed operation/ACK boundary differs")
        summary = self.invoke("b", "b-application-recover", "wake")
        repeat = self.invoke("b", "b-application-repeat-wake", "wake")
        require(summary["transitions"] == repeat["transitions"] == [[self.application, "r1"]],
                "B executed a second application transition")
        require(len(repeat["outbox"]) == 1 and repeat["outbox"][0]["state"] == "stored",
                "B's immutable reply was not durably observed stored")
        self.observations["b_after_commit"] = committed
        self.observations["b_after_recovery"] = repeat
        return self.received("b", "r1"), self.submission("b", "reply-r1")

    def consume_reply(self):
        self.invoke("a", "a-application-after-ack", "wake", cut="after-ack")
        summary = self.invoke("a", "a-application-recover", "wake")
        repeat = self.invoke("a", "a-application-repeat-wake", "wake")
        require(summary["transitions"] == repeat["transitions"] == [[self.application, "reply-r1"]],
                "A executed a second application transition")
        require(repeat["state"].get("replies") == "1", "A did not correlate exactly one reply")
        require(any(row["operation_id"] == "r1" and row["result"] == "replied"
                    for row in repeat["operations"]), "A's original operation was not settled by Q")
        self.observations["a_after_recovery"] = repeat
        report_at_a, _ = self.received("a", "r1")
        reply_at_a, source = self.received("a", "reply-r1")
        reply_at_b, _ = self.received("b", "reply-r1")
        report_artifact, _ = self.submission("a", "r1")
        reply_artifact, _ = self.submission("b", "reply-r1")
        report_at_b, _ = self.received("b", "r1")
        hops = {"R": {"submission": report_artifact, "at_a": report_at_a, "at_b": report_at_b},
                "Q": {"submission": reply_artifact, "at_a": reply_at_a, "at_b": reply_at_b}}
        for hop in hops.values():
            for received in (hop["at_a"], hop["at_b"]):
                for field in ("message_id", "source_sha256", "ed25519_sha256", "ml_dsa_65_sha256"):
                    require(received[field] == hop["submission"][field], "carried artifact changed: " + field)
        self.observations["hops"] = hops
        return reply_at_a, source
