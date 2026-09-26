"""Two sleeping agents on TWO fn nodes exchange a signed report and a reply.

Node A and node B are separate developer-image owners with separate Stores,
peered over NNTP: each pushes fn.* to the other (streaming feed), and B also
pulls from A by NEWNEWS through a recording proxy, so the same article can
reach B by two paths.  Agent A's consumer talks only to A's control socket,
agent B's only to B's; neither consumer talks to the other node.

  A authors R (hybrid-author into A's Store)
    -> A's feed carries R to B; B's pull lists R again
    -> B's consumer verifies R with ITS OWN keyring, commits its one
       transition and immutable reply Q, and acks its position
    -> B's feed carries Q to A
    -> A's consumer verifies Q with its own keyring and correlates it.

The cases (SCN-106; specs/consumer-progress.md "Two nodes", CNS-004):

- test_exchange_across_two_nodes_and_every_cut: the six ownership cuts on
  B's side and A's correlation side, the lost reply (Q's POST uncertain at
  B, the resend answered duplicate), the repeated transfer (feed and pull;
  one Store event at B; an IHAVE of R answered 435), a node restart
  mid-poll (the same page re-served, the ack idempotent), and the per-hop
  identity table (authored source and both signatures identical at both
  hops; the hop-local stored projections differ).
- test_revoked_author_settles_by_observation_across_nodes: PKT-322's case
  with a second node: A accepts R and the consumer dies before recording
  the answer, A revokes the author; B still consumes R, carried before the
  revocation; A's resend is refused and settles only that resend; R is
  stored by store-observation.

Python here is the test tool: it starts processes, cuts them and reads the
owners' facts (the consumer databases, `consumer status`, `operator status`,
NNTP STAT/IHAVE).  It decides nothing fn or the consumer decides.

Opt-in: FN_RUN_CONSUMER_EXCHANGE=1 and FN_NATIVE_DEVELOPER_HOST naming a
source-matched developer image (the owner stop cut is developer-only).
FN_CONSUMER_EXCHANGE_EVIDENCE names a directory for the per-case witnesses.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time
import unittest

from tests.native_process import stop_and_diagnostics
from tests.test_native_peer_pull import RecordingProxy

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
ENABLED = os.environ.get("FN_RUN_CONSUMER_EXCHANGE") == "1"
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
CONSUMER = ROOT / "tools" / "fn_consumer.py"
VERIFIER = ROOT / "tools" / "fn_verify.py"
APP = "fn-e1"
PULL_INTERVAL = "2"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def sha(octets):
    return hashlib.sha256(octets).hexdigest()


@unittest.skipUnless(ENABLED and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_RUN_CONSUMER_EXCHANGE=1 and a source-matched "
                     "FN_NATIVE_DEVELOPER_HOST")
class NativeTwoNodeConsumerExchangeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-consumer-2n-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_NATIVE_CONTROL_FAULT",
                     "FN_NATIVE_CONTROL_TEST_STOP", "FN_CONSUMER_CUT"):
            self.env.pop(name, None)
        self.log = []
        self.nodes = {}
        self.principals = {}
        self.addCleanup(self.stop_all)

    # -- native processes -----------------------------------------------------
    def native(self, *words, expected=0):
        result = subprocess.run([str(IMAGE), "--fn", *map(str, words)],
                                cwd=ROOT, env=self.env, capture_output=True,
                                timeout=300, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected,
                             (result.stdout + result.stderr).decode("utf-8", "replace"))
        return result

    def initialize(self, name):
        root = self.root / name
        root.mkdir()
        node = {"name": name, "root": root, "store": root / "store",
                "control": root / "control.sock", "config": root / "fn.toml",
                "port": free_port(), "log": root / "service.log",
                "path": "%s.exchange.example.invalid" % name.lower(),
                "process": None, "starts": 0}
        node["config"].write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                node["store"], node["port"], node["control"], node["log"]),
            encoding="ascii")
        self.native("store", node["store"], "init", "fn.test")
        self.native("operator", node["config"], "policy", "set", "path-identity",
                    node["path"])
        self.nodes[name] = node
        return node

    def peer(self, source, target, port=None):
        """SOURCE's record for TARGET: inbound and outbound fn.*, transit from
        127.0.0.1, streaming; PORT (a proxy) in place of TARGET's own."""
        self.native("operator", source["config"], "peer", "add", target["name"],
                    target["path"], "127.0.0.1", port or target["port"],
                    "fn.*", "fn.*", "127.0.0.1", "true")

    def start(self, node, *, stop_after_submit=False):
        env = dict(self.env)
        if stop_after_submit:
            env["FN_NATIVE_CONTROL_TEST_STOP"] = "after-submit"
        node["starts"] += 1
        out = node["root"] / ("owner-%d.stdout" % node["starts"])
        with open(out, "wb") as stdout, open(node["root"] / "owner.stderr", "ab") as err:
            node["process"] = subprocess.Popen(
                [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
                cwd=ROOT, env=env, stdin=subprocess.DEVNULL, stdout=stdout, stderr=err)
        node["stdout"] = out
        self.await_output(node, b"LISTENING %d" % node["port"], 120)

    def await_output(self, node, needle, timeout):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if needle in node["stdout"].read_bytes():
                return
            if node["process"].poll() is not None:
                self.fail("%s owner exited %s before %r: %s" % (
                    node["name"], node["process"].returncode, needle,
                    (node["root"] / "owner.stderr").read_bytes()[-2000:]))
            time.sleep(0.1)
        self.fail("%s owner never printed %r" % (node["name"], needle))

    def stop(self, node):
        process = node["process"]
        node["process"] = None
        diagnostics = stop_and_diagnostics(process, timeout=60)
        self.assertEqual(process.returncode, 0, diagnostics)

    def kill(self, node):
        process = node["process"]
        node["process"] = None
        process.send_signal(signal.SIGKILL)
        process.wait(timeout=30)

    def stop_all(self):
        for node in self.nodes.values():
            process = node.get("process")
            if process is not None and process.poll() is None:
                process.kill()
                process.wait(timeout=30)

    # -- NNTP observation (the Store's own answers) ----------------------------
    def session(self, node, lines):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            greeting = stream.readline()
            self.assertTrue(greeting[:3] in (b"200", b"201"), greeting)
            replies = []
            for line in lines:
                stream.write(line)
                replies.append(stream.readline())
            return replies

    def stat(self, node, message_id):
        return self.session(node, [b"STAT " + message_id.encode("ascii") + b"\r\n"])[0][:3]

    def await_article(self, node, message_id, timeout=90):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            try:
                if self.stat(node, message_id) == b"223":
                    return
            except OSError:
                pass
            time.sleep(0.25)
        self.fail("%s never stored %s; log tail %r" % (
            node["name"], message_id, self.log_tail(node)))

    def log_tail(self, node):
        try:
            return node["log"].read_text(errors="replace")[-2000:]
        except OSError:
            return ""

    def pull_rounds(self, node):
        try:
            return sum("round=done" in line for line in
                       node["log"].read_text(errors="replace").splitlines()
                       if line.startswith("pull peer="))
        except OSError:
            return 0

    def await_pull_round(self, node, after, timeout=90):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if self.pull_rounds(node) > after:
                return
            time.sleep(0.25)
        self.fail("%s finished no pull round after %d; log %r" % (
            node["name"], after, self.log_tail(node)))

    def articles(self, node):
        out = self.native("operator", node["config"], "status").stdout
        match = re.search(rb"\barticles=(\d+)", out)
        self.assertIsNotNone(match, out)
        return int(match.group(1))

    def status(self, node, label):
        out = self.native("consumer", "status", node["control"], label).stdout
        match = re.search(rb"committed-ack=(\d+) committed-journal-frontier=(\d+)", out)
        self.assertIsNotNone(match, out)
        return int(match.group(1)), int(match.group(2))

    # -- agents ---------------------------------------------------------------
    def signer(self, label, principal_byte):
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
        return keys, (bytes([principal_byte]) * 32).hex()

    def agent(self, label, principal_byte, generation, node):
        """An author whose keys every node enrols (in the same generation
        order), and a consumer of NODE only."""
        keys, principal_hex = self.signer(label, principal_byte)
        self.principals[label] = (keys, principal_hex, generation)
        for each in self.nodes.values():
            self.native("hybrid-enroll", each["control"], generation, keys["principal"],
                        keys["ed_public"], keys["ml_public"])
        config = self.root / label / "consumer.json"
        config.write_text(json.dumps({
            "image": str(IMAGE), "control": str(node["control"]),
            "consumer": label, "group": "fn.test", "application_id": APP,
            "from": "%s@example.invalid" % label,
            "db": str(self.root / label / "state.db"),
            "work": str(self.root / label / "work"), "keys": keys,
            "principal_hex": principal_hex, "generation": str(generation),
            "keyring": str(self.root / label / "trusted.json"), "claims": []}),
            encoding="utf-8")
        self.native("consumer", "register", node["control"], label, "fn.test",
                    self.root / label / "registered.fncu")
        return config

    def trust(self, config, labels, claims):
        """The consumer's own keyring (from the authors' public key files,
        never from a node) and the application's claims."""
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

    def consumer(self, config, *words, cut=None, expected=0, background=False):
        env = dict(self.env)
        if cut:
            env["FN_CONSUMER_CUT"] = cut
        argv = [sys.executable, str(CONSUMER), str(config), *words]
        if background:
            return subprocess.Popen(argv, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True,
                                timeout=900, check=False)
        self.log.append([config.parent.name, list(words), cut, result.returncode,
                         result.stderr.decode("utf-8", "replace")[-600:]])
        if expected is not None:
            self.assertEqual(result.returncode, expected,
                             (result.stdout + result.stderr).decode("utf-8", "replace"))
        if cut:
            self.assertIn(("CONSUMER-CUT " + cut).encode(), result.stderr)
        return result

    def summary(self, config):
        return json.loads(self.consumer(config, "summary").stdout)

    def cut_at_owner(self, node, config, *words):
        """NODE's owner completes the consumer's first control request and
        stops before replying (developer FN_NATIVE_CONTROL_TEST_STOP); the
        consumer's outcome is uncertain (exit 3); the owner restarts."""
        self.stop(node)
        self.start(node, stop_after_submit=True)
        proc = self.consumer(config, *words, background=True)
        self.await_output(node, b"CONTROL-SUBMITTED", 300)
        self.kill(node)
        stdout, stderr = proc.communicate(timeout=300)
        self.log.append([config.parent.name, list(words), "owner-after-submit",
                         proc.returncode, stderr.decode("utf-8", "replace")[-600:]])
        self.assertEqual(proc.returncode, 3, (stdout + stderr).decode("utf-8", "replace"))
        self.start(node)
        return json.loads(stdout)

    def inbox(self, config, operation_id):
        """The consumer database's inbox rows for OPERATION_ID (its owner's
        record), with the received article re-checked independently."""
        data = json.loads(config.read_text(encoding="utf-8"))
        db = sqlite3.connect(data["db"])
        try:
            rows = db.execute(
                "SELECT message_id, source, received, disposition, own_verdict, "
                "node_verdict, store_sequence FROM inbox WHERE operation_id=? "
                "ORDER BY store_sequence", (operation_id,)).fetchall()
        finally:
            db.close()
        out = []
        for message_id, source, received, disposition, own, node_verdict, seq in rows:
            article = self.root / ("check-%s" % sha(received))
            article.write_bytes(received)
            check = subprocess.run(
                [sys.executable, str(VERIFIER), "check-article", str(article), message_id,
                 "--keyring", data["keyring"]], capture_output=True, timeout=120)
            verdict = json.loads(check.stdout)
            out.append({"message_id": message_id, "source_sha256": sha(source),
                        "received_sha256": sha(received),
                        "received_path": received.split(b"\r\n", 1)[0].decode(
                            "ascii", "replace"),
                        "disposition": disposition, "own_verdict": own,
                        "node_verdict": node_verdict, "store_sequence": seq,
                        "check": verdict.get("outcome"),
                        "check_source_sha256": verdict.get("source-sha256"),
                        "signatures_sha256": sha(json.dumps(
                            verdict.get("signatures"), sort_keys=True).encode())})
        return out

    def submission(self, config, operation_id):
        data = json.loads(config.read_text(encoding="utf-8"))
        db = sqlite3.connect(data["db"])
        try:
            message_id, source, ed, ml = db.execute(
                "SELECT message_id, source, ed_sig, ml_sig FROM submissions "
                "WHERE operation_id=?", (operation_id,)).fetchone()
        finally:
            db.close()
        return {"message_id": message_id, "source_sha256": sha(source),
                "signatures_sha256": sha(json.dumps(
                    {"ed25519": ed.hex(), "ml-dsa-65": ml.hex()},
                    sort_keys=True).encode())}

    def witness(self, case, data):
        data = dict(data, case=case, log=self.log, image_sha256=sha(IMAGE.read_bytes()))
        text = json.dumps(data, indent=1, sort_keys=True)
        print("CONSUMER-2N-WITNESS %s sha256=%s" % (case, sha(text.encode())), flush=True)
        print(text, flush=True)
        out = os.environ.get("FN_CONSUMER_EXCHANGE_EVIDENCE")
        if out:
            Path(out).mkdir(parents=True, exist_ok=True)
            (Path(out) / (case + ".json")).write_text(text, encoding="utf-8")

    def two_nodes(self):
        """A and B peered both ways; B also pulls from A through a proxy."""
        a, b = self.initialize("A"), self.initialize("B")
        proxy = RecordingProxy(a["port"])
        self.addCleanup(proxy.close)
        self.peer(a, b)
        self.peer(b, a, port=proxy.port)
        self.native("operator", b["config"], "peer", "pull", "A", PULL_INTERVAL)
        for node in (a, b):
            self.start(node)
            self.native("consumer", "bootstrap", node["control"])
        return a, b, proxy

    # -- the cases ------------------------------------------------------------
    def test_exchange_across_two_nodes_and_every_cut(self):
        a, b, proxy = self.two_nodes()
        agent_a = self.agent("agent-a", 0xA1, 1, a)
        agent_b = self.agent("agent-b", 0xB2, 2, b)
        # A probe consumer on B, registered before R exists: the test's own
        # reader for the restart-mid-poll case (fn's poll and ack, nothing
        # of agent-b's).
        self.native("consumer", "register", b["control"], "probe", "fn.test",
                    self.root / "probe-registered.fncu")
        for config in (agent_a, agent_b):
            self.trust(config, ("agent-a", "agent-b"),
                       (("r", "agent-a"), ("reply-", "agent-b")))

        # A authors R into A's Store and sleeps.
        self.consumer(agent_a, "report", "r1", "dregg-receipt-0001")
        [r_out] = self.summary(agent_a)["outbox"]
        self.assertEqual(r_out["state"], "stored", r_out)
        r_id = r_out["message_id"]

        # The repeated transfer: R reaches B by A's feed and is listed again
        # by B's NEWNEWS pull; B's Store holds one event for it, and a third
        # offer (IHAVE from the peer's address) is answered 435.
        self.await_article(b, r_id)
        rounds = self.pull_rounds(b)
        self.await_pull_round(b, rounds)
        self.await_pull_round(b, rounds + 1)
        newnews = proxy.newnews()
        pulled_r = [c for c in proxy.commands if c.upper().startswith("ARTICLE")
                    and r_id in c]
        ihave = self.session(b, [b"IHAVE " + r_id.encode("ascii") + b"\r\n"])[0]
        self.assertTrue(ihave.startswith(b"435"), ihave)
        self.assertEqual(self.articles(b), 1)
        self.assertTrue(newnews, "B's pull asked no NEWNEWS")
        transfer = {"newnews": newnews[:4], "pull_article_commands_for_r": pulled_r,
                    "ihave_r_at_b": ihave.decode("ascii", "replace").strip(),
                    "articles_at_b": 1}

        # Node restart mid-poll (the probe): poll, restart B, poll again: the
        # same page; the ack twice: one position.
        probe_cursor, probe_report = self.root / "probe-1.fncu", self.root / "probe-1.fn-e"
        self.native("consumer", "poll", b["control"], "probe", probe_cursor, probe_report)
        self.stop(b)
        self.start(b)
        again_cursor, again_report = self.root / "probe-2.fncu", self.root / "probe-2.fn-e"
        self.native("consumer", "poll", b["control"], "probe", again_cursor, again_report)
        self.assertEqual(probe_report.read_bytes(), again_report.read_bytes())
        self.assertEqual(probe_cursor.read_bytes(), again_cursor.read_bytes())
        self.assertGreater(len(probe_report.read_bytes()), 0)
        self.native("consumer", "ack", b["control"], again_cursor)
        acked = self.status(b, "probe")[0]
        self.native("consumer", "ack", b["control"], again_cursor)
        self.assertEqual(self.status(b, "probe")[0], acked)
        restart = {"report_sha256": sha(probe_report.read_bytes()),
                   "cursor_sha256": sha(probe_cursor.read_bytes()), "acked": acked}

        # Cut 1: B dies inside its transaction; B's database holds nothing,
        # B's position did not move.
        self.consumer(agent_b, "wake", cut="in-transaction", expected=97)
        s = self.summary(agent_b)
        self.assertEqual((s["operations"], s["outbox"], s["transitions"],
                          s["pending_ack"]), ([], [], [], None))
        self.assertEqual(self.status(b, "agent-b")[0], 0)

        # Cut 2 (a consumer death between the claim's commit and the ack):
        # the transition and Q's artifact are committed, the ack is not sent.
        self.consumer(agent_b, "wake", cut="after-commit", expected=97)
        s = self.summary(agent_b)
        self.assertEqual(s["transitions"], [[APP, "r1"]])
        self.assertEqual([o["state"] for o in s["outbox"]], ["pending"])
        self.assertEqual(s["pending_ack"], "unsent")
        self.assertEqual(self.status(b, "agent-b")[0], 0)

        # Cut 3: B's owner commits the ack and dies before replying.
        s = self.cut_at_owner(b, agent_b, "wake")
        self.assertEqual(s["pending_ack"], "uncertain")
        b_acked = self.status(b, "agent-b")[0]
        self.assertGreater(b_acked, 0)

        # Cut 4: the durable ack settled by position; death before Q's POST.
        self.consumer(agent_b, "wake", cut="before-post", expected=97)
        s = self.summary(agent_b)
        self.assertIsNone(s["pending_ack"])
        self.assertEqual([o["state"] for o in s["outbox"]], ["pending"])
        self.assertEqual(self.status(b, "agent-b")[0], b_acked)

        # Cut 5, the lost reply: B's owner stores Q and dies before
        # answering; the resend of the saved artifact is answered duplicate
        # (D25) or Q is observed in B's Store.  Still one transition.
        s = self.cut_at_owner(b, agent_b, "wake")
        [q_out] = s["outbox"]
        self.assertEqual(q_out["state"], "uncertain")
        self.consumer(agent_b, "wake")
        s = self.summary(agent_b)
        [q_out] = s["outbox"]
        self.assertEqual((q_out["state"], q_out["attempts"]), ("stored", 2), q_out)
        self.assertIn((q_out["last_exit"], q_out["settled_by"]),
                      ((0, "post-answer"), (1, "store-observation")))
        self.assertEqual(s["transitions"], [[APP, "r1"]])
        q_id = q_out["message_id"]

        # Cut 6: Q crosses back to A while A sleeps; A dies after its ack,
        # then correlates Q with R on the next wake: one transition.
        self.await_article(a, q_id)
        self.assertEqual(self.status(a, "agent-a")[0], 0)
        self.consumer(agent_a, "wake", cut="after-ack", expected=97)
        self.consumer(agent_a, "wake")
        s = self.summary(agent_a)
        self.assertEqual(s["transitions"], [[APP, "reply-r1"]])
        self.assertEqual(s["state"].get("replies"), "1")
        self.assertEqual([(o["operation_id"], o["result"]) for o in s["operations"]
                          if o["operation_id"] == "r1"], [("r1", "replied")])
        self.assertEqual([i["disposition"] for i in s["inbox"]], ["repeat", "applied"])
        # Every consumer reaches its own frontier and sees no second event.
        self.consumer(agent_b, "wake")
        self.consumer(agent_a, "wake")
        sb = self.summary(agent_b)
        self.assertEqual(sb["transitions"], [[APP, "r1"]])
        self.assertEqual([(i["operation_id"], i["disposition"]) for i in sb["inbox"]],
                         [("r1", "applied"), ("reply-r1", "repeat")])
        self.assertEqual(self.summary(agent_a)["transitions"], [[APP, "reply-r1"]])
        self.assertEqual((self.articles(a), self.articles(b)), (2, 2))

        # The per-hop identities: the authored source and both signatures
        # are the submission's at every hop; each hop's stored projection
        # (the received article, with that node's Path) is its own.
        hops = {"R": {"submission": self.submission(agent_a, "r1"),
                      "at_a": self.inbox(agent_a, "r1"), "at_b": self.inbox(agent_b, "r1")},
                "Q": {"submission": self.submission(agent_b, "reply-r1"),
                      "at_b": self.inbox(agent_b, "reply-r1"),
                      "at_a": self.inbox(agent_a, "reply-r1")}}
        for name, hop in hops.items():
            [at_a], [at_b] = hop["at_a"], hop["at_b"]
            want = hop["submission"]
            for row in (at_a, at_b):
                self.assertEqual((row["message_id"], row["source_sha256"],
                                  row["check_source_sha256"], row["signatures_sha256"],
                                  row["check"], row["own_verdict"]),
                                 (want["message_id"], want["source_sha256"],
                                  want["source_sha256"], want["signatures_sha256"],
                                  "verified", "verified"), (name, row))
            # The hop-local projections MAY differ (each node's Path); what
            # they are is recorded, not required.
            hop["projections_differ"] = at_a["received_sha256"] != at_b["received_sha256"]
        self.witness("exchange-two-nodes", {
            "transfer": transfer, "restart_mid_poll": restart, "hops": hops,
            "q_settled_by": q_out["settled_by"], "b_acked": b_acked,
            "positions": {"agent-a": self.status(a, "agent-a")[0],
                          "agent-b": self.status(b, "agent-b")[0]}})
        self.stop(a)
        self.stop(b)

    def test_revoked_author_settles_by_observation_across_nodes(self):
        a, b, _ = self.two_nodes()
        agent_a = self.agent("agent-a", 0xA1, 1, a)
        agent_b = self.agent("agent-b", 0xB2, 2, b)
        for config in (agent_a, agent_b):
            self.trust(config, ("agent-a", "agent-b"),
                       (("r", "agent-a"), ("reply-", "agent-b")))
        # A's owner accepts R; the consumer dies before recording the answer.
        self.consumer(agent_a, "report", "r1", "dregg-receipt-0001", cut="after-post",
                      expected=97)
        [after_death] = self.summary(agent_a)["outbox"]
        self.assertEqual((after_death["state"], after_death["attempts"]),
                         ("uncertain", 1), after_death)
        # R was carried to B before the revocation; B consumes it.
        self.await_article(b, after_death["message_id"])
        keys = self.principals["agent-a"][0]
        self.native("hybrid-revoke-next", a["control"], keys["principal"])
        self.consumer(agent_b, "wake")
        self.assertEqual(self.summary(agent_b)["transitions"], [[APP, "r1"]])
        # A's reconciliation resend is refused (revoked) and settles only
        # itself; R is stored by A's Store serving the artifact back.
        woke = self.consumer(agent_a, "wake", expected=None)
        [final] = self.summary(agent_a)["outbox"]
        self.assertEqual(woke.returncode, 0, woke.stderr)
        self.assertEqual((final["state"], final["settled_by"]),
                         ("stored", "store-observation"), final)
        self.assertEqual([(j["purpose"], j["state"], j["exit"]) for j in final["journal"]],
                         [("submit", "unanswered", None), ("reconcile", "answered", 1)])
        self.assertEqual(final["sha256"], after_death["sha256"])
        self.witness("revoked-author-two-nodes", {
            "a_outbox": final, "b_transitions": self.summary(agent_b)["transitions"]})
        self.stop(a)
        self.stop(b)


if __name__ == "__main__":
    unittest.main()
