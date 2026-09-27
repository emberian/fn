"""Opt-in two-node native ingress/outbound-feed composition witness.

Python is the external harness and pre-start configuration tool.  Both running
nodes are the production saved image through its public operator entry; no
Python service or feed process participates after startup.
"""

import hashlib
import json
import os
from pathlib import Path
import socket
import struct
import subprocess
import tempfile
import threading
import time
import unittest

from tests.native_process import wait_for_announcement


ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
CORE = Path(str(IMAGE) + ".core") if IMAGE is not None else None
SOURCE = os.environ.get("FN_NATIVE_IMAGE_SOURCE_SHA")
LAUNCHER_SHA256 = os.environ.get("FN_NATIVE_LAUNCHER_SHA256")
CORE_SHA256 = os.environ.get("FN_NATIVE_CORE_SHA256")
RUNTIME_SHA256 = os.environ.get("FN_NATIVE_RUNTIME_SHA256")


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


ACTUAL_LAUNCHER = digest(IMAGE) if IMAGE is not None and IMAGE.is_file() else None
ACTUAL_CORE = digest(CORE) if CORE is not None and CORE.is_file() else None
READY = bool(
    IMAGE_TEXT and IMAGE is not None and CORE is not None
    and IMAGE.is_file() and os.access(IMAGE, os.X_OK) and CORE.is_file()
    and LAUNCHER_SHA256 == ACTUAL_LAUNCHER
    and CORE_SHA256 == ACTUAL_CORE and RUNTIME_SHA256)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class ScriptedTransitPeer:
    """A minimal INN-shaped transit server for fn's outbound feed.

    It greets with 200, answers MODE STREAM with MODE_REPLY (203 streams;
    501 is what a server without RFC 4644 answers, RFC 3977 section 3.2.1),
    and then takes IHAVE (335 / 235) or CHECK / TAKETHIS (238 / 239) the way
    INN's innd does.  Every command line it reads is recorded with its
    connection number, so a test can say which form carried each article.
    """

    def __init__(self, mode_reply):
        self.mode_reply = mode_reply
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        self.commands = []
        self.articles = {}
        self.lock = threading.Lock()
        self.connections = 0
        self.closed = False
        threading.Thread(target=self.serve, daemon=True).start()

    def close(self):
        self.closed = True
        self.listener.close()

    def serve(self):
        while not self.closed:
            try:
                client, _ = self.listener.accept()
            except OSError:
                return
            with self.lock:
                self.connections += 1
                number = self.connections
            threading.Thread(target=self.session, args=(client, number),
                             daemon=True).start()

    def read_article(self, stream):
        body = bytearray()
        while True:
            line = stream.readline()
            if not line or line == b".\r\n":
                return bytes(body)
            body.extend(line[1:] if line.startswith(b"..") else line)

    def session(self, client, number):
        with client:
            stream = client.makefile("rwb", buffering=0)
            stream.write(b"200 scripted transit peer\r\n")
            while True:
                line = stream.readline()
                if not line:
                    return
                text = line.rstrip(b"\r\n").decode("ascii", "replace")
                with self.lock:
                    self.commands.append((number, text))
                words = text.split()
                verb = words[0].upper() if words else ""
                if verb == "MODE":
                    stream.write(self.mode_reply.encode("ascii") + b"\r\n")
                elif verb == "IHAVE":
                    stream.write(b"335 send it\r\n")
                    article = self.read_article(stream)
                    with self.lock:
                        self.articles[words[1]] = ("IHAVE", article)
                    stream.write(b"235 article transferred OK\r\n")
                elif verb == "CHECK":
                    stream.write(b"238 " + words[1].encode("ascii") + b"\r\n")
                elif verb == "TAKETHIS":
                    article = self.read_article(stream)
                    with self.lock:
                        self.articles[words[1]] = ("TAKETHIS", article)
                    stream.write(b"239 " + words[1].encode("ascii") + b"\r\n")
                elif verb == "QUIT":
                    stream.write(b"205 bye\r\n")
                    return
                else:
                    stream.write(b"500 unknown command\r\n")

    def await_article(self, message_id, timeout=60):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            with self.lock:
                if message_id in self.articles:
                    return self.articles[message_id]
            time.sleep(0.1)
        return None


@unittest.skipUnless(
    READY,
    "set explicit native image/source and matching launcher/core SHA-256 values",
)
class NativePeeringTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        print("native-peering launcher-sha256={} core-sha256={} declared-source={}".format(
            ACTUAL_LAUNCHER, ACTUAL_CORE, SOURCE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-peering-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.processes = []
        self.addCleanup(self.stop_all)

    def command(self, arguments, expected=0, timeout=180):
        result = subprocess.run(
            list(map(str, arguments)), cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False)
        self.assertEqual(result.returncode, expected,
                         "command {} returned {}\nstdout={}\nstderr={}".format(
                             arguments, result.returncode,
                             result.stdout.decode("utf-8", "replace"),
                             result.stderr.decode("utf-8", "replace")))
        return result

    def initialize(self, name, port):
        root = self.base / name
        store = root / "store"
        control = root / "control.sock"
        root.mkdir()
        self.command([IMAGE, "--fn", "store", store, "init", "fn.test"])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(store, port, control),
            encoding="ascii")
        return {"name": name, "root": root, "store": store,
                "control": control, "config": config, "port": port}

    def process_identity(self, process):
        proc = Path("/proc") / str(process.pid)
        if not proc.is_dir():
            return {"status": "unknown", "reason": "/proc unavailable"}
        try:
            runtime = Path(os.readlink(proc / "exe"))
            words = (proc / "cmdline").read_bytes().split(b"\0")[:-1]
            core = Path(words[words.index(b"--core") + 1].decode("utf-8"))
            return {"status": "observed", "runtime": str(runtime),
                    "runtime_sha256": digest(runtime), "core": str(core),
                    "core_sha256": digest(core)}
        except (OSError, UnicodeError, ValueError, IndexError) as error:
            return {"status": "unknown", "reason": "{}: {}".format(
                type(error).__name__, error)}

    def verify_process_identity(self, node):
        found = self.process_identity(node["process"])
        if found["status"] != "observed":
            self.skipTest("cannot observe native runtime/core: {}".format(found["reason"]))
        self.assertEqual(found["runtime_sha256"], RUNTIME_SHA256, found)
        self.assertEqual(found["core_sha256"], CORE_SHA256, found)
        node.setdefault("identities", []).append(found)
        return found

    def configure_peer(self, source, target, outbound="fn.*"):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], "{}.example.invalid".format(target["name"]),
            "127.0.0.1", str(target["port"]), "fn.*", outbound,
            "127.0.0.1", "true",
        ])

    def start(self, node):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.processes.append(process)
        node["process"] = process
        line = wait_for_announcement(process, b"LISTENING ")
        self.assertEqual(line, "LISTENING {}\n".format(node["port"]).encode(),
                         "{} emitted an unexpected readiness line: {!r}".format(
                             node["name"], line))
        node["process"] = process
        self.verify_process_identity(node)

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
        for process in self.processes:
            if process.poll() is None:
                process.wait(timeout=30)
            if process.stdout:
                process.stdout.close()
            if process.stderr:
                process.stderr.close()
        self.processes = []

    @staticmethod
    def article(message_id, marker):
        return ("From: sender@example.invalid\r\n"
                "Newsgroups: fn.test\r\n"
                "Subject: native two-node {}\r\n"
                "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                "Message-ID: {}\r\n\r\n{}\r\n".format(
                    marker, message_id, marker)).encode("ascii")

    def post(self, node, message_id, marker):
        payload = node["root"] / (marker + ".article")
        payload.write_bytes(self.article(message_id, marker))
        self.command([IMAGE, "--fn", "operator", node["config"], "post",
                      "--message-id", message_id, "--payload", payload,
                      "--group", "fn.test"])

    def article_from(self, node, message_id):
        try:
            client = socket.create_connection(("127.0.0.1", node["port"]), timeout=10)
        except ConnectionRefusedError:
            process = node.get("process")
            if process is not None and process.poll() is not None:
                self.fail("{} exited while awaiting article: {}".format(
                    node["name"], process.stderr.read().decode("utf-8", "replace")))
            return None
        with client:
            stream = client.makefile("rwb", buffering=0)
            if not stream.readline().startswith(b"200 "):
                return None
            stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
            if not stream.readline().startswith(b"220 "):
                return None
            article = bytearray()
            while True:
                line = stream.readline()
                if line == b".\r\n":
                    return self.stored_octets(bytes(article))
                if not line:
                    return None
                article.extend(line[1:] if line.startswith(b"..") else line)

    def stored_octets(self, served):
        # ARTICLE serves this node's Xref line first, then the stored octets
        # (NNT-052, PKT-668; D01): the comparisons below are of the octets
        # the nodes store and relay, so the one leading Xref line goes.
        if served.startswith(b"Xref: "):
            head, _, rest = served.partition(b"\r\n")
            self.assertNotIn(b"\r\nXref: ", rest.split(b"\r\n\r\n", 1)[0])
            return rest
        return served

    def await_article(self, node, message_id, timeout=60):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            article = self.article_from(node, message_id)
            if article is not None:
                return article
            time.sleep(0.1)
        self.fail("{} did not receive {}".format(node["name"], message_id))

    def duplicate_offer(self, node, message_id):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=10) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + message_id.encode("ascii") + b"\r\n")
            return stream.readline()

    def transfer_then_reset_before_reply(self, node, message_id, marker):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=10)
        greeting = bytearray()
        while not greeting.endswith(b"\n"):
            chunk = client.recv(1)
            self.assertTrue(chunk)
            greeting.extend(chunk)
        self.assertTrue(greeting.startswith(b"200 "))
        payload = self.article(message_id, marker).replace(b"\r\n.\r\n", b"\r\n..\r\n")
        client.sendall(b"TAKETHIS " + message_id.encode("ascii") + b"\r\n"
                       + payload + b".\r\n")
        # Force a reset while the owner is completing the accepted article.
        # A reply write may fail, but that connection-local failure must not
        # be reclassified as an ambiguous Store outcome or stop the owner.
        client.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                          struct.pack("ii", 1, 0))
        client.close()

    def transit(self, node, message_id, source):
        """Drive the public peer port through IHAVE and compare served octets."""
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=10) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + message_id.encode("ascii") + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"335 "))
            for line in source.splitlines(keepends=True):
                self.assertTrue(line.endswith(b"\r\n"))
                stream.write(b"." + line if line.startswith(b".") else line)
            stream.write(b".\r\n")
            self.assertTrue(stream.readline().startswith(b"235 "))

    def capabilities(self, node):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=10) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"CAPABILITIES\r\n")
            self.assertTrue(stream.readline().startswith(b"101 "))
            lines = []
            while True:
                line = stream.readline()
                if line == b".\r\n":
                    break
                self.assertNotEqual(line, b"")
                lines.append(line.rstrip(b"\r\n"))
            # Keep this on one connection: it detects a worker that returns
            # after every successful read instead of only after QUIT/close.
            stream.write(b"QUIT\r\n")
            self.assertTrue(stream.readline().startswith(b"205 "))
            return lines

    def test_public_native_nodes_exchange_both_ways_and_suppress_duplicate(self):
        self.exchange_both_ways(live_configuration=False)

    def test_live_peer_configuration_activates_both_directions(self):
        self.exchange_both_ways(live_configuration=True)

    def exchange_both_ways(self, live_configuration):
        a = self.initialize("a", free_port())
        b = self.initialize("b", free_port())
        if not live_configuration:
            self.configure_peer(a, b)
            self.configure_peer(b, a)
        self.start(a)
        self.start(b)
        if live_configuration:
            self.configure_peer(a, b)
            self.configure_peer(b, a)
        self.assertIn(b"IHAVE", self.capabilities(a))
        self.assertIn(b"STREAMING", self.capabilities(a))
        self.assertIn(b"IHAVE", self.capabilities(b))
        self.assertIn(b"STREAMING", self.capabilities(b))

        transit_a_id = "<native-transit-a-to-b@example.invalid>"
        transit_a = self.article(transit_a_id, "transit-a-to-b")
        self.transit(b, transit_a_id, transit_a)
        self.assertEqual(self.await_article(b, transit_a_id), transit_a)
        transit_a_duplicate = self.duplicate_offer(b, transit_a_id)
        self.assertTrue(transit_a_duplicate.startswith(b"435 "))

        transit_b_id = "<native-transit-b-to-a@example.invalid>"
        transit_b = self.article(transit_b_id, "transit-b-to-a")
        self.transit(a, transit_b_id, transit_b)
        self.assertEqual(self.await_article(a, transit_b_id), transit_b)
        transit_b_duplicate = self.duplicate_offer(a, transit_b_id)
        self.assertTrue(transit_b_duplicate.startswith(b"435 "))

        a_id = "<native-a-to-b@example.invalid>"
        self.post(a, a_id, "a-to-b")
        a_source = self.await_article(a, a_id)
        b_article = self.await_article(b, a_id)
        self.assertEqual(b_article, a_source)
        a_duplicate = self.duplicate_offer(b, a_id)
        self.assertTrue(a_duplicate.startswith(b"435 "))

        b_id = "<native-b-to-a@example.invalid>"
        self.post(b, b_id, "b-to-a")
        b_source = self.await_article(b, b_id)
        a_article = self.await_article(a, b_id)
        self.assertEqual(a_article, b_source)
        b_duplicate = self.duplicate_offer(a, b_id)
        self.assertTrue(b_duplicate.startswith(b"435 "))
        identities = {node["name"]: self.verify_process_identity(node)
                      for node in (a, b)}
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "transit-and-feed", "transit": {
                "ab": {"offer": "335", "transfer": "235", "duplicate": "435",
                       "identical": True},
                "ba": {"offer": "335", "transfer": "235", "duplicate": "435",
                       "identical": True}},
            "feed": {"ab": {"identical": b_article == a_source,
                               "duplicate": a_duplicate[:3].decode()},
                     "ba": {"identical": a_article == b_source,
                               "duplicate": b_duplicate[:3].decode()}},
            "identity": identities,
        }, sort_keys=True))


    def test_durable_feed_requeues_after_source_process_death(self):
        a = self.initialize("restart-a", free_port())
        b = self.initialize("restart-b", free_port())
        self.configure_peer(a, b)
        # B starts after A is killed, but its peer record must exist before
        # that listener accepts A's loopback feed connection; otherwise it is
        # a reader connection and IHAVE is correctly refused as unauthorized.
        self.configure_peer(b, a, outbound="-")
        self.start(a)

        message_id = "<native-requeue-after-kill@example.invalid>"
        self.post(a, message_id, "requeue-after-kill")
        journal = a["store"] / "feed" / "restart-b.fnfd"
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline and not journal.is_file():
            time.sleep(0.05)
        self.assertTrue(journal.is_file(), "accepted post has no durable FNFD intent")

        source = self.processes.pop(0)
        source.kill()
        source.wait(timeout=30)
        source.stdout.close()
        source.stderr.close()

        self.start(b)
        self.start(a)
        source_article = self.await_article(a, message_id)
        target_article = self.await_article(b, message_id)
        self.assertEqual(target_article, source_article)
        duplicate = self.duplicate_offer(b, message_id)
        self.assertTrue(duplicate.startswith(b"435 "))
        identities = {node["name"]: self.verify_process_identity(node)
                      for node in (a, b)}
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "requeue-restart", "journal": True, "source_killed": True,
            "source_restarted": True, "target_identical": target_article == source_article,
            "duplicate": duplicate[:3].decode(), "identity": identities,
        }, sort_keys=True))

    def test_reset_while_transit_completes_keeps_durable_article_and_owner(self):
        source = self.initialize("reset-source", free_port())
        target = self.initialize("reset-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.start(target)

        message_id = "<native-reset-after-transit@example.invalid>"
        self.transfer_then_reset_before_reply(target, message_id, "reset-after-transit")
        self.assertEqual(self.await_article(target, message_id),
                         self.article(message_id, "reset-after-transit"))
        self.assertIsNone(target["process"].poll(),
                          "connection-local reply failure stopped the owner")
        self.assertIn(b"IHAVE", self.capabilities(target))

    def test_transit_into_a_node_with_a_path_identity_is_accepted_and_owner_stays(self):
        # transit-436: on 6c0626c5, with a Path identity set, every transit
        # was stored but answered 436 uncertain and stopped the service,
        # because the completion was compared with the received octets
        # rather than the Path-updated octets the owner stored.
        source = self.initialize("path-source", free_port())
        target = self.initialize("path-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.command([IMAGE, "--fn", "operator", target["config"], "policy",
                      "set", "path-identity", "path-target.example.invalid"])
        self.start(target)

        replies = {}
        message_id = "<native-path-identity-ihave@example.invalid>"
        offered = (b"Path: path-source.example.invalid!not-for-mail\r\n"
                   + self.article(message_id, "path-identity-ihave"))
        with socket.create_connection(("127.0.0.1", target["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + message_id.encode("ascii") + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"335 "))
            stream.write(offered + b".\r\n")
            replies["ihave"] = stream.readline()
            streamed = "<native-path-identity-takethis@example.invalid>"
            stream.write(b"TAKETHIS " + streamed.encode("ascii") + b"\r\n"
                         + b"Path: path-source.example.invalid!not-for-mail\r\n"
                         + self.article(streamed, "path-identity-takethis") + b".\r\n")
            replies["takethis"] = stream.readline()
        self.assertTrue(replies["ihave"].startswith(b"235 "), replies)
        self.assertTrue(replies["takethis"].startswith(b"239 "), replies)
        self.assertIsNone(target["process"].poll(),
                          "a durable transit stopped the owner for recovery")

        served = self.await_article(target, message_id)
        self.assertTrue(served.startswith(
            b"Path: path-target.example.invalid!"), served[:80])
        self.assertIn(b"path-source.example.invalid!not-for-mail", served)
        self.assertTrue(self.duplicate_offer(target, message_id).startswith(b"435 "))
        self.assertIsNone(target["process"].poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "path-identity-transit",
            "ihave": replies["ihave"][:3].decode(),
            "takethis": replies["takethis"][:3].decode(),
            "served_path": served.split(b"\r\n", 1)[0].decode("ascii", "replace"),
            "owner_alive": target["process"].poll() is None,
            "identity": self.verify_process_identity(target),
        }, sort_keys=True))

    # -------------------------------------------------------------------
    # Streaming (RFC 4644), PRF-207 / NNT-045 / SCN-138

    def test_inn_shaped_streaming_driver_gets_the_ihave_verdicts(self):
        """An INN-shaped peer streams into fn: MODE STREAM, then CHECKs
        pipelined before their TAKETHISes, as innfeed sends them.  Every
        streamed answer is the RFC 4644 image of the IHAVE answer for the
        same case (one decision, three wire forms), and the pipeline past
        the peer's max-inflight (16, `peer add`'s inbound bound) is 431."""
        source = self.initialize("stream-source", free_port())
        target = self.initialize("stream-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.start(target)

        def outscope(message_id, marker):
            return self.article(message_id, marker).replace(
                b"Newsgroups: fn.test", b"Newsgroups: alt.elsewhere")

        fresh = ["<stream-{}@example.invalid>".format(n) for n in range(20)]
        held = "<stream-held@example.invalid>"
        refused_ihave = "<stream-refused-ihave@example.invalid>"
        refused_takethis = "<stream-refused-takethis@example.invalid>"
        replies = {}
        with socket.create_connection(("127.0.0.1", target["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"MODE STREAM\r\n")
            replies["mode"] = stream.readline()
            # IHAVE first, on the same connection: the held article, and an
            # out-of-scope one the transfer decision refuses.
            stream.write(b"IHAVE " + held.encode() + b"\r\n")
            replies["ihave-offer"] = stream.readline()
            stream.write(self.article(held, "held") + b".\r\n")
            replies["ihave-transfer"] = stream.readline()
            stream.write(b"IHAVE " + held.encode() + b"\r\n")
            replies["ihave-duplicate"] = stream.readline()
            stream.write(b"IHAVE " + refused_ihave.encode() + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"335 "))
            stream.write(outscope(refused_ihave, "refused-ihave") + b".\r\n")
            replies["ihave-refused"] = stream.readline()
            # The pipeline: 20 fresh CHECKs and the held one, written at once.
            stream.write(b"".join(b"CHECK " + m.encode() + b"\r\n"
                                  for m in fresh + [held]))
            checks = [stream.readline() for _ in range(len(fresh) + 1)]
            # TAKETHIS for every 238, pipelined in one write as innfeed
            # sends them (PKT-600 repaired, PRF-213: each article is its own
            # step, committed and answered before the next is framed).
            wanted = [m for m, r in zip(fresh, checks) if r.startswith(b"238 ")]
            stream.write(b"".join(b"TAKETHIS " + m.encode() + b"\r\n"
                                  + self.article(m, m[1:-1]) + b".\r\n"
                                  for m in wanted))
            takes = [stream.readline() for _ in wanted]
            stream.write(b"TAKETHIS " + refused_takethis.encode() + b"\r\n"
                         + outscope(refused_takethis, "refused-takethis") + b".\r\n")
            replies["takethis-refused"] = stream.readline()
            # The deferred ones again, now that the promises are retired.
            deferred = [m for m, r in zip(fresh, checks) if r.startswith(b"431 ")]
            stream.write(b"".join(b"CHECK " + m.encode() + b"\r\n" for m in deferred))
            rechecks = [stream.readline() for _ in deferred]
            stream.write(b"".join(b"TAKETHIS " + m.encode() + b"\r\n"
                                  + self.article(m, m[1:-1]) + b".\r\n"
                                  for m in deferred))
            retakes = [stream.readline() for _ in deferred]
            # A TAKETHIS of an article already held: 439, and IHAVE says 435.
            stream.write(b"TAKETHIS " + fresh[0].encode() + b"\r\n"
                         + self.article(fresh[0], fresh[0][1:-1]) + b".\r\n")
            replies["takethis-duplicate"] = stream.readline()
            stream.write(b"CHECK " + fresh[0].encode() + b"\r\n")
            replies["check-duplicate"] = stream.readline()
            stream.write(b"QUIT\r\n")
            replies["quit"] = stream.readline()

        codes = {k: v[:3].decode() for k, v in replies.items()}
        self.assertEqual(codes["mode"], "203", replies)
        self.assertEqual((codes["ihave-offer"], codes["ihave-transfer"]), ("335", "235"), replies)
        self.assertEqual(codes["ihave-duplicate"], "435", replies)
        self.assertEqual(codes["ihave-refused"], "437", replies)
        check_codes = [c[:3].decode() for c in checks]
        # The bound: sixteen promises, then 431 (retry later), and the held
        # article 438 -- the images of 335, 436 and 435.
        self.assertEqual(check_codes[:16], ["238"] * 16, checks)
        self.assertEqual(check_codes[16:20], ["431"] * 4, checks)
        self.assertEqual(check_codes[20], "438", checks)
        for message_id, reply in zip(fresh, checks):
            self.assertTrue(reply.rstrip(b"\r\n").endswith(message_id.encode()), reply)
        self.assertEqual([t[:3] for t in takes], [b"239"] * 16, takes)
        for message_id, reply in zip(wanted, takes):
            self.assertTrue(reply.rstrip(b"\r\n").endswith(message_id.encode()), reply)
        self.assertEqual(codes["takethis-refused"], "439", replies)
        self.assertEqual([r[:3] for r in rechecks], [b"238"] * 4, rechecks)
        self.assertEqual([r[:3] for r in retakes], [b"239"] * 4, retakes)
        self.assertEqual(codes["takethis-duplicate"], "439", replies)
        self.assertEqual(codes["check-duplicate"], "438", replies)
        self.assertEqual(codes["quit"], "205", replies)
        for message_id in fresh:
            self.assertEqual(self.await_article(target, message_id),
                             self.article(message_id, message_id[1:-1]))
        self.assertIsNone(self.article_from(target, refused_takethis))
        self.assertIsNone(self.article_from(target, refused_ihave))
        self.assertIsNone(target["process"].poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "inn-shaped-streaming",
            "ihave": {"offer": codes["ihave-offer"], "transfer": codes["ihave-transfer"],
                      "duplicate": codes["ihave-duplicate"], "refused": codes["ihave-refused"]},
            "stream": {"mode": codes["mode"], "check": check_codes,
                       "takethis": [t[:3].decode() for t in takes],
                       "refused": codes["takethis-refused"],
                       "recheck": [r[:3].decode() for r in rechecks],
                       "retake": [r[:3].decode() for r in retakes],
                       "duplicate": codes["takethis-duplicate"],
                       "check_duplicate": codes["check-duplicate"]},
            "stored": len(fresh),
            "identity": self.verify_process_identity(target),
        }, sort_keys=True))

    def test_transit_hygiene_refused_offer_memory_and_relay_checks(self):
        """PRF-235 / PRF-236 (NNT-049, NNT-050, SCN-161, SCN-162), INN-shaped:
        three peers offer one article whose Path is malformed.  The first
        peer's CHECK draws 238 and its TAKETHIS 439 (the transfer decision
        parses it once); the refusal is remembered (books/owner.lisp
        fn-own-transit-refused), so the second and third peers' CHECK draw
        438 and IHAVE 435 with the remembered reason, and no transfer
        happens.  With `relay-date-skew 3600' and `relay-require-path 1' set
        by the operator, an article dated two hours ahead is refused 437
        "dated in the future" and a Path-less one 437 "no Path"; an article
        within the skew and with a Path is accepted 235.  Nothing is
        persisted: the memory is the owner's, in memory only."""
        target = self.initialize("hygiene-target", free_port())
        sources = [("hyg1", "127.0.0.1"), ("hyg2", "127.0.0.2"), ("hyg3", "127.0.0.3")]
        for name, address in sources:
            self.command([IMAGE, "--fn", "operator", target["config"], "peer", "add",
                          name, "{}.example.invalid".format(name), address, "9",
                          "fn.*", "-", address, "true"])
        self.command([IMAGE, "--fn", "operator", target["config"], "policy", "set",
                      "relay-date-skew", "3600"])
        self.command([IMAGE, "--fn", "operator", target["config"], "policy", "set",
                      "relay-require-path", "1"])
        self.start(target)

        def hygienic(message_id, path, date):
            head = b"" if path is None else b"Path: " + path + b"\r\n"
            return (head + b"From: sender@example.invalid\r\n"
                    b"Newsgroups: fn.test\r\nSubject: hygiene\r\n"
                    b"Date: " + date + b"\r\nMessage-ID: " + message_id.encode()
                    + b"\r\n\r\nbody\r\n")

        def rfc5322(offset):
            return time.strftime("%a, %d %b %Y %H:%M:%S +0000",
                                 time.gmtime(time.time() + offset)).encode()

        def session(address):
            client = socket.create_connection(("127.0.0.1", target["port"]), timeout=15,
                                              source_address=(address, 0))
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            return client, stream

        def ask(stream, line):
            stream.write(line + b"\r\n")
            return stream.readline()

        bad = "<hygiene-bad-path@example.invalid>"
        bad_article = hygienic(bad, b"inn hbox!not-for-mail", rfc5322(-60))
        witness = {"kind": "transit-hygiene"}
        client, stream = session("127.0.0.1")
        with client:
            witness["peer1-check"] = ask(stream, b"CHECK " + bad.encode()).decode()
            stream.write(b"TAKETHIS " + bad.encode() + b"\r\n" + bad_article + b".\r\n")
            witness["peer1-takethis"] = stream.readline().decode()
            ask(stream, b"QUIT")
        for name, address in sources[1:]:
            client, stream = session(address)
            with client:
                witness[name + "-check"] = ask(stream, b"CHECK " + bad.encode()).decode()
                witness[name + "-ihave"] = ask(stream, b"IHAVE " + bad.encode()).decode()
                ask(stream, b"QUIT")

        future = "<hygiene-future@example.invalid>"
        pathless = "<hygiene-no-path@example.invalid>"
        good = "<hygiene-good@example.invalid>"
        client, stream = session("127.0.0.2")
        with client:
            for key, message_id, article in (
                    ("future", future, hygienic(future, b"hyg2.example.invalid!not-for-mail",
                                                rfc5322(7200))),
                    ("no-path", pathless, hygienic(pathless, None, rfc5322(-60))),
                    ("good", good, hygienic(good, b"hyg2.example.invalid!not-for-mail",
                                            rfc5322(1800)))):
                witness[key + "-offer"] = ask(stream, b"IHAVE " + message_id.encode()).decode()
                stream.write(article + b".\r\n")
                witness[key + "-transfer"] = stream.readline().decode()
            ask(stream, b"QUIT")
        print("NATIVE-PEERING-WITNESS " + json.dumps(witness, sort_keys=True))

        self.assertTrue(witness["peer1-check"].startswith("238 "), witness)
        self.assertTrue(witness["peer1-takethis"].startswith("439 "), witness)
        for name, _ in sources[1:]:
            self.assertTrue(witness[name + "-check"].startswith("438 "), witness)
            self.assertEqual(witness[name + "-ihave"],
                             "435 not wanted; malformed Path\r\n", witness)
        self.assertTrue(witness["future-offer"].startswith("335 "), witness)
        self.assertEqual(witness["future-transfer"],
                         "437 transfer rejected; dated in the future\r\n", witness)
        self.assertTrue(witness["no-path-offer"].startswith("335 "), witness)
        self.assertEqual(witness["no-path-transfer"],
                         "437 transfer rejected; no Path\r\n", witness)
        self.assertTrue(witness["good-offer"].startswith("335 "), witness)
        self.assertTrue(witness["good-transfer"].startswith("235 "), witness)
        self.assertIsNone(target["process"].poll())

    def test_pipelined_takethis_in_one_read_answers_every_article(self):
        """PKT-600, repaired (PRF-213, NNT-044, SCN-144): eight TAKETHIS
        articles in one write, as innfeed pipelines them.  The served read
        yields after each article's submission
        (books/served-tls-prefix.lisp fn-served-feed-counted, the span fold
        books/served-span.lisp fn-scar-feed-span), the owner commits and
        answers it, and host/native/owner.lisp feeds the rest of the read
        back; every article is answered 239 in order and stored.  Until the
        repair the second of two articles in one read was never admitted
        and never answered, and this case was an expected failure."""
        source = self.initialize("pipe-source", free_port())
        target = self.initialize("pipe-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.start(target)
        ids = ["<pipe-{}@example.invalid>".format(n) for n in range(8)]
        with socket.create_connection(("127.0.0.1", target["port"]), timeout=15) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"".join(b"TAKETHIS " + m.encode() + b"\r\n"
                                  + self.article(m, m[1:-1]) + b".\r\n"
                                  for m in ids))
            replies = []
            for _ in ids:
                try:
                    replies.append(stream.readline())
                except socket.timeout:
                    replies.append(b"")
            stream.write(b"QUIT\r\n")
            quit_reply = stream.readline()
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "pipelined-takethis-pkt-600",
            "replies": [r.decode("ascii", "replace") for r in replies],
            "quit": quit_reply.decode("ascii", "replace")}))
        self.assertEqual([r[:3] for r in replies], [b"239"] * len(ids), replies)
        for message_id, reply in zip(ids, replies):
            self.assertTrue(reply.rstrip(b"\r\n").endswith(message_id.encode()), reply)
        self.assertTrue(quit_reply.startswith(b"205 "), quit_reply)
        for message_id in ids:
            self.assertEqual(self.await_article(target, message_id),
                             self.article(message_id, message_id[1:-1]))
        self.assertIsNone(target["process"].poll())

    def test_fragmented_takethis_without_check_answers_every_article(self):
        """PKT-600 under fragmentation (PRF-213, SCN-144; the gpt-6 review of
        2026-09-26, section 6): four TAKETHIS with no CHECK before them (RFC
        4644 section 2.5 permits that), written as many small segments with
        TCP_NODELAY, the cuts falling inside command lines, bodies and every
        `.CRLF' terminator (between `.' and CR and between CR and LF).  Every
        article is answered 239 in order and stored, as in one write
        (fn-served-drain-run-is-boundary-independent)."""
        source = self.initialize("frag-source", free_port())
        target = self.initialize("frag-target", free_port())
        self.configure_peer(target, source, outbound="-")
        self.start(target)
        ids = ["<frag-{}@example.invalid>".format(n) for n in range(4)]
        blocks = [b"TAKETHIS " + m.encode() + b"\r\n" + self.article(m, m[1:-1]) + b".\r\n"
                  for m in ids]
        data = b"".join(blocks)
        cuts = set(range(5, len(data), 7))
        end = 0
        for block in blocks:
            end += len(block)
            cuts.update({end - 2, end - 1})
        pieces, start = [], 0
        for cut in sorted(cuts):
            pieces.append(data[start:cut])
            start = cut
        pieces.append(data[start:])
        with socket.create_connection(("127.0.0.1", target["port"]), timeout=15) as client:
            client.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            for piece in pieces:
                client.sendall(piece)
                time.sleep(0.002)
            replies = [stream.readline() for _ in ids]
            stream.write(b"QUIT\r\n")
            quit_reply = stream.readline()
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "fragmented-takethis-pkt-600", "segments": len(pieces),
            "replies": [r.decode("ascii", "replace") for r in replies]}))
        self.assertEqual([r[:3] for r in replies], [b"239"] * len(ids), replies)
        for message_id, reply in zip(ids, replies):
            self.assertTrue(reply.rstrip(b"\r\n").endswith(message_id.encode()), reply)
        self.assertTrue(quit_reply.startswith(b"205 "), quit_reply)
        for message_id in ids:
            self.assertEqual(self.await_article(target, message_id),
                             self.article(message_id, message_id[1:-1]))
        self.assertIsNone(target["process"].poll())

    def test_pipelined_post_in_one_read_answers_every_article(self):
        """PKT-600 for POST (PRF-213, NNT-044, SCN-144): two POST blocks in
        one write, and then an article followed by the next command in one
        write.  Each article is its own step: the reply stream is 340 240
        340 240 in order, the 340 for the next POST never precedes the 240
        for the article before it, and every article is stored."""
        node = self.initialize("pipe-post", free_port())
        self.start(node)
        ids = ["<pipe-post-{}@example.invalid>".format(n) for n in range(4)]
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=15) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            # Two whole POST blocks in one write.
            stream.write(b"".join(b"POST\r\n" + self.article(m, m[1:-1]) + b".\r\n"
                                  for m in ids[:2]))
            greedy = [stream.readline() for _ in range(4)]
            # RFC 3977 section 3.5's pipelined shape: after the 340, the
            # article and the next POST in one write, then the last article
            # and QUIT in one write.
            stream.write(b"POST\r\n")
            offer = stream.readline()
            stream.write(self.article(ids[2], ids[2][1:-1]) + b".\r\nPOST\r\n")
            pipelined = [stream.readline() for _ in range(2)]
            stream.write(self.article(ids[3], ids[3][1:-1]) + b".\r\nQUIT\r\n")
            last = [stream.readline() for _ in range(2)]
        codes = [r[:3] for r in greedy + [offer] + pipelined + last]
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "pipelined-post-pkt-600",
            "codes": [c.decode("ascii", "replace") for c in codes]}))
        self.assertEqual(codes, [b"340", b"240", b"340", b"240",
                                 b"340", b"240", b"340", b"240", b"205"],
                         greedy + [offer] + pipelined + last)
        for message_id in ids:
            got = self.await_article(node, message_id)
            self.assertIsNotNone(got, message_id)
            self.assertIn(("Message-ID: " + message_id).encode("ascii"), got)
        self.assertIsNone(node["process"].poll())

    def feed_to_scripted_peer(self, mode_reply, marker):
        peer = ScriptedTransitPeer(mode_reply)
        self.addCleanup(peer.close)
        source = self.initialize(marker + "-source", free_port())
        target = {"name": marker + "-peer", "port": peer.port}
        self.configure_peer(source, target)
        self.start(source)
        message_id = "<{}@example.invalid>".format(marker)
        self.post(source, message_id, marker)
        served = self.await_article(source, message_id)
        got = peer.await_article(message_id)
        self.assertIsNotNone(got, "the scripted peer never received the article; "
                             "commands={}".format(peer.commands))
        return peer, source, message_id, served, got

    def test_feed_to_a_peer_without_streaming_falls_back_to_ihave(self):
        """PRF-207: a peer that answers MODE STREAM with 501 (RFC 3977
        section 3.2.1) is fed with IHAVE on the SAME connection; no CHECK or
        TAKETHIS is ever sent to it, and the owner keeps dialling it."""
        peer, source, message_id, served, got = self.feed_to_scripted_peer(
            "501 unknown MODE variant", "fallback")
        form, article = got
        self.assertEqual(form, "IHAVE")
        self.assertEqual(article, served)
        with peer.lock:
            commands = list(peer.commands)
        verbs = [(n, c.split()[0].upper()) for n, c in commands]
        mode_conn = [n for n, v in verbs if v == "MODE"][0]
        ihave_conn = [n for n, c in commands if c == "IHAVE " + message_id][0]
        self.assertEqual(mode_conn, ihave_conn, commands)
        self.assertNotIn("CHECK", [v for _, v in verbs], commands)
        self.assertNotIn("TAKETHIS", [v for _, v in verbs], commands)
        # A second article reaches the same peer: the dial was not stopped.
        second = "<fallback-2@example.invalid>"
        self.post(source, second, "fallback-2")
        again = peer.await_article(second)
        self.assertIsNotNone(again, commands)
        self.assertEqual(again[0], "IHAVE")
        self.assertIsNone(source["process"].poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "mode-stream-501-ihave-fallback",
            "commands": commands, "identical": article == served,
            "second": again[0], "identity": self.verify_process_identity(source),
        }, sort_keys=True))

    def test_feed_to_a_streaming_peer_uses_check_and_takethis(self):
        """A peer that answers 203 is fed with CHECK then TAKETHIS (RFC 4644
        sections 2.4, 2.5), never IHAVE."""
        peer, source, message_id, served, got = self.feed_to_scripted_peer(
            "203 streaming permitted", "streamed")
        form, article = got
        self.assertEqual(form, "TAKETHIS")
        self.assertEqual(article, served)
        with peer.lock:
            commands = list(peer.commands)
        verbs = [c.split()[0].upper() for _, c in commands]
        self.assertIn("CHECK", verbs, commands)
        self.assertNotIn("IHAVE", verbs, commands)
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "mode-stream-203-streaming", "commands": commands,
            "identical": article == served,
            "identity": self.verify_process_identity(source),
        }, sort_keys=True))

    def test_feed_distribution_filter(self):
        """PRF-237 / SCN-163 (RFC 5537 section 3.6 paragraph 2): with `peer
        distributions NAME fn`, an article whose Distribution is world is not
        fed to that peer; one whose Distribution is fn, and one with no
        Distribution, are."""
        peer = ScriptedTransitPeer("203 streaming permitted")
        self.addCleanup(peer.close)
        source = self.initialize("dist-source", free_port())
        target = {"name": "dist-peer", "port": peer.port}
        self.configure_peer(source, target)
        self.command([IMAGE, "--fn", "operator", source["config"], "peer",
                      "distributions", target["name"], "fn"])
        self.start(source)
        cases = [("world", "Distribution: world\r\n"),
                 ("fn", "Distribution: FN\r\n"),
                 ("none", "")]
        ids = {}
        for marker, header in cases:
            message_id = "<dist-{}@example.invalid>".format(marker)
            ids[marker] = message_id
            payload = source["root"] / ("dist-" + marker + ".article")
            payload.write_bytes((
                "From: sender@example.invalid\r\n"
                "Newsgroups: fn.test\r\n"
                "Subject: distribution {}\r\n"
                "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                "{}"
                "Message-ID: {}\r\n\r\n{}\r\n").format(
                    marker, header, message_id, marker).encode("ascii"))
            self.command([IMAGE, "--fn", "operator", source["config"], "post",
                          "--message-id", message_id, "--payload", payload,
                          "--group", "fn.test"])
        for marker in ("world", "fn", "none"):
            self.assertIsNotNone(self.await_article(source, ids[marker]), marker)
        for marker in ("fn", "none"):
            got = peer.await_article(ids[marker])
            self.assertIsNotNone(got, "{} never reached the peer; commands={}".format(
                marker, peer.commands))
        with peer.lock:
            commands = list(peer.commands)
            received = sorted(peer.articles)
        self.assertNotIn(ids["world"], received, commands)
        self.assertFalse([c for _, c in commands if ids["world"] in c], commands)
        self.assertIsNone(source["process"].poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "feed-distribution-filter-prf-237",
            "commands": commands, "received": received,
            "identity": self.verify_process_identity(source),
        }, sort_keys=True))
