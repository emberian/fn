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
import threading
import time
import types
import unittest

from tests.native_harness import EXIT_OK, Client, Node, free_port, native_image, scratch
from tools.wire_stream import whole_stream


# The image must be named explicitly: the case pins its launcher and core.
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = native_image("FN_NATIVE_HOST") if IMAGE_TEXT else None
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


class ScriptedTransitPeer:
    """A minimal INN-shaped transit server for fn's outbound feed.

    It greets with 200, answers MODE STREAM with MODE_REPLY (203 streams;
    501 is what a server without RFC 4644 answers, RFC 3977 section 3.2.1),
    and then takes IHAVE (335 / 235) or CHECK / TAKETHIS (238 / 239) the way
    INN's innd does.  Every command line it reads is recorded with its
    connection number, so a test can say which form carried each article.
    """

    def __init__(self, mode_reply, accept_gate=None):
        self.mode_reply = mode_reply
        self.accept_gate = accept_gate
        self.accepted = set()
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
        if self.accept_gate is not None:
            self.accept_gate.set()
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
            stream = whole_stream(client)
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
                    if self.accept_gate is not None and not self.accept_gate.wait(60):
                        return
                    stream.write(b"235 article transferred OK\r\n")
                    with self.lock:
                        self.accepted.add(words[1])
                elif verb == "CHECK":
                    stream.write(b"238 " + words[1].encode("ascii") + b"\r\n")
                elif verb == "TAKETHIS":
                    article = self.read_article(stream)
                    with self.lock:
                        self.articles[words[1]] = ("TAKETHIS", article)
                    if self.accept_gate is not None and not self.accept_gate.wait(60):
                        return
                    stream.write(b"239 " + words[1].encode("ascii") + b"\r\n")
                    with self.lock:
                        self.accepted.add(words[1])
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
        self.base = scratch(self, "fn-native-peering-")

    def initialize(self, name, *init):
        """A node NAME under the test's tree, its store made by `store init`
        (INIT, default the one group fn.test); every node it starts is
        stopped at cleanup."""
        node = Node(self, IMAGE, root=self.base / name, name=name)
        node.store("init", *(init or ("fn.test",)), expect=EXIT_OK)
        return node

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
        found = self.process_identity(node.process)
        if found["status"] != "observed":
            self.skipTest("cannot observe native runtime/core: {}".format(found["reason"]))
        self.assertEqual(found["runtime_sha256"], RUNTIME_SHA256, found)
        self.assertEqual(found["core_sha256"], CORE_SHA256, found)
        node.identities = getattr(node, "identities", []) + [found]
        return found

    def configure_peer(self, source, target, outbound="fn.*"):
        source.operator("peer", "add", target.name,
                        "{}.example.invalid".format(target.name), "127.0.0.1",
                        str(target.port), "fn.*", outbound, "127.0.0.1", "true",
                        expect=EXIT_OK)

    def start(self, node):
        node.start()
        self.verify_process_identity(node)

    @staticmethod
    def article(message_id, marker):
        return ("From: sender@example.invalid\r\n"
                "Newsgroups: fn.test\r\n"
                "Subject: native two-node {}\r\n"
                "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                "Message-ID: {}\r\n\r\n{}\r\n".format(
                    marker, message_id, marker)).encode("ascii")

    def post(self, node, message_id, marker):
        node.post(message_id, self.article(message_id, marker), expect=EXIT_OK)

    def article_from(self, node, message_id):
        try:
            client = Client(node.port, timeout=10, greeting=(b"200",))
        except ConnectionRefusedError:
            process = node.process
            if process is not None and process.poll() is not None:
                self.fail("{} exited while awaiting article: {}".format(
                    node.name, process.stderr.tail().decode("utf-8", "replace")))
            return None
        except (AssertionError, EOFError):
            return None
        with client:
            try:
                served = client.article(message_id)
            except EOFError:
                return None
        return None if served is None else self.stored_octets(served)

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
        self.fail("{} did not receive {}".format(node.name, message_id))

    def duplicate_offer(self, node, message_id):
        with Client(node.port, timeout=10, greeting=(b"200",)) as client:
            return client.command(b"IHAVE " + message_id.encode("ascii"))

    def transfer_then_reset_before_reply(self, node, message_id, marker):
        client = socket.create_connection(("127.0.0.1", node.port), timeout=10)
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
        for line in source.splitlines(keepends=True):
            self.assertTrue(line.endswith(b"\r\n"))
        with Client(node.port, timeout=10, greeting=(b"200",)) as client:
            offer, reply = client.post(source, verb=b"IHAVE " + message_id.encode("ascii"))
        self.assertTrue(offer.startswith(b"335 "), offer)
        self.assertTrue(reply.startswith(b"235 "), reply)

    def capabilities(self, node):
        client = Client(node.port, timeout=10, greeting=(b"200",))
        try:
            status, body = client.multiline(b"CAPABILITIES")
            self.assertTrue(status.startswith(b"101 "), status)
            # Keep this on one connection: it detects a worker that returns
            # after every successful read instead of only after QUIT/close.
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
        finally:
            client.close(quit=False)
        return [line for line in body.split(b"\r\n") if line]

    def test_public_native_nodes_exchange_both_ways_and_suppress_duplicate(self):
        self.exchange_both_ways(live_configuration=False)

    def test_live_peer_configuration_activates_both_directions(self):
        self.exchange_both_ways(live_configuration=True)

    def exchange_both_ways(self, live_configuration):
        a = self.initialize("a")
        b = self.initialize("b")
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
        identities = {node.name: self.verify_process_identity(node)
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
        a = self.initialize("restart-a")
        b = self.initialize("restart-b")
        self.configure_peer(a, b)
        # B starts after A is killed, but its peer record must exist before
        # that listener accepts A's loopback feed connection; otherwise it is
        # a reader connection and IHAVE is correctly refused as unauthorized.
        self.configure_peer(b, a, outbound="-")
        self.start(a)

        message_id = "<native-requeue-after-kill@example.invalid>"
        self.post(a, message_id, "requeue-after-kill")
        journal = a.store_path / "feed" / "restart-b.fnfd"
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline and not journal.is_file():
            time.sleep(0.05)
        self.assertTrue(journal.is_file(), "accepted post has no durable FNFD intent")

        source = a.process
        source.kill()
        source.wait(timeout=30)
        source.finish()

        self.start(b)
        self.start(a)
        source_article = self.await_article(a, message_id)
        target_article = self.await_article(b, message_id)
        self.assertEqual(target_article, source_article)
        duplicate = self.duplicate_offer(b, message_id)
        self.assertTrue(duplicate.startswith(b"435 "))
        identities = {node.name: self.verify_process_identity(node)
                      for node in (a, b)}
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "requeue-restart", "journal": True, "source_killed": True,
            "source_restarted": True, "target_identical": target_article == source_article,
            "duplicate": duplicate[:3].decode(), "identity": identities,
        }, sort_keys=True))

    def test_receiver_killed_mid_ihave_keeps_what_it_acknowledged(self):
        """tools/twonode_gate.py's three questions on two native owners (the
        gate drove the Python host and retired with it, python-diet T5).
        The rest of its feed question is owned elsewhere: IHAVE 335/235 and
        the 435 duplicate by exchange_both_ways and the streaming driver
        above, the Path loop (437 after 335) by tools/inn_lab.py against a
        real INN.
        independent: X posted on A and Y on B; each answers only its own.
        feed: X offered to B by IHAVE, acknowledged 235.
        kill: B SIGKILLed after 335 with half of Z sent; restarted, B still
        serves X and Y octet for octet, Z is absent and takes a fresh 335/235
        (the interrupted transfer left nothing), and A never stopped.
        The v0 matrix's rows V0-CRASH-KILL, V0-CRASH-SURVIVOR, V0-CRASH-RECOVER,
        V0-CRASH-ACKNOWLEDGED, V0-CRASH-INTERRUPTED and V0-CRASH-RESTART are
        this case (tools/v0_matrix.py retired with it, python-diet T2b)."""
        a = self.initialize("kill-a")
        b = self.initialize("kill-b")
        self.configure_peer(b, a, outbound="-")
        self.start(a)
        self.start(b)
        x, y, z = ("<twonode-{}@example.invalid>".format(n) for n in "xyz")
        self.post(a, x, "x")
        self.post(b, y, "y")
        x_on_a, y_on_b = self.await_article(a, x), self.await_article(b, y)
        self.assertIsNone(self.article_from(b, x))
        self.assertIsNone(self.article_from(a, y))

        self.transit(b, x, x_on_a)
        self.assertEqual(self.await_article(b, x), x_on_a)

        source = self.article(z, "interrupted")
        with socket.create_connection(("127.0.0.1", b.port), timeout=30) as client:
            stream = whole_stream(client)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"IHAVE " + z.encode("ascii") + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"335 "))
            stream.write(source[:len(source) // 2])
            receiver = b.process
            receiver.kill()
            receiver.wait(timeout=30)
            receiver.finish()

        self.start(b)
        self.assertEqual(self.await_article(b, x), x_on_a)
        self.assertEqual(self.await_article(b, y), y_on_b)
        self.assertIsNone(self.article_from(b, z))
        self.assertIsNone(a.process.poll(), "A stopped while B died")
        self.assertEqual(self.await_article(a, x), x_on_a)
        self.transit(b, z, source)
        self.assertEqual(self.await_article(b, z), source)

    def test_reset_while_transit_completes_keeps_durable_article_and_owner(self):
        source = self.initialize("reset-source")
        target = self.initialize("reset-target")
        self.configure_peer(target, source, outbound="-")
        self.start(target)

        message_id = "<native-reset-after-transit@example.invalid>"
        self.transfer_then_reset_before_reply(target, message_id, "reset-after-transit")
        self.assertEqual(self.await_article(target, message_id),
                         self.article(message_id, "reset-after-transit"))
        self.assertIsNone(target.process.poll(),
                          "connection-local reply failure stopped the owner")
        self.assertIn(b"IHAVE", self.capabilities(target))

    def test_transit_into_a_node_with_a_path_identity_is_accepted_and_owner_stays(self):
        # transit-436: on 6c0626c5, with a Path identity set, every transit
        # was stored but answered 436 uncertain and stopped the service,
        # because the completion was compared with the received octets
        # rather than the Path-updated octets the owner stored.
        source = self.initialize("path-source")
        target = self.initialize("path-target")
        self.configure_peer(target, source, outbound="-")
        target.operator("policy", "set", "path-identity", "path-target.example.invalid",
                        expect=EXIT_OK)
        self.start(target)

        replies = {}
        message_id = "<native-path-identity-ihave@example.invalid>"
        offered = (b"Path: path-source.example.invalid!not-for-mail\r\n"
                   + self.article(message_id, "path-identity-ihave"))
        with socket.create_connection(("127.0.0.1", target.port), timeout=30) as client:
            stream = whole_stream(client)
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
        self.assertIsNone(target.process.poll(),
                          "a durable transit stopped the owner for recovery")

        served = self.await_article(target, message_id)
        self.assertTrue(served.startswith(
            b"Path: path-target.example.invalid!"), served[:80])
        self.assertIn(b"path-source.example.invalid!not-for-mail", served)
        self.assertTrue(self.duplicate_offer(target, message_id).startswith(b"435 "))
        self.assertIsNone(target.process.poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "path-identity-transit",
            "ihave": replies["ihave"][:3].decode(),
            "takethis": replies["takethis"][:3].decode(),
            "served_path": served.split(b"\r\n", 1)[0].decode("ascii", "replace"),
            "owner_alive": target.process.poll() is None,
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
        source = self.initialize("stream-source")
        target = self.initialize("stream-target")
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
        with socket.create_connection(("127.0.0.1", target.port), timeout=30) as client:
            stream = whole_stream(client)
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
        self.assertIsNone(target.process.poll())
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
        target = self.initialize("hygiene-target")
        sources = [("hyg1", "127.0.0.1"), ("hyg2", "127.0.0.2"), ("hyg3", "127.0.0.3")]
        for name, address in sources:
            target.operator("peer", "add", name, "{}.example.invalid".format(name),
                            address, "9", "fn.*", "-", address, "true", expect=EXIT_OK)
        target.operator("policy", "set", "relay-date-skew", "3600", expect=EXIT_OK)
        target.operator("policy", "set", "relay-require-path", "1", expect=EXIT_OK)
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
            client = socket.create_connection(("127.0.0.1", target.port), timeout=15,
                                              source_address=(address, 0))
            stream = whole_stream(client)
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
        self.assertIsNone(target.process.poll())

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
        source = self.initialize("pipe-source")
        target = self.initialize("pipe-target")
        self.configure_peer(target, source, outbound="-")
        self.start(target)
        ids = ["<pipe-{}@example.invalid>".format(n) for n in range(8)]
        with socket.create_connection(("127.0.0.1", target.port), timeout=15) as client:
            stream = whole_stream(client)
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
        self.assertIsNone(target.process.poll())

    def test_a_full_store_defers_transit_and_the_sender_is_not_healthy(self):
        """PKT-711 (the stranger rehearsal, 2026-09-27): a receiver whose
        Store is full answered TAKETHIS 439 (drop) with `reason=none', and
        the sender forgot the article and stayed healthy.  Now a full Store
        answers 436 (retry; books/peer-inbound.lisp
        fn-peer-full-store-is-a-retry-code), its log names
        reason=unaffordable, and a sender whose peer defers holds
        unavailable-peer (books/native-health.lisp
        fn-nh-deferring-peer-is-held)."""
        source = self.initialize("full-source")
        full = self.initialize("full-target", "--max-transactions", "12", "fn.test")
        port = full.port
        self.configure_peer(full, source, outbound="-")
        self.start(full)
        ids = ["<full-{}@example.invalid>".format(n) for n in range(16)]
        replies = []
        with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
            stream = whole_stream(client)
            self.assertTrue(stream.readline().startswith(b"200 "))
            for message_id in ids:
                stream.write(b"TAKETHIS " + message_id.encode() + b"\r\n"
                             + self.article(message_id, message_id[1:-1]) + b".\r\n")
                replies.append(stream.readline())
            stream.write(b"QUIT\r\n")
        codes = [r[:3] for r in replies]
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "full-store-defers-pkt-711",
            "replies": [r.decode("ascii", "replace") for r in replies]}))
        self.assertIn(b"239", codes, replies)
        self.assertIn(b"436", codes, replies)
        self.assertNotIn(b"439", codes, replies)
        first = codes.index(b"436")
        self.assertEqual(set(codes[first:]), {b"436"}, replies)
        # The sender: a peer that defers is not healthy.
        self.configure_peer(source, full)
        self.start(source)
        self.post(source, "<full-sent@example.invalid>", "full-sent")
        deadline = time.monotonic() + 90
        health = None
        while time.monotonic() < deadline:
            health = source.operator("health", timeout=60)
            if b"unavailable-peer held" in health.stdout:
                break
            time.sleep(1)
        self.assertIsNotNone(health)
        self.assertIn(b"unavailable-peer held deferred=", health.stdout, health.stdout)
        self.assertNotEqual(health.returncode, 0, health.stdout)
        # The receiver's log names why it deferred.
        full.process.terminate()
        _, log = full.process.communicate(timeout=60)
        self.assertIn(b"reason=unaffordable", log, log[-2000:])

    def test_fragmented_takethis_without_check_answers_every_article(self):
        """PKT-600 under fragmentation (PRF-213, SCN-144; the gpt-6 review of
        2026-09-26, section 6): four TAKETHIS with no CHECK before them (RFC
        4644 section 2.5 permits that), written as many small segments with
        TCP_NODELAY, the cuts falling inside command lines, bodies and every
        `.CRLF' terminator (between `.' and CR and between CR and LF).  Every
        article is answered 239 in order and stored, as in one write
        (fn-served-drain-run-is-boundary-independent)."""
        source = self.initialize("frag-source")
        target = self.initialize("frag-target")
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
        with socket.create_connection(("127.0.0.1", target.port), timeout=15) as client:
            client.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            stream = whole_stream(client)
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
        self.assertIsNone(target.process.poll())

    def test_pipelined_post_in_one_read_answers_every_article(self):
        """PKT-600 for POST (PRF-213, NNT-044, SCN-144): two POST blocks in
        one write, and then an article followed by the next command in one
        write.  Each article is its own step: the reply stream is 340 240
        340 240 in order, the 340 for the next POST never precedes the 240
        for the article before it, and every article is stored."""
        node = self.initialize("pipe-post")
        self.start(node)
        ids = ["<pipe-post-{}@example.invalid>".format(n) for n in range(4)]
        with socket.create_connection(("127.0.0.1", node.port), timeout=15) as client:
            stream = whole_stream(client)
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
        self.assertIsNone(node.process.poll())

    def feed_to_scripted_peer(self, mode_reply, marker):
        peer = ScriptedTransitPeer(mode_reply)
        self.addCleanup(peer.close)
        source = self.initialize(marker + "-source")
        target = types.SimpleNamespace(name=marker + "-peer", port=peer.port)
        self.configure_peer(source, target)
        self.start(source)
        message_id = "<{}@example.invalid>".format(marker)
        self.post(source, message_id, marker)
        served = self.await_article(source, message_id)
        got = peer.await_article(message_id)
        self.assertIsNotNone(got, "the scripted peer never received the article; "
                             "commands={}".format(peer.commands))
        return peer, source, message_id, served, got

    def test_productive_local_transfer_precedes_remote_acceptance(self):
        """PRF-1062: actual article bytes arrive while 239 is withheld.

        This witnesses local handoff only.  The test peer is scripted, and
        sending its 239 is explicitly independent of the bytes it observed.
        """
        gate = threading.Event()
        peer = ScriptedTransitPeer("203 streaming permitted", accept_gate=gate)
        self.addCleanup(peer.close)
        source = self.initialize("productive-source")
        target = types.SimpleNamespace(name="productive-peer", port=peer.port)
        self.configure_peer(source, target)
        self.start(source)
        message_id = "<productive-transfer@example.invalid>"
        marker = ".productive-transfer"
        self.post(source, message_id, marker)
        served = self.await_article(source, message_id)
        got = peer.await_article(message_id)
        self.assertIsNotNone(got, peer.commands)
        self.assertEqual(got, ("TAKETHIS", served))
        self.assertIn(b"\r\n.productive-transfer\r\n", got[1])
        with peer.lock:
            commands = list(peer.commands)
            self.assertNotIn(message_id, peer.accepted)
        self.assertIn("CHECK " + message_id, [line for _, line in commands])
        self.assertIn("TAKETHIS " + message_id, [line for _, line in commands])
        journal = source.store_path / "feed" / "productive-peer.fnfd"
        self.assertTrue(journal.is_file())
        self.assertGreater(journal.stat().st_size, 0)
        self.assertIsNone(source.process.poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "productive-local-transfer-before-remote-acceptance",
            "commands": commands, "identical": got[1] == served,
            "remote_acceptance_withheld": True, "journal_present": True,
            "journal_bytes": journal.stat().st_size,
            "identity": self.verify_process_identity(source),
        }, sort_keys=True))
        gate.set()

    def test_productive_reader_answers_number_and_message_id(self):
        """Recovered native ARTICLE reads preserve a selected reader's view.

        The persisted article is written before the owner starts, so the
        first retrieval traverses recovery's extent-backed representation.
        This is successful native I/O evidence, not a disk honesty proof.
        """
        source = self.initialize("productive-reader")
        message_id = "<productive-read@example.invalid>"
        self.post(source, message_id, ".productive-read")
        self.start(source)
        with Client(source.port, timeout=60, greeting=(b"200",)) as client:
            selected = client.command("GROUP fn.test")
            self.assertTrue(selected.startswith(b"211 1 1 1 fn.test"), selected)
            number_status, numbered = client.multiline("ARTICLE 1")
            self.assertTrue(number_status.startswith(b"220 1 " + message_id.encode()),
                            number_status)
            id_status, identified = client.multiline("ARTICLE " + message_id)
            self.assertTrue(id_status.startswith(b"220 1 " + message_id.encode()), id_status)
            self.assertEqual(numbered, identified)
            self.assertIn(b"Message-ID: " + message_id.encode() + b"\r\n", numbered)
            self.assertIn(b"\r\n.productive-read\r\n", numbered)
            self.assertTrue(client.command("ARTICLE 2").startswith(b"423"))
            self.assertTrue(client.command("ARTICLE <missing-productive@example.invalid>").startswith(b"430"))
            stat = client.command("STAT")
            self.assertTrue(stat.startswith(b"223 1 " + message_id.encode()), stat)
            # A second locally accepted article does not change this pin;
            # selecting the group again is the explicit view advance.
            self.post(source, "<productive-later@example.invalid>", "later")
            self.assertTrue(client.command("ARTICLE 2").startswith(b"423"))
            advanced = client.command("GROUP fn.test")
            self.assertTrue(advanced.startswith(b"211 2 1 2 fn.test"), advanced)
            self.assertTrue(client.command("STAT 2").startswith(
                b"223 2 <productive-later@example.invalid>"))
        self.assertIsNone(source.process.poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "productive-reader-number-message-id-and-pinned-view",
            "number_status": number_status.decode("ascii").rstrip(),
            "message_id_status": id_status.decode("ascii").rstrip(),
            "identical": numbered == identified,
            "article_sha256": hashlib.sha256(numbered).hexdigest(),
            "old_pin_absent_423": True, "explicit_group_advance": True,
            "identity": self.verify_process_identity(source),
        }, sort_keys=True))

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
        self.assertIsNone(source.process.poll())
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
        source = self.initialize("dist-source")
        target = types.SimpleNamespace(name="dist-peer", port=peer.port)
        self.configure_peer(source, target)
        source.operator("peer", "distributions", target.name, "fn", expect=EXIT_OK)
        self.start(source)
        cases = [("world", "Distribution: world\r\n"),
                 ("fn", "Distribution: FN\r\n"),
                 ("none", "")]
        ids = {}
        for marker, header in cases:
            message_id = "<dist-{}@example.invalid>".format(marker)
            ids[marker] = message_id
            source.post(message_id, (
                "From: sender@example.invalid\r\n"
                "Newsgroups: fn.test\r\n"
                "Subject: distribution {}\r\n"
                "Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                "{}"
                "Message-ID: {}\r\n\r\n{}\r\n").format(
                    marker, header, message_id, marker).encode("ascii"), expect=EXIT_OK)
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
        self.assertIsNone(source.process.poll())
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "feed-distribution-filter-prf-237",
            "commands": commands, "received": received,
            "identity": self.verify_process_identity(source),
        }, sort_keys=True))

    # -----------------------------------------------------------------
    # PRF-335 (the openbsd-rehearsal release blocker, 2026-09-27): a
    # delivered feed entry stayed in the peer's queue, `peer add' fixes the
    # queue at 1,024, so after 1,024 fed articles every local post was
    # refused with an unnamed 441 while health said healthy.

    def fill_node(self, marker, down_port=None):
        """A node with two peers, both by source address: `injector'
        (127.0.0.1, inbound only: the test's raw TAKETHIS client) and
        `down' (127.0.0.2, outbound only, at DOWN_PORT)."""
        # Room for 12,000 transactions with a record bound small enough that
        # the heap the profile asks for fits the test's 24 GiB scope.
        node = self.initialize(marker, "--max-transactions", "12000",
                               "--max-record-octets", "262144",
                               "--max-history-octets", "134217728",
                               "--max-article-octets", "8192",
                               "--max-groups-per-article", "8", "fn.test")
        node.operator("peer", "add", "injector", "injector.example.invalid", "127.0.0.1",
                      str(free_port()), "fn.*", "-", "127.0.0.1", "true", expect=EXIT_OK)
        if down_port is not None:
            node.operator("peer", "add", "down", "down.example.invalid", "127.0.0.1",
                          str(down_port), "-", "fn.*", "127.0.0.2", "true", expect=EXIT_OK)
        return node

    def stop_timed(self, node):
        started = time.monotonic()
        node.process.stop(grace=300)
        return round(time.monotonic() - started, 2)

    def inject(self, node, ids):
        replies = []
        with socket.create_connection(("127.0.0.1", node.port), timeout=60) as client:
            stream = whole_stream(client)
            self.assertTrue(stream.readline().startswith(b"200 "))
            for message_id in ids:
                stream.write(b"TAKETHIS " + message_id.encode() + b"\r\n"
                             + self.article(message_id, message_id[1:-1]) + b".\r\n")
                replies.append(stream.readline())
            stream.write(b"QUIT\r\n")
        return replies

    def nntp_post(self, node, message_id):
        with socket.create_connection(("127.0.0.1", node.port), timeout=60) as client:
            stream = whole_stream(client)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"POST\r\n")
            offer = stream.readline()
            if not offer.startswith(b"340"):
                return offer
            stream.write(self.article(message_id, message_id[1:-1]) + b".\r\nQUIT\r\n")
            return stream.readline()

    def health(self, node):
        return node.operator("health", timeout=120)

    def test_feeding_past_the_queue_bound_keeps_local_posts_accepted(self):
        """PRF-335: 1,100 transit articles are fed to a streaming peer (more
        than `peer add''s max-queue of 1,024); every transfer is 239, every
        article reaches the peer, a local POST afterwards is 240, health
        does not hold unavailable-peer, and a restart opens in seconds (the
        rehearsal measured 35 to 46 s with the delivered entries kept)."""
        peer = ScriptedTransitPeer("203 streaming permitted")
        self.addCleanup(peer.close)
        node = self.fill_node("past-bound", peer.port)
        self.start(node)
        ids = ["<past-{}@example.invalid>".format(n) for n in range(1100)]
        # In batches the feed can drain: a batch past the peer's undelivered
        # bound would be deferred (436), which is the saturated test's case.
        for start in range(0, len(ids), 275):
            batch = ids[start:start + 275]
            replies = self.inject(node, batch)
            codes = [r[:3] for r in replies]
            self.assertEqual(set(codes), {b"239"},
                             [r for r in replies if r[:3] != b"239"][:5])
            self.assertIsNotNone(peer.await_article(batch[-1], timeout=600),
                                 "the peer never received " + batch[-1])
        with peer.lock:
            received = set(peer.articles)
        self.assertEqual(received, set(ids))
        posted = "<past-local@example.invalid>"
        reply = self.nntp_post(node, posted)
        self.assertTrue(reply.startswith(b"240"), reply)
        self.assertIsNotNone(peer.await_article(posted, timeout=120))
        health = self.health(node)
        self.assertIn(b"unavailable-peer clear", health.stdout, health.stdout)
        stopped = self.stop_timed(node)
        started = time.monotonic()
        self.start(node)
        opened = time.monotonic() - started
        reply = self.nntp_post(node, "<past-after-restart@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "feed-past-queue-bound-prf-335", "fed": len(received),
            "post": reply.decode("ascii", "replace").strip(),
            "restart_to_listening_s": round(opened, 2), "stop_s": stopped,
            "identity": self.verify_process_identity(node)}, sort_keys=True))
        # The rehearsal measured 35 to 46 s (90 s at hbox load 37); one
        # loaded run of this case took 20.9 s, the next 2.7 s.
        self.assertLess(opened, 30.0)

    def test_a_saturated_feed_queue_names_the_refusal_and_holds_health(self):
        """PRF-335: with the peer unreachable, its queue fills with
        undelivered obligations.  At the bound the next transfer is 436 (the
        sender keeps it, not the drop code 439), a local POST is the NAMED
        refusal feed-queue-full, and health holds unavailable-peer with
        saturated=1."""
        closed = free_port()
        node = self.fill_node("saturated", closed)
        self.start(node)
        ids = ["<sat-{}@example.invalid>".format(n) for n in range(1026)]
        replies = self.inject(node, ids)
        codes = [r[:3] for r in replies]
        self.assertEqual(set(codes[:1024]), {b"239"}, replies[:3])
        self.assertEqual(set(codes[1024:]), {b"436"}, replies[1024:])
        reply = self.nntp_post(node, "<sat-local@example.invalid>")
        self.assertTrue(reply.startswith(b"441 "), reply)
        self.assertIn(b"(feed-queue-full)", reply)
        health = self.health(node)
        self.assertNotEqual(health.returncode, 0, health.stdout)
        self.assertIn(b"unavailable-peer held", health.stdout, health.stdout)
        self.assertIn(b"saturated=1", health.stdout, health.stdout)
        identity = self.verify_process_identity(node)
        # The backlog is durable: after a restart the queue is still full
        # and the refusal still named.  The open time with 1,024 undelivered
        # entries is printed (a measurement, not a bound: fn-feedp is still
        # re-checked per replayed record).
        stopped = self.stop_timed(node)
        started = time.monotonic()
        self.start(node)
        opened = time.monotonic() - started
        again = self.nntp_post(node, "<sat-local-2@example.invalid>")
        self.assertIn(b"(feed-queue-full)", again)
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "feed-queue-saturated-prf-335",
            "post": reply.decode("ascii", "replace").strip(),
            "health": health.stdout.decode("ascii", "replace").splitlines()[:9],
            "restart_to_listening_s": round(opened, 2), "stop_s": stopped,
            "identity": identity}, sort_keys=True))

    def test_obligations_report_of_five_thousand_articles_answers(self):
        """PRF-336 (the openbsd-rehearsal, stop 2): `operator CONFIG
        obligations' at about 1,029 held obligations (keep-forever, one per
        article) exhausted the owner's 1,024 KB control stack in
        fn-native-live-status-host-answer and stopped the node.  At 5,000
        the report answers, the owner keeps running, and `status' still
        answers after it."""
        node = self.fill_node("obligations")
        self.start(node)
        ids = ["<obl-{}@example.invalid>".format(n) for n in range(5000)]
        # No outbound peer: nothing is fed, every article is held (keep-forever).
        replies = self.inject(node, ids)
        self.assertEqual(set(r[:3] for r in replies), {b"239"},
                         [r for r in replies if r[:3] != b"239"][:5])
        report = node.operator("obligations", timeout=300)
        self.assertEqual(report.returncode, 0, report.stderr[-2000:])
        first = report.stdout.split(b"\n", 1)[0]
        self.assertTrue(first.startswith(b"obligations="), first)
        held = int(first.split(b"=", 1)[1].split()[0])
        self.assertGreaterEqual(held, 5000, first)
        self.assertEqual(report.stdout.count(b"\nobligation id="), held, first)
        self.assertIsNone(node.process.poll(), "the owner stopped")
        status = node.operator("status", timeout=120)
        self.assertEqual(status.returncode, 0, status.stderr[-2000:])
        print("NATIVE-PEERING-WITNESS " + json.dumps({
            "kind": "obligations-five-thousand-prf-336", "held": held,
            "octets": len(report.stdout),
            "identity": self.verify_process_identity(node)}, sort_keys=True))
