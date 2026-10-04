"""A misbehaving peer never pins the owner (lane scenarios, 2026-10-04).

ember, 2026-10-04: fn's first external collaborator will peer with the next
redeploy, so "a slow or misbehaving peer (stalls, resets, garbage,
slowloris) must never pin the owner or stop the node".  The reader-port
strangers are tests.test_native_public_exposure's; a peer that dies or
resets around a completed transfer is tests.test_native_peering's.  This
module is the configured peer that misbehaves *inside* a transfer:

* it opens IHAVE, gets 335 and trickles the article a few octets at a time
  and never ends it (slowloris inside a transfer);
* it opens a TAKETHIS stream, sends half an article and resets;
* it sends unframed garbage, NULs and a line with no end after MODE STREAM;
* it floods CHECK and never reads a reply (the owner's writes back up).

During each, on other connections:

* a reader's DATE is answered within READER_BOUND seconds every time;
* a well-behaved transfer from the same peer address completes (235) and
  its article is served byte-exact.

After each:

* the owner is still running;
* the half-sent article is not stored (STAT 430);
* the same Message-ID transfers cleanly afterwards (335 then 235). A
  transfer that died must leave no reservation that refuses the id
  forever.

The node is the production image (FN_NATIVE_HOST): what a stranger meets.
"""

import os
import socket
import struct
import threading
import time
import unittest

from tests.native_harness import EXIT_OK, Client, Node, free_port, native_image, scratch

IMAGE = native_image("FN_NATIVE_HOST")
READY = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
GROUP = "fn.test"
# public_exposure's bound for the legitimate reader under a flood.
READER_BOUND = 5.0
TRANSFER_BOUND = 20.0
STALL_SECONDS = 15.0


def article(message_id, marker, lines=1):
    body = "".join("{} line {}\r\n".format(marker, n) for n in range(lines))
    return ("From: stranger@peer.example.invalid\r\n"
            "Newsgroups: {}\r\n"
            "Subject: misbehaving peer {}\r\n"
            "Date: Sun, 04 Oct 2026 12:00:00 +0000\r\n"
            "Path: peer.example.invalid!not-for-mail\r\n"
            "Message-ID: {}\r\n\r\n{}".format(GROUP, marker, message_id, body)).encode("ascii")


class ReaderWatch:
    """A reader sending DATE every quarter second on its own connection,
    recording each answer's latency; a missed or late answer is kept."""

    def __init__(self, port):
        self.port = port
        self.latencies = []
        self.failures = []
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self.run, daemon=True)
        self.thread.start()

    def run(self):
        try:
            client = Client(self.port, timeout=30, greeting=(b"200", b"201"))
        except Exception as error:  # noqa: BLE001 - reported by the case
            self.failures.append("connect: {!r}".format(error))
            return
        with client:
            while not self.stop.is_set():
                started = time.monotonic()
                try:
                    reply = client.command(b"DATE")
                except Exception as error:  # noqa: BLE001
                    self.failures.append("DATE: {!r}".format(error))
                    return
                self.latencies.append(time.monotonic() - started)
                if not reply.startswith(b"111 "):
                    self.failures.append("DATE answered {!r}".format(reply))
                self.stop.wait(0.25)

    def finish(self):
        self.stop.set()
        self.thread.join(40)
        return self.latencies, self.failures


def raw(port):
    sock = socket.create_connection(("127.0.0.1", port), timeout=30)
    greeting = b""
    while not greeting.endswith(b"\r\n"):
        chunk = sock.recv(1)
        if not chunk:
            raise EOFError("closed before the greeting")
        greeting += chunk
    if not greeting.startswith(b"200 "):
        raise AssertionError("greeting {!r}".format(greeting))
    return sock


def reset(sock):
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    sock.close()


@unittest.skipUnless(READY, "needs the production image (FN_NATIVE_HOST): {}".format(IMAGE))
class MisbehavingPeerTests(unittest.TestCase):

    def setUp(self):
        self.base = scratch(self, "fn-peer-misbehaving-")
        self.node = Node(self, IMAGE, root=self.base / "target", name="target")
        self.node.store("init", GROUP, expect=EXIT_OK)
        # The stranger's server: inbound fn.*, nothing outbound, from 127.0.0.1.
        self.node.operator("peer", "add", "stranger", "peer.example.invalid", "127.0.0.1",
                           str(free_port()), "fn.*", "-", "127.0.0.1", "true",
                           expect=EXIT_OK)
        self.node.start()
        self.port = self.node.port

    # -- the oracle ---------------------------------------------------------

    def transfer(self, message_id, marker):
        """A well-behaved IHAVE of a fresh article: (offer, final, seconds)."""
        started = time.monotonic()
        with Client(self.port, timeout=TRANSFER_BOUND, greeting=(b"200",)) as client:
            offer, final = client.post(article(message_id, marker),
                                       verb=b"IHAVE " + message_id.encode("ascii"))
        return offer, final, time.monotonic() - started

    def served(self, message_id):
        with Client(self.port, timeout=30, greeting=(b"200", b"201")) as client:
            return client.article(message_id)

    def stat(self, message_id):
        with Client(self.port, timeout=30, greeting=(b"200", b"201")) as client:
            return client.command(b"STAT " + message_id.encode("ascii"))

    def assert_alive(self, what):
        self.assertIsNone(self.node.process.poll(),
                          "{} stopped the owner: {}".format(
                              what, self.node.process.stderr.tail().decode("utf-8", "replace")))

    def assert_served_meanwhile(self, watch, what, good_id):
        offer, final, seconds = self.transfer(good_id, what)
        self.assertTrue(offer.startswith(b"335"), (what, offer))
        self.assertTrue(final is not None and final.startswith(b"235"), (what, final))
        self.assertLess(seconds, TRANSFER_BOUND, what)
        latencies, failures = watch.finish()
        self.assertEqual(failures, [], what)
        self.assertGreater(len(latencies), 4, (what, latencies))
        self.assertLess(max(latencies), READER_BOUND, (what, sorted(latencies)[-5:]))
        served = self.served(good_id)
        self.assertIsNotNone(served, what)
        self.assertTrue(served.endswith(article(good_id, what).split(b"\r\n\r\n", 1)[1]),
                        what)
        print("PEER-MISBEHAVING {} reader-max-s={:.3f} reader-n={} transfer-s={:.3f}".format(
            what, max(latencies), len(latencies), seconds), flush=True)

    def assert_id_unspoiled(self, message_id, what):
        """The half-sent article is absent, and the id transfers cleanly now."""
        self.assertTrue(self.stat(message_id).startswith(b"430"), (what, message_id))
        # Nothing about the dead transfer is remembered as refused: a
        # streaming peer's CHECK still wants it (lane read-peer's case 5).
        with Client(self.port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"MODE STREAM").startswith(b"203"), what)
            wanted = client.command(b"CHECK " + message_id.encode("ascii"))
        self.assertTrue(wanted.startswith(b"238"), (what, "CHECK after the dead transfer", wanted))
        offer, final, _ = self.transfer(message_id, what + "-retry")
        self.assertTrue(offer.startswith(b"335"), (what, "retry offer", offer))
        self.assertTrue(final is not None and final.startswith(b"235"),
                        (what, "retry", final))

    # -- the cases ----------------------------------------------------------

    def test_a_peer_trickling_an_article_inside_ihave_pins_nothing(self):
        stalled = "<trickle@peer.example.invalid>"
        sock = raw(self.port)
        sock.sendall(b"IHAVE " + stalled.encode("ascii") + b"\r\n")
        offer = sock.recv(512)
        self.assertTrue(offer.startswith(b"335"), offer)
        payload = article(stalled, "trickle", lines=400)
        watch = ReaderWatch(self.port)
        deadline = time.monotonic() + STALL_SECONDS
        sent = 0
        closed_by_node = False
        try:
            while time.monotonic() < deadline and sent < len(payload) - 8:
                sock.sendall(payload[sent:sent + 3])
                sent += 3
                time.sleep(0.2)
        except OSError:
            closed_by_node = True  # the node may end a stalled transfer: allowed
        self.assert_served_meanwhile(watch, "trickle", "<trickle-good@peer.example.invalid>")
        self.assert_alive("a trickled IHAVE")
        reset(sock)
        time.sleep(0.5)
        self.assert_alive("resetting a trickled IHAVE")
        print("PEER-MISBEHAVING trickle sent={} closed-by-node={}".format(sent, closed_by_node))
        self.assert_id_unspoiled(stalled, "trickle")

    def test_a_peer_resetting_half_way_through_takethis_spoils_nothing(self):
        half = "<half@peer.example.invalid>"
        sock = raw(self.port)
        sock.sendall(b"MODE STREAM\r\n")
        mode = sock.recv(512)
        self.assertTrue(mode.startswith(b"203"), mode)
        payload = article(half, "half", lines=2000)
        watch = ReaderWatch(self.port)
        sock.sendall(b"TAKETHIS " + half.encode("ascii") + b"\r\n" + payload[:len(payload) // 2])
        time.sleep(1.0)
        reset(sock)
        self.assert_served_meanwhile(watch, "half-takethis", "<half-good@peer.example.invalid>")
        self.assert_alive("a reset half-way through TAKETHIS")
        self.assert_id_unspoiled(half, "half-takethis")

    def test_garbage_and_an_endless_line_from_a_peer_stop_nothing(self):
        watch = ReaderWatch(self.port)
        sock = raw(self.port)
        sock.sendall(b"MODE STREAM\r\n")
        sock.recv(512)
        garbage = bytes((n * 7919 + 13) % 256 for n in range(65536))
        try:
            sock.sendall(garbage + b"\0\0\0\r\n" + b"TAKETHIS " + b"x" * (2 << 20))
        except OSError:
            pass  # the node may close a connection that sends this: allowed
        time.sleep(2.0)
        reset(sock)
        self.assert_served_meanwhile(watch, "garbage", "<garbage-good@peer.example.invalid>")
        self.assert_alive("garbage from a peer")

    def test_a_peer_that_never_reads_its_check_replies_pins_nothing(self):
        flooder = raw(self.port)
        flooder.sendall(b"MODE STREAM\r\n")
        self.assertTrue(flooder.recv(512).startswith(b"203"))
        flooder.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
        watch = ReaderWatch(self.port)
        lines = b"".join(b"CHECK <never-read-%d@peer.example.invalid>\r\n" % n
                         for n in range(100000))
        flooder.settimeout(STALL_SECONDS)
        sent = 0
        try:
            while sent < len(lines):
                sent += flooder.send(lines[sent:sent + 65536])
        except OSError:
            pass  # the node stopped reading (or closed): its replies are unread
        self.assert_served_meanwhile(watch, "unread-check", "<unread-good@peer.example.invalid>")
        self.assert_alive("a peer that never reads its replies")
        reset(flooder)
        time.sleep(0.5)
        self.assert_alive("resetting the unread CHECK flood")
        print("PEER-MISBEHAVING unread-check sent-octets={}".format(sent), flush=True)


if __name__ == "__main__":
    unittest.main()
