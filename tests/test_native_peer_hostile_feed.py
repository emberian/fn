"""A stranger's server talking back: replies a peer may legally or wrongly
give fn's feed, and offers that must not poison what fn will take
(lane scenarios with lane read-peer, 2026-10-04).

Outbound (fn feeds a scripted streaming peer):

* throttled: the peer answers `431 <id>` (try later, RFC 4644 section
  2.4) to CHECK four times, then takes the article.  fn keeps the article it
  offered (specs/peering.md section 9; PKT-711) and delivers it.  Ledger:
  rp-feed-defer-drop -- today it is dropped after the third 431
  (*fn-own-feed-retry-bound* = 3).
* stray reply: the peer answers one TAKETHIS with `239 <a>` twice.  The
  stray line must not be read as the answer to the next offer: the next
  article <b> is still transferred.  Ledger: rp-feed-reply-msgid.

Inbound (fn receives from two configured peers, X on 127.0.0.1 and Y on
127.0.0.2):

* poisoned Message-ID: X sends `TAKETHIS <v>` whose article says another
  Message-ID and gets 439.  Y's `CHECK <v>` must still be wanted (238),
  and Y's genuine <v> is taken and served.  A forged offer from one peer
  denies nothing to another.  Ledger: rp-refused-memory-poison, a design
  question.
* changed bytes after acceptance: X's <s> is taken.  X's `CHECK <s>` gets
  438, and a TAKETHIS of other bytes under <s> gets 439.  The stored <s>
  is unchanged.

Also: a peer that swallows CHECK or never greets is dropped at the round
deadline (600 s) and redialled (slow: ten minutes), and a TAKETHIS whose id
fails the grammar is consumed and refused without running its body as
commands (rp-takethis-bad-msgid-desync).

The node is the production image (FN_NATIVE_HOST).
"""

import os
import socket
import threading
import time
import unittest

from tests.native_harness import EXIT_OK, Client, Node, free_port, native_image, scratch
from tools.wire_stream import whole_stream

IMAGE = native_image("FN_NATIVE_HOST")
READY = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
GROUP = "fn.test"
DELIVERY_SECONDS = 180


def article(message_id, marker, header_id=None):
    return ("From: poster@example.invalid\r\n"
            "Newsgroups: {}\r\n"
            "Subject: hostile feed {}\r\n"
            "Date: {}\r\n"
            "Path: x.example.invalid!not-for-mail\r\n"
            "Message-ID: {}\r\n\r\n{} body\r\n".format(
                GROUP, marker, time.strftime("%a, %d %b %Y %H:%M:%S +0000", time.gmtime()),
                header_id or message_id, marker)).encode("ascii")


def stuffed(octets):
    lines = octets.split(b"\r\n")
    return b"\r\n".join(b"." + line if line.startswith(b".") else line for line in lines)


class StreamingPeer:
    """An INN-shaped streaming peer whose answers a case scripts:
    check(id, n) gives the reply line to the n-th CHECK of id;
    takethis(id) gives the reply lines to a TAKETHIS of id."""

    def __init__(self, check, takethis, mute_first=False):
        self.check, self.takethis = check, takethis
        self.mute_first = mute_first
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        self.lock = threading.Lock()
        self.commands, self.articles, self.checks = [], {}, {}
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
            threading.Thread(target=self.session, args=(client, number), daemon=True).start()

    def session(self, client, number):
        with client:
            if self.mute_first and number == 1:
                # Accepts the dial and never greets: the socket stays open.
                while client.recv(4096):
                    pass
                return
            stream = whole_stream(client)
            stream.write(b"200 scripted streaming peer\r\n")
            while True:
                line = stream.readline()
                if not line:
                    return
                words = line.rstrip(b"\r\n").decode("ascii", "replace").split()
                verb = words[0].upper() if words else ""
                with self.lock:
                    self.commands.append(" ".join(words))
                if verb == "MODE":
                    stream.write(b"203 streaming permitted\r\n")
                elif verb == "CHECK":
                    with self.lock:
                        n = self.checks[words[1]] = self.checks.get(words[1], 0) + 1
                    reply = self.check(words[1], n)
                    if reply is not None:  # None: swallowed, the socket stays open
                        stream.write(reply.encode("ascii") + b"\r\n")
                elif verb == "TAKETHIS":
                    body = bytearray()
                    while True:
                        part = stream.readline()
                        if not part or part == b".\r\n":
                            break
                        body.extend(part[1:] if part.startswith(b"..") else part)
                    with self.lock:
                        self.articles[words[1]] = bytes(body)
                    for reply in self.takethis(words[1]):
                        stream.write(reply.encode("ascii") + b"\r\n")
                elif verb == "IHAVE":
                    stream.write(b"435 streaming only here\r\n")
                elif verb == "QUIT":
                    stream.write(b"205 bye\r\n")
                    return
                else:
                    stream.write(b"500 unknown command\r\n")

    def await_article(self, message_id, timeout):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            with self.lock:
                if message_id in self.articles:
                    return self.articles[message_id]
            time.sleep(0.2)
        return None


@unittest.skipUnless(READY, "needs the production image (FN_NATIVE_HOST): {}".format(IMAGE))
class HostileFeedTests(unittest.TestCase):

    def setUp(self):
        self.base = scratch(self, "fn-peer-hostile-")

    def node(self, name):
        node = Node(self, IMAGE, root=self.base / name, name=name)
        node.store("init", GROUP, expect=EXIT_OK)
        return node

    def feeding(self, peer):
        source = self.node("source")
        source.operator("peer", "add", "stranger", "stranger.example.invalid", "127.0.0.1",
                        str(peer.port), "-", "fn.*", "127.0.0.1", "true", expect=EXIT_OK)
        source.start()
        self.assertIsNone(source.process.poll())
        return source

    def post(self, node, message_id, marker):
        node.post(message_id, article(message_id, marker), group=GROUP, expect=EXIT_OK)

    # -- outbound -------------------------------------------------------------

    def test_a_peer_throttling_with_431_still_gets_the_article(self):
        peer = StreamingPeer(lambda mid, n: ("431 " if n <= 4 else "238 ") + mid,
                             lambda mid: ["239 " + mid])
        self.addCleanup(peer.close)
        source = self.feeding(peer)
        wanted = "<throttled@example.invalid>"
        self.post(source, wanted, "throttled")
        got = peer.await_article(wanted, DELIVERY_SECONDS)
        with peer.lock:
            checks, commands = dict(peer.checks), list(peer.commands)
        print("PEER-HOSTILE-FEED throttled checks={} commands={}".format(
            checks.get(wanted, 0), len(commands)), flush=True)
        self.assertIsNotNone(got, "a 431 (try later) answer made fn drop the article: "
                                  "{} CHECKs, commands {}".format(checks.get(wanted), commands[-12:]))
        self.assertGreaterEqual(checks.get(wanted, 0), 5, checks)
        self.assertIsNone(source.process.poll())

    def test_a_stray_239_is_not_the_answer_to_the_next_offer(self):
        first = "<stray-a@example.invalid>"
        peer = StreamingPeer(lambda mid, n: "238 " + mid,
                             lambda mid: ["239 " + mid] * (2 if mid == first else 1))
        self.addCleanup(peer.close)
        source = self.feeding(peer)
        self.post(source, first, "stray-a")
        self.assertIsNotNone(peer.await_article(first, DELIVERY_SECONDS))
        second = "<stray-b@example.invalid>"
        self.post(source, second, "stray-b")
        got = peer.await_article(second, DELIVERY_SECONDS)
        with peer.lock:
            commands = list(peer.commands)
        self.assertIsNotNone(got, "the stray 239 for {} was taken as the answer for {}: {}"
                             .format(first, second, commands[-12:]))
        self.assertIsNone(source.process.poll())

    def test_a_silent_peer_is_dropped_at_the_round_deadline_and_redialled(self):
        """read-peer case 1, native and slow: one peer swallows the first CHECK
        (no reply, socket open), another accepts the dial and never greets.
        Each link is dropped at fn-prd-round-deadline (600 s,
        books/peer-round-driver.lisp) and redialled, and the article is
        delivered on the redial.  The fast witness is
        tests.test_native_feed_fair_round's reply-deadline case."""
        silent = StreamingPeer(lambda mid, n: None if n == 1 else "238 " + mid,
                               lambda mid: ["239 " + mid])
        mute = StreamingPeer(lambda mid, n: "238 " + mid, lambda mid: ["239 " + mid],
                             mute_first=True)
        for peer in (silent, mute):
            self.addCleanup(peer.close)
        source = self.node("source")
        for name, peer in (("silent", silent), ("mute", mute)):
            source.operator("peer", "add", name, "{}.example.invalid".format(name), "127.0.0.1",
                            str(peer.port), "-", "fn.*", "127.0.0.1", "true", expect=EXIT_OK)
        source.start()
        wanted = "<silent@example.invalid>"
        self.post(source, wanted, "silent")
        got = {name: peer.await_article(wanted, 720) for name, peer in
               (("silent", silent), ("mute", mute))}
        print("PEER-HOSTILE-FEED silent connections={} mute connections={}".format(
            silent.connections, mute.connections), flush=True)
        self.assertIsNotNone(got["silent"], "a peer that swallowed CHECK held the link and "
                                            "the article past the round deadline")
        self.assertIsNotNone(got["mute"], "a peer that never greeted held the link past "
                                          "the round deadline")
        self.assertGreaterEqual(silent.connections, 2)
        self.assertGreaterEqual(mute.connections, 2)
        self.assertIsNone(source.process.poll())

    # -- inbound --------------------------------------------------------------

    def test_a_takethis_with_an_ungrammatical_id_never_desynchronises_the_stream(self):
        """read-peer case 7 (rp-takethis-bad-msgid-desync): TAKETHIS's argument
        fails the Message-ID grammar (here 260 octets), and its article's body
        holds a line `TAKETHIS <inner@...>` with a forged header block.  The
        article is consumed whole and refused 439 (RFC 4644 section 2.5:
        TAKETHIS is always followed by the article); nothing in its body is
        run as a command, and the stream stays in step."""
        target = self.receiving()
        x = self.streaming(target, "127.0.0.1")
        bad = "<" + "a" * 260 + "@x.example.invalid>"
        inner = "<inner@x.example.invalid>"
        smuggled = (b"TAKETHIS " + inner.encode("ascii") + b"\r\n" + article(inner, "forged"))
        payload = article("<outer@x.example.invalid>", "outer") + smuggled
        first = self.takethis(x, bad, payload)
        self.assertTrue(first.startswith(b"439"), first)
        fresh = "<fresh@x.example.invalid>"
        after = x.command(b"CHECK " + fresh.encode("ascii"))
        self.assertTrue(after.startswith(b"238 " + fresh.encode("ascii")),
                        "the stream is out of step after the refused TAKETHIS: {!r}".format(after))
        with Client(target.port, timeout=30, greeting=(b"200", b"201")) as reader:
            self.assertTrue(reader.command(b"STAT " + inner.encode("ascii")).startswith(b"430"),
                            "the smuggled inner article was stored")
        self.assertIsNone(target.process.poll())

    def receiving(self):
        target = self.node("target")
        for name, address in (("x", "127.0.0.1"), ("y", "127.0.0.2")):
            target.operator("peer", "add", name, "{}.example.invalid".format(name), address,
                            str(free_port()), "fn.*", "-", address, "true", expect=EXIT_OK)
        target.start()
        return target

    def streaming(self, node, source):
        try:
            client = Client(node.port, timeout=30, greeting=(b"200",), source=source)
        except OSError as error:
            self.skipTest("cannot bind {} here: {}".format(source, error))
        self.addCleanup(client.close, quit=False)
        self.assertTrue(client.command(b"MODE STREAM").startswith(b"203"))
        return client

    def takethis(self, client, message_id, octets):
        client.send(b"TAKETHIS " + message_id.encode("ascii") + b"\r\n"
                    + stuffed(octets) + b".\r\n")
        return client.line()

    def test_a_forged_offer_from_one_peer_denies_nothing_to_another(self):
        target = self.receiving()
        victim = "<victim@a.example.invalid>"
        x = self.streaming(target, "127.0.0.1")
        forged = self.takethis(x, victim, article(victim, "forged", header_id="<other@x.invalid>"))
        self.assertTrue(forged.startswith(b"439"), forged)
        y = self.streaming(target, "127.0.0.2")
        wanted = y.command(b"CHECK " + victim.encode("ascii"))
        self.assertTrue(wanted.startswith(b"238"),
                        "X's forged offer made fn refuse Y's genuine {}: {!r}".format(victim, wanted))
        taken = self.takethis(y, victim, article(victim, "genuine"))
        self.assertTrue(taken.startswith(b"239"), taken)
        with Client(target.port, timeout=30, greeting=(b"200", b"201")) as reader:
            served = reader.article(victim)
        self.assertIsNotNone(served)
        self.assertIn(b"genuine body", served)

    def test_changed_bytes_after_acceptance_are_refused_and_change_nothing(self):
        target = self.receiving()
        kept = "<kept@x.example.invalid>"
        x = self.streaming(target, "127.0.0.1")
        self.assertTrue(self.takethis(x, kept, article(kept, "original")).startswith(b"239"))
        self.assertTrue(x.command(b"CHECK " + kept.encode("ascii")).startswith(b"438"))
        other = self.takethis(x, kept, article(kept, "changed"))
        self.assertTrue(other.startswith(b"439"), other)
        with Client(target.port, timeout=30, greeting=(b"200", b"201")) as reader:
            served = reader.article(kept)
        self.assertIsNotNone(served)
        self.assertIn(b"original body", served)
        self.assertNotIn(b"changed body", served)
        self.assertIsNone(target.process.poll())


if __name__ == "__main__":
    unittest.main()
