"""Concurrent posters of the profile's largest articles: every POST is answered
accepted or refused by name, and the node never faults (lane zero-copy-commit,
2026-09-28; books/owner-article-slots.lisp, books/heap-store-figure.lisp).

Before the lane the dynamic space held no article in flight: each connection
mid-article retained its body as octet lists (32 octets of heap per octet
with the collector's copy) charged to the machine only, so enough concurrent
posters of large articles exhausted the heap and the node exited 4.  Now the
launcher's figure holds `fn-heap-article-slots' articles in flight and the
owner admits a connection into article mode only within them; past them a
POST is answered 440 with the memory reason at the command, before the
client sends anything.

THE CREDIT IS THE PACKED ARTICLE (lane chunked-body-2, B6b).  A slot's
reserve is twice the larger of the wire's packed store (at most A + 1
octets in 512-octet blocks: 544 octets of heap a block) and the queued
submission's packed form (books/heap-store-figure.lisp
fn-heap-article-reserve-octets), no longer 32 x (512 + A + HDR).  At the
default preset with A = 1 MiB the 64 MiB pool holds 30 articles in flight
(it held one): THIRTY posters are all offered 340, all hold their articles
half sent at once, and all are accepted; a thirty-first is answered 440 by
name meanwhile, and accepted afterwards.  At A = 4 MiB the pool holds 7.

THE DEADLOCK CASE (the policy is reserve-to-finish: a slot is a whole
article's worst case, so an admitted upload never needs more of the pool;
books/owner-article-held.lisp fn-oas-read-span-never-blocks-an-admitted-
article).  Under A = 4 MiB the node holds seven.  Seven posters are
admitted and each sends HALF its article, holding the whole pool; two more
are refused 440 by name; then the seven finish, last admitted first, and
each is accepted -- none waits on another -- and the two refused posters are
then admitted and accepted.

THE ONE-READ CASE (lane admission-gap, 2026-09-28; books/owner-article-held.lisp
fn-oah-read-span-keeps-held-within-the-slots).  A TAKETHIS (RFC 4644 section
2.5) carries its article with the command, so a small one arrives in ONE
socket read: the connection enters article mode and leaves it within the
read with one more submission queued.  The admission before this lane
checked only a read that left the connection newly mid-article, so such a
read was accepted (239) with every slot already held (by six posters and
one peer's IHAVE upload here): one article more than the slots.  Now the whole read is
refused: 400 with the memory reason and the connection closed (RFC 4644
offers TAKETHIS no "later"; RFC 3977 section 3.2.1's 400 is it), nothing it
carried is taken; the admitted IHAVE completes (235), and the TAKETHIS
retried afterwards is accepted (239).

    tools/hbox_native.sh --images developer,production . tests.test_native_article_slots
"""
import socket
import time
import unittest

from tests.test_native_bounds_join import JoinFixture, article, dot_stuff

from tests.native_harness import EXIT_OK  # noqa: E402
MIB4 = 4 * 1024 * 1024
INIT_PROFILE = ("--profile", "development", "--max-transactions", "1024",
                "--max-history-octets", str(64 << 20),
                "--max-record-octets", "4199563",
                "--max-article-octets", str(MIB4),
                "--max-groups-per-article", "16")
# The pool's articles in flight at A = 4 MiB and at A = 1 MiB (ACL2's own
# values: fn-heap-article-slots of the two profiles, header bound 16 KiB).
SLOTS_4MIB = 7
MIB1 = 1024 * 1024
SLOTS_1MIB = 30
MIB1_PROFILE = ("--profile", "default", "--max-transactions", "1024",
                "--max-history-octets", str(64 << 20),
                "--max-record-octets", "4199563",
                "--max-article-octets", str(MIB1),
                "--max-groups-per-article", "16")
def transit(message_id, total):
    """ARTICLE with a Date line, as a transit article must carry (RFC 5536
    section 3.1.1; otherwise 437 "no Injection-Date or Date")."""
    data = article(message_id, total)
    first, rest = data.split(b"\r\n", 1)
    return first + b"\r\nDate: Mon, 28 Sep 2026 12:00:00 +0000\r\n" + rest


MEMORY_400 = b"400 the articles in flight fill the memory; try again later"
MEMORY_440 = ("440 posting not permitted now; the articles in flight fill the "
              "memory, try again later")


class Poster:
    def __init__(self, port):
        self.conn = socket.create_connection(("127.0.0.1", port), timeout=300)
        self.stream = self.conn.makefile("rwb")
        greeting = self.stream.readline()
        assert greeting.startswith(b"200"), greeting

    def ask(self):
        self.stream.write(b"POST\r\n")
        self.stream.flush()
        return self.stream.readline().rstrip(b"\r\n").decode("ascii", "replace")

    def send(self, data, pieces=1, pause=0.0):
        step = max(1, len(data) // pieces)
        for start in range(0, len(data), step):
            self.stream.write(data[start:start + step])
            self.stream.flush()
            if pause:
                time.sleep(pause)
        return self.stream.readline().rstrip(b"\r\n").decode("ascii", "replace")

    def close(self):
        try:
            self.stream.write(b"QUIT\r\n")
            self.stream.flush()
        except OSError:
            pass
        self.conn.close()


class ArticleSlotsTests(JoinFixture):
    def hold_and_finish(self, profile, size, slots, extra, order):
        """SLOTS posters admitted, each with HALF its article sent, holding
        the pool at once; EXTRA more refused 440 by name; the admitted finish
        in ORDER (a permutation of range(SLOTS)) and are accepted; then the
        refused are admitted and accepted."""
        created = self.op("init", *profile, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        posters = [Poster(self.port) for _ in range(slots + extra)]
        try:
            wire = [dot_stuff(article("<slots-{}@example.invalid>".format(n), size - 4096))
                    + b".\r\n" for n in range(slots + extra)]
            halves = [len(w) // 2 for w in wire]
            for n in range(slots):
                offered = posters[n].ask()
                self.assertTrue(offered.startswith("340"), (n, offered))
                posters[n].stream.write(wire[n][:halves[n]])
                posters[n].stream.flush()
            time.sleep(1)
            refused = [posters[n].ask() for n in range(slots, slots + extra)]
            print(slots, "articles in flight at once; then:", refused, flush=True)
            self.assertEqual(refused, [MEMORY_440] * extra)
            self.assertIsNone(owner.poll(), "the node stopped")
            for n in order:
                done = posters[n].send(wire[n][halves[n]:], pieces=2)
                self.assertTrue(done.startswith("240"), (n, done))
            # A 440 by name while the previous submissions are still held by
            # the commit is the same refusal; the poster asks again.
            for n in range(slots, slots + extra):
                for _ in range(50):
                    offered = posters[n].ask()
                    if offered != MEMORY_440:
                        break
                    time.sleep(0.2)
                self.assertTrue(offered.startswith("340"), (n, offered))
                accepted = posters[n].send(wire[n], pieces=2)
                self.assertTrue(accepted.startswith("240"), (n, accepted))
            self.assertIsNone(owner.poll(), "the node stopped")
        finally:
            for p in posters:
                p.close()
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], slots + extra)

    def test_thirty_one_mib_posters_are_all_mid_article_at_once(self):
        self.hold_and_finish(MIB1_PROFILE, MIB1, SLOTS_1MIB, 1, range(SLOTS_1MIB))

    def test_partial_uploads_holding_the_pool_all_complete(self):
        self.hold_and_finish(INIT_PROFILE, MIB4, SLOTS_4MIB, 2,
                             reversed(range(SLOTS_4MIB)))

    def test_a_takethis_within_one_read_past_the_slot_is_refused_whole(self):
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        # Loopback is this peer (outbound "-": the node never dials it).
        added = self.op("peer", "add", "slots-peer", "slots-peer.example.invalid",
                        "127.0.0.1", "1", "fn.*", "-", "127.0.0.1", "true")
        self.assertEqual(added.returncode, EXIT_OK, added.stderr.decode())
        owner = self.node.start(image=self.image)
        uploader = Poster(self.port)
        posters = [Poster(self.port) for _ in range(SLOTS_4MIB - 1)]
        try:
            # All slots but one held by posters mid-article.
            wire = [dot_stuff(article("<slots-{}@example.invalid>".format(n), MIB4 - 4096))
                    + b".\r\n" for n in range(SLOTS_4MIB - 1)]
            for n, p in enumerate(posters):
                offered = p.ask()
                self.assertTrue(offered.startswith("340"), (n, offered))
                p.stream.write(wire[n][:len(wire[n]) // 2])
                p.stream.flush()
            held_id = "<slots-ihave@example.invalid>"
            held = dot_stuff(transit(held_id, 64 * 1024)) + b".\r\n"
            uploader.stream.write(b"IHAVE " + held_id.encode("ascii") + b"\r\n")
            uploader.stream.flush()
            offered = uploader.stream.readline()
            self.assertTrue(offered.startswith(b"335"), offered)
            # Mid-article: the last slot is held.
            half = len(held) // 2
            uploader.stream.write(held[:half])
            uploader.stream.flush()
            time.sleep(1)
            streamed_id = "<slots-takethis@example.invalid>"
            streamed = (b"TAKETHIS " + streamed_id.encode("ascii") + b"\r\n"
                        + dot_stuff(transit(streamed_id, 600)) + b".\r\n")
            with socket.create_connection(("127.0.0.1", self.port), timeout=60) as peer:
                stream = peer.makefile("rwb")
                self.assertTrue(stream.readline().startswith(b"200"))
                stream.write(streamed)   # one write, one read at the owner
                stream.flush()
                answer = stream.readline().rstrip(b"\r\n")
                closed = stream.readline()
            print("a TAKETHIS in one read past the slot:", answer, closed, flush=True)
            self.assertEqual(answer, MEMORY_400)
            self.assertEqual(closed, b"", "the connection stays open after 400")
            self.assertIsNone(owner.poll(), "the node stopped")
            done = uploader.send(held[half:], pieces=2)
            self.assertTrue(done.startswith("235"), done)
            # The retried TAKETHIS is accepted once the commit released the slot.
            for _ in range(50):
                with socket.create_connection(("127.0.0.1", self.port), timeout=60) as peer:
                    stream = peer.makefile("rwb")
                    self.assertTrue(stream.readline().startswith(b"200"))
                    stream.write(streamed)
                    stream.flush()
                    answer = stream.readline().rstrip(b"\r\n")
                if answer != MEMORY_400:
                    break
                time.sleep(0.2)
            self.assertTrue(answer.startswith(b"239"), answer)
            for n, p in enumerate(posters):
                done = p.send(wire[n][len(wire[n]) // 2:], pieces=2)
                self.assertTrue(done.startswith("240"), (n, done))
            self.assertIsNone(owner.poll(), "the node stopped")
        finally:
            uploader.close()
            for p in posters:
                p.close()
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], 2 + SLOTS_4MIB - 1)


if __name__ == "__main__":
    unittest.main()
