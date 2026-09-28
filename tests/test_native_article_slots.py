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

Under a profile with A = 4 MiB, one slot's reserve is 32 x (512 + A + HDR),
past the 64 MiB slot budget, so the node holds ONE article in flight.  N = 6 posters each send POST; exactly one is offered 340 while the
others are answered 440 by name; the first sends its 4 MiB article slowly (in
pieces, so it stays mid-article while the others ask), then it is accepted
(240); the refused posters then post in turn and are accepted.  The node is
alive throughout and stops cleanly (exit 0).

THE DEADLOCK CASE (the policy is reserve-to-finish: a slot is a whole
article's worst case, so an admitted upload never needs more of the pool;
books/owner-article-held.lisp fn-oas-read-span-never-blocks-an-admitted-
article).  Under A = 600,000 the node holds three.  Three posters are
admitted and each sends HALF its article, holding the whole pool; two more
are refused 440 by name; then the three finish, last admitted first, and each
is accepted -- none waits on another -- and the two refused posters are then
admitted and accepted.

THE ONE-READ CASE (lane admission-gap, 2026-09-28; books/owner-article-held.lisp
fn-oah-read-span-keeps-held-within-the-slots).  A TAKETHIS (RFC 4644 section
2.5) carries its article with the command, so a small one arrives in ONE
socket read: the connection enters article mode and leaves it within the
read with one more submission queued.  The admission before this lane
checked only a read that left the connection newly mid-article, so such a
read was accepted (239) with the one slot already held by another peer's
IHAVE upload: two articles in flight in one slot.  Now the whole read is
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
POSTERS = 6
A600K = 600000
DEADLOCK_PROFILE = ("--profile", "development", "--max-transactions", "1024",
                    "--max-history-octets", str(64 << 20),
                    "--max-record-octets", "4199563",
                    "--max-article-octets", str(A600K),
                    "--max-groups-per-article", "16")
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
    def test_concurrent_large_posters_are_answered_by_name_and_the_node_lives(self):
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        posters = [Poster(self.port) for _ in range(POSTERS)]
        try:
            wire = [dot_stuff(article("<slots-{}@example.invalid>".format(n), MIB4 - 4096))
                    + b".\r\n" for n in range(POSTERS)]
            first = posters[0].ask()
            self.assertTrue(first.startswith("340"), first)
            # The first poster is mid-article: half its body sent.
            half = len(wire[0]) // 2
            posters[0].stream.write(wire[0][:half])
            posters[0].stream.flush()
            time.sleep(1)
            refused = [p.ask() for p in posters[1:]]
            print("while one article is in flight:", refused, flush=True)
            self.assertEqual(refused, [MEMORY_440] * (POSTERS - 1))
            self.assertIsNone(owner.poll(), "the node stopped")
            done = posters[0].send(wire[0][half:], pieces=8, pause=0.05)
            self.assertTrue(done.startswith("240"), done)
            # In turn, each refused poster is admitted and accepted.
            # (A 440 by name while the previous submission is still held by
            # the commit is the same refusal; the poster asks again.)
            for n in range(1, POSTERS):
                for _ in range(50):
                    offered = posters[n].ask()
                    if offered != MEMORY_440:
                        break
                    time.sleep(0.2)
                self.assertTrue(offered.startswith("340"), (n, offered))
                accepted = posters[n].send(wire[n], pieces=4)
                self.assertTrue(accepted.startswith("240"), (n, accepted))
            self.assertIsNone(owner.poll(), "the node stopped")
        finally:
            for p in posters:
                p.close()
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], POSTERS)

    def test_partial_uploads_holding_the_pool_all_complete(self):
        created = self.op("init", *DEADLOCK_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        posters = [Poster(self.port) for _ in range(5)]
        try:
            wire = [dot_stuff(article("<pool-{}@example.invalid>".format(n), A600K - 4096))
                    + b".\r\n" for n in range(5)]
            halves = [len(w) // 2 for w in wire]
            for n in range(3):
                offered = posters[n].ask()
                self.assertTrue(offered.startswith("340"), (n, offered))
                posters[n].stream.write(wire[n][:halves[n]])
                posters[n].stream.flush()
            time.sleep(1)
            refused = [posters[n].ask() for n in (3, 4)]
            print("the pool held by three partial uploads:", refused, flush=True)
            self.assertEqual(refused, [MEMORY_440, MEMORY_440])
            for n in (2, 1, 0):
                done = posters[n].send(wire[n][halves[n]:], pieces=2)
                self.assertTrue(done.startswith("240"), (n, done))
            for n in (3, 4):
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
        self.assertEqual(self.headroom()["transactions-used"], 5)

    def test_a_takethis_within_one_read_past_the_slot_is_refused_whole(self):
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        # Loopback is this peer (outbound "-": the node never dials it).
        added = self.op("peer", "add", "slots-peer", "slots-peer.example.invalid",
                        "127.0.0.1", "1", "fn.*", "-", "127.0.0.1", "true")
        self.assertEqual(added.returncode, EXIT_OK, added.stderr.decode())
        owner = self.node.start(image=self.image)
        uploader = Poster(self.port)
        try:
            held_id = "<slots-ihave@example.invalid>"
            held = dot_stuff(article(held_id, 64 * 1024)) + b".\r\n"
            uploader.stream.write(b"IHAVE " + held_id.encode("ascii") + b"\r\n")
            uploader.stream.flush()
            offered = uploader.stream.readline()
            self.assertTrue(offered.startswith(b"335"), offered)
            # Mid-article: the one slot is held.
            half = len(held) // 2
            uploader.stream.write(held[:half])
            uploader.stream.flush()
            time.sleep(1)
            streamed_id = "<slots-takethis@example.invalid>"
            streamed = (b"TAKETHIS " + streamed_id.encode("ascii") + b"\r\n"
                        + dot_stuff(article(streamed_id, 600)) + b".\r\n")
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
            self.assertIsNone(owner.poll(), "the node stopped")
        finally:
            uploader.close()
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], 2)


if __name__ == "__main__":
    unittest.main()
