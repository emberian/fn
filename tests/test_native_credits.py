"""Memory credits on the served path (lane credits, B5; books/owner-credits.lisp,
PRF-380; SCN-194).

The launcher's reservation is the credit budget: what it leaves free is the
articles' pool (fn-mca-initial-funds-exactly-the-articles), and every
buffer an article occupies holds one reserve of it -- the body mid-article,
the queued submission, the submission the committer took, and the batch in
flight until its barrier returns.  A client that goes away frees only its
own body and queue, never what the committer or its fdatasync still owns
(fn-mca-close-keeps-what-the-commit-owns).

1. THE BATCH IN FLIGHT KEEPS ITS CREDIT (SCN-194; developer image, the
   barrier held 3 s by FN_NATIVE_OWNER_TEST_BARRIER_MS, under D = 5 s so the
   disk is not yet slow).  A = 4 MiB: the pool holds seven articles (lane
   chunked-body-2: the reserve is the packed article); six posters hold six
   of them mid-article.  Poster A sends its whole article and hangs up; while
   its batch's barrier runs, B's POST is answered the memory 440 by name.  Before this lane the owner's
   queue, its in-flight field and A's connection were all empty by then
   (the pipeline feeds each member's outcome before the barrier), so the
   slots admitted B's body beside the batch the syncer still held.  After
   the barrier B is admitted and accepted, and A's article is durable; the
   six finish.

2. MANY LARGE POSTERS AND READERS AT ONCE never fault the node (no exit 4):
   A = 600,000 (32 articles in flight, the default configuration's
   connections, since the reserve is the packed article), twelve posters racing and four
   readers reading; every POST is offered 340 or refused the memory 440 by
   name, every offered article is accepted, and the node stops cleanly.

    tools/hbox_native.sh --images developer,production . tests.test_native_credits
"""
import socket
import threading
import time
import unittest

from tests.native_harness import EXIT_OK, executable, native_image
from tests.test_native_article_slots import INIT_PROFILE, MEMORY_440, MIB4, SLOTS_4MIB, Poster
from tests.test_native_bounds_join import JoinFixture, article, dot_stuff

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST", "build/fn-host-developer")
POSTERS = 12
READERS = 4
A600K = 600000
DEADLOCK_PROFILE = ("--profile", "development", "--max-transactions", "1024",
                    "--max-history-octets", str(64 << 20),
                    "--max-record-octets", "4199563",
                    "--max-article-octets", str(A600K),
                    "--max-groups-per-article", "16")


class Reader(threading.Thread):
    """GROUP, LISTGROUP, STAT and HEAD in a loop until told to stop; records
    every status line that is not a 2xx/4xx answer of the command asked."""

    def __init__(self, port, stop):
        super().__init__(daemon=True)
        self.port, self.stop, self.bad, self.rounds = port, stop, [], 0

    def ask(self, stream, line):
        stream.write(line + b"\r\n")
        stream.flush()
        status = stream.readline()
        if status[:3] in (b"215", b"211") and line.startswith(b"LISTGROUP"):
            while stream.readline() not in (b".\r\n", b""):
                pass
        elif status[:3] in (b"221",):
            while stream.readline() not in (b".\r\n", b""):
                pass
        return status

    def run(self):
        try:
            conn = socket.create_connection(("127.0.0.1", self.port), timeout=120)
            stream = conn.makefile("rwb")
            stream.readline()
            while not self.stop.is_set():
                for line in (b"GROUP fn.test", b"LISTGROUP fn.test", b"STAT 1", b"HEAD 1"):
                    status = self.ask(stream, line)
                    if not status or status[:1] not in (b"2", b"4"):
                        self.bad.append((line, status))
                self.rounds += 1
            stream.write(b"QUIT\r\n")
            stream.flush()
            conn.close()
        except OSError as error:
            self.bad.append(("socket", repr(error)))


class CreditsTests(JoinFixture):
    def test_the_batch_in_flight_keeps_its_credit_past_the_close(self):
        if not executable(DEVELOPER):
            self.skipTest("{} is required".format(DEVELOPER))
        self.image = DEVELOPER
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=DEVELOPER, env={"FN_NATIVE_OWNER_TEST_BARRIER_MS": "3000"})
        wire = [dot_stuff(article("<credit-{}@example.invalid>".format(n), MIB4 - 4096)) + b".\r\n"
                for n in range(2 + SLOTS_4MIB - 1)]
        a, b = Poster(self.port), Poster(self.port)
        fillers = [Poster(self.port) for _ in range(SLOTS_4MIB - 1)]
        try:
            for n, p in enumerate(fillers, start=2):
                offered = p.ask()
                self.assertTrue(offered.startswith("340"), (n, offered))
                p.stream.write(wire[n][:len(wire[n]) // 2])
                p.stream.flush()
            offered = a.ask()
            self.assertTrue(offered.startswith("340"), offered)
            a.stream.write(wire[0])
            a.stream.flush()
            # A hangs up without waiting for its answer: its batch is in flight.
            time.sleep(0.8)
            a.conn.close()
            time.sleep(0.2)
            during = b.ask()
            print("while A's batch is in flight:", during, flush=True)
            self.assertEqual(during, MEMORY_440)
            self.assertIsNone(owner.poll(), "the node stopped")
            for _ in range(60):
                offered = b.ask()
                if offered != MEMORY_440:
                    break
                time.sleep(0.2)
            self.assertTrue(offered.startswith("340"), offered)
            accepted = b.send(wire[1], pieces=4)
            self.assertTrue(accepted.startswith("240"), accepted)
            for n, p in enumerate(fillers, start=2):
                done = p.send(wire[n][len(wire[n]) // 2:], pieces=2)
                self.assertTrue(done.startswith("240"), (n, done))
            self.assertIsNone(owner.poll(), "the node stopped")
        finally:
            b.close()
            for p in fillers:
                p.close()
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], 2 + SLOTS_4MIB - 1)

    def test_many_large_posters_and_readers_never_fault_the_node(self):
        created = self.op("init", *DEADLOCK_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        stop = threading.Event()
        readers = [Reader(self.port, stop) for _ in range(READERS)]
        for r in readers:
            r.start()
        answers, errors = {}, []

        def post(n):
            try:
                p = Poster(self.port)
                data = dot_stuff(article("<crowd-{}@example.invalid>".format(n), A600K - 4096)) + b".\r\n"
                seen = []
                for _ in range(600):
                    offered = p.ask()
                    seen.append(offered[:3])
                    if offered == MEMORY_440:
                        time.sleep(0.05)
                        continue
                    if not offered.startswith("340"):
                        errors.append((n, "offer", offered))
                        return
                    answers[n] = p.send(data, pieces=3)
                    break
                p.close()
            except OSError as error:
                errors.append((n, "socket", repr(error)))

        posters = [threading.Thread(target=post, args=(n,), daemon=True) for n in range(POSTERS)]
        for t in posters:
            t.start()
        for t in posters:
            t.join(timeout=600)
        stop.set()
        for r in readers:
            r.join(timeout=120)
        print("posters:", sorted(answers.items()), "errors:", errors,
              "reader rounds:", [r.rounds for r in readers], flush=True)
        self.assertIsNone(owner.poll(), "the node stopped (exit {})".format(owner.poll()))
        self.assertEqual(errors, [])
        self.assertEqual(sorted(answers), list(range(POSTERS)))
        self.assertTrue(all(a.startswith("240") for a in answers.values()), answers)
        self.assertEqual([r.bad for r in readers], [[]] * READERS)
        self.node.stop(process=owner)
        self.assertEqual(self.headroom()["transactions-used"], POSTERS)


if __name__ == "__main__":
    unittest.main()
