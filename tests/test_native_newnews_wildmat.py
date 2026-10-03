"""NEWNEWS with a wildmat answers in bounded time while another reader is
served (lane served-live, 2026-10-03; ledger cg-newnews-hang).

On image set 45e05c7fd `NEWNEWS fn.* <date>` gave no answer within 100 s at
12 articles and ran 225 s at ~77% owner CPU at 50, while `NEWNEWS fn.g1`
answered in 7 ms.  The reference scan (books/nntp-responses.lisp
fn-nntp-newnews-scan) read every candidate's payload head for the reclaim
tombstone; on the served path a payload miss discards the line, reads the
one entry off the owner mutex and runs the line again, and the realizer
keeps 8 entries (fn-arx-read-cache-entries), so more than 8 candidates
evicted their own entries on every run and the line never finished.  The
served arm now reads the catalog's tombstone column
(books/served-catalog-dispatch.lisp fn-nntp-newnews-response-cat).

The case posts N articles (FN_NEWNEWS_WILDMAT_N, default 1000) to eight
groups, every fifth cross-posted to a second, and asserts:
  * `NEWNEWS fn.* <yesterday>` answers 230 within ANSWER_SECONDS and lists
    every posted Message-ID exactly once;
  * a second reader, served throughout, never waits more than
    OTHER_SECONDS for a reply while the NEWNEWS is outstanding;
  * `NEWNEWS fn.g1 <yesterday>` lists exactly the articles in fn.g1.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_newnews_wildmat
"""
import os
import threading
import time
import unittest

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
N = int(os.environ.get("FN_NEWNEWS_WILDMAT_N", "1000"))
GROUPS = ["fn.g%d" % i for i in range(8)]
ANSWER_SECONDS = 60
OTHER_SECONDS = 5


def groups_of(i):
    groups = [GROUPS[i % len(GROUPS)]]
    if i % 5 == 0:
        groups.append(GROUPS[(i + 3) % len(GROUPS)])
    return groups


def msgid(i):
    return "<nnw-%06d@wildmat.invalid>" % i


def article(i):
    head = ("From: nnw@wildmat.invalid\r\nNewsgroups: %s\r\nSubject: newnews %d\r\n"
            "Date: Thu, 01 Oct 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (",".join(groups_of(i)), i, msgid(i)))
    return (head + "a body line of a wildmat newnews article.\r\n" * 20).encode("ascii")


def listed(client, command, deadline):
    client.sock.settimeout(max(1.0, deadline - time.monotonic()))
    status = client.command(command)
    ids = []
    if status.startswith(b"230"):
        while True:
            line = client.line()
            if line == b".\r\n":
                break
            ids.append(line.rstrip(b"\r\n").decode("ascii"))
    return status, ids


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeNewnewsWildmat(unittest.TestCase):
    def test_wildmat_newnews_is_bounded_and_others_are_served(self):
        node = Node(self, IMAGE)
        node.operator("init", "--profile", "scale", "--max-article-octets", "4096", *GROUPS)
        owner = node.start()
        since = time.strftime("%Y%m%d %H%M%S", time.gmtime(time.time() - 86400))
        with Client(node.port, timeout=120) as poster:
            for i in range(N):
                first, final = poster.post(article(i))
                self.assertTrue(first.startswith(b"340"), first)
                self.assertTrue(final is not None and final.startswith(b"240"), (i, final))

        other_waits = []
        stop = threading.Event()

        def other_reader():
            with Client(node.port, timeout=OTHER_SECONDS * 4) as other:
                while not stop.is_set():
                    asked = time.monotonic()
                    status = other.command("GROUP fn.g2")
                    other_waits.append(time.monotonic() - asked)
                    if not status.startswith(b"211"):
                        other_waits.append(("status", status))
                        return
                    time.sleep(0.02)

        reader = threading.Thread(target=other_reader)
        with Client(node.port, timeout=ANSWER_SECONDS) as client:
            reader.start()
            try:
                asked = time.monotonic()
                status, ids = listed(client, "NEWNEWS fn.* " + since + " GMT",
                                     asked + ANSWER_SECONDS)
                answered = time.monotonic() - asked
            finally:
                stop.set()
                reader.join(OTHER_SECONDS * 8)
            self.assertTrue(status.startswith(b"230"), status)
            self.assertEqual(sorted(ids), sorted(msgid(i) for i in range(N)))
            self.assertLess(answered, ANSWER_SECONDS)
            status, g1 = listed(client, "NEWNEWS fn.g1 " + since + " GMT",
                                time.monotonic() + ANSWER_SECONDS)
            self.assertTrue(status.startswith(b"230"), status)
            self.assertEqual(sorted(g1), sorted(msgid(i) for i in range(N) if "fn.g1" in groups_of(i)))
        print("NEWNEWS-WILDMAT n={} answered={:.3f}s other-replies={} other-max={:.3f}s".format(
            N, answered, len(other_waits),
            max([w for w in other_waits if isinstance(w, float)] or [0.0])), flush=True)
        self.assertFalse(reader.is_alive(), "the other reader was not served")
        self.assertTrue(other_waits, "the other reader was never answered")
        self.assertTrue(all(isinstance(w, float) and w < OTHER_SECONDS for w in other_waits),
                        other_waits[-5:])
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
