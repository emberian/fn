"""LIST ACTIVE reads each group at its hold's view while posters append
(lane spans-list-hold, 2026-10-11; Codex F1 on lane/spans-newnews).

Before this lane a LIST cursor kept the view it captured at the command for
the whole reply, and every group visit corrected the catalog's live summary
back to that view by walking every row appended since
(books/served-catalog-view.lisp fn-scv-x): N appends during a LIST meant N
iterations inside each owner hold.  The host now refreshes the LIST cursor
to the view its hold reads at (books/served-query-plan.lisp
fn-qplan-refresh), so the correction covers at most the batches in flight.

The case creates G groups (FN_LIST_FLOOD_GROUPS, default 3000), seeds the
last ten, starts a poster appending N articles (FN_LIST_FLOOD_N, default
2000) to those ten, then sends `LIST ACTIVE` with a small receive window and
reads it one line at a time with a pause.  It asserts:
  * the LIST completes with exactly G group lines and the terminator;
  * a late group shows a high more than one batch above what was posted
    to it when LIST was sent (the view moved: the tooth, false under a view
    fixed at the command);
  * every line's high is at most the number of articles posted to it;
  * a second reader's GROUP replies stay under OTHER_SECONDS throughout.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_list_flood
"""
import os
import socket
import threading
import time
import unittest

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
G = int(os.environ.get("FN_LIST_FLOOD_GROUPS", "3000"))
N = int(os.environ.get("FN_LIST_FLOOD_N", "2000"))
GROUPS = ["fn.lf%03d" % i for i in range(G)]
LATE = GROUPS[-10:]
ANSWER_SECONDS = 300
OTHER_SECONDS = 5
PAUSE = 0.01
RCVBUF = 4096


def article(tag, i, group):
    head = ("From: lf@flood.invalid\r\nNewsgroups: %s\r\nSubject: flood %s %d\r\n"
            "Date: Thu, 01 Oct 2026 12:00:00 +0000\r\nMessage-ID: <lf-%s-%06d@flood.invalid>\r\n\r\n"
            % (group, tag, i, tag, i))
    return (head + "a body line of a list flood article.\r\n" * 4).encode("ascii")


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeListFlood(unittest.TestCase):
    def test_list_reads_each_group_at_its_hold_view(self):
        node = Node(self, IMAGE)
        node.operator("init", "--profile", "scale", "--max-article-octets", "4096", *GROUPS)
        owner = node.start()
        posted = {g: 0 for g in GROUPS}
        with Client(node.port, timeout=120) as poster:
            for i, g in enumerate(LATE):
                first, final = poster.post(article("seed", i, g))
                self.assertTrue(final is not None and final.startswith(b"240"), (g, final))
                posted[g] += 1

        stop = threading.Event()
        flood_started = threading.Event()
        flood_errors = []
        other_waits = []

        def flood():
            try:
                with Client(node.port, timeout=120) as p:
                    for i in range(N):
                        if stop.is_set():
                            return
                        g = LATE[i % len(LATE)]
                        first, final = p.post(article("flood", i, g))
                        if final is None or not final.startswith(b"240"):
                            flood_errors.append((i, final))
                            return
                        posted[g] += 1
                        flood_started.set()
            except Exception as error:  # reported to the test thread
                flood_errors.append(("exception", repr(error)))

        def other_reader():
            try:
                with Client(node.port, timeout=OTHER_SECONDS * 4) as other:
                    while not stop.is_set():
                        asked = time.monotonic()
                        status = other.command("GROUP " + GROUPS[0])
                        other_waits.append(time.monotonic() - asked)
                        if not status.startswith(b"211"):
                            other_waits.append(("status", status))
                            return
                        time.sleep(0.02)
            except Exception as error:  # a timeout is a failed wait, not a missing sample
                other_waits.append(("exception", repr(error)))

        lines = []
        with Client(node.port, timeout=ANSWER_SECONDS) as client:
            poster_thread = threading.Thread(target=flood)
            reader = threading.Thread(target=other_reader)
            # A small receive window keeps the reply from being rendered
            # whole into socket buffers before the flood moves the view.
            client.sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, RCVBUF)
            reader.start()
            poster_thread.start()
            self.assertTrue(flood_started.wait(60), "the flood never posted")
            asked = time.monotonic()
            status = client.command("LIST ACTIVE")
            self.assertTrue(status.startswith(b"215"), status)
            # Read after the 215: the command's view was captured before it,
            # and the one serial poster has at most one post in flight, so
            # the command's view holds no more than this plus one per group.
            at_command = dict(posted)
            try:
                while True:
                    line = client.line()
                    if line == b".\r\n":
                        break
                    lines.append(line.rstrip(b"\r\n").decode("ascii"))
                    time.sleep(PAUSE)
                answered = time.monotonic() - asked
            finally:
                stop.set()
                poster_thread.join(120)
                reader.join(OTHER_SECONDS * 8)
        self.assertFalse(poster_thread.is_alive(), "the poster did not stop")
        self.assertFalse(reader.is_alive(), "the other reader did not stop")
        self.assertFalse(flood_errors, flood_errors[:3])
        self.assertEqual(len(lines), G, "LIST did not give exactly one line per group")
        highs = {}
        for line in lines:
            name, high, low, _status = line.split(" ")
            highs[name] = int(high)
        self.assertEqual(sorted(highs), sorted(GROUPS))
        self.assertLess(answered, ANSWER_SECONDS)
        for g in GROUPS:
            self.assertLessEqual(highs[g], posted[g], g)
        # A batch (64 records by default) may be durable at the command
        # before its 240s reached the poster; more than that is movement.
        moved = [g for g in LATE if highs[g] > at_command[g] + 64]
        print("LIST-FLOOD groups={} n={} answered={:.3f}s moved={} other-replies={} other-max={:.3f}s".format(
            G, N, answered, len(moved), len(other_waits),
            max([w for w in other_waits if isinstance(w, float)] or [0.0])), flush=True)
        self.assertTrue(moved, "every late group was read at the command's view")
        self.assertTrue(other_waits, "the other reader was never answered")
        self.assertTrue(all(isinstance(w, float) and w < OTHER_SECONDS for w in other_waits),
                        other_waits[-5:])
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
