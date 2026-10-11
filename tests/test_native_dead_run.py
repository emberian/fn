"""Post-and-cancel in one group costs the same at the end as at the start, and
GROUP over a cancelled run costs what it costs over none (lane
spans-dead-runs, RED-2, 2026-10-11).

A group's live summary keeps its least and greatest live numbers.  Two walks
crossed the dead numbers between them: a withdrawal of the greatest found the
next one below by probing every number (the reference catalog's
fn-cat$c-scan-down; the paged catalog every image runs reads its link table,
fn-cat$p-prev), and a reader's summary at a view below the count stepped down
number by number from the greatest past every number in X or dead
(books/served-catalog-view.lisp, before this lane).  Both now read the live
list (fn-cat-live-prev, fn-scv-link-down), so neither mentions the run.

The case files D articles (FN_DEAD_RUN_D, default 20000) to fn.dr through a
configured peer, each with an RFC 8315 Cancel-Lock, and cancels every one in
ascending order: a run of D dead numbers.  Then R rounds (FN_DEAD_RUN_R,
default 2000) each post one article to fn.dr above the run and cancel it
(the cancel withdraws the group's greatest, whose live neighbour below is
the run's floor), while a reader repeats GROUP fn.dr and GROUP fn.ctl (a
group with no run) as the views lag the posts.  It asserts:
  * every post and cancel is accepted (235);
  * the mean cancel time over the last 200 rounds is within 2x of the first
    200 (flat per cancel: a scan over the run would grow with nothing, but
    it would cost D probes each round, so also the absolute check below);
  * GROUP fn.dr's p95 is within 2x (plus 2 ms) of GROUP fn.ctl's.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_dead_run
"""
import base64
import hashlib
import os
import threading
import time
import unittest

from tests.native_harness import (
    EXIT_OK, ROOT, Client, Node, environment, executable, native_image, native_peer_add)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
D = int(os.environ.get("FN_DEAD_RUN_D", "20000"))
R = int(os.environ.get("FN_DEAD_RUN_R", "2000"))
WINDOW = 200
KEY = base64.b64encode(hashlib.sha256(b"dead run poster").digest())
LOCK = base64.b64encode(hashlib.sha256(KEY).digest())


def article(message_id, group):
    return (b"From: dr@example.invalid\r\n"
            b"Newsgroups: " + group + b"\r\n"
            b"Subject: dead run\r\n"
            b"Date: Sun, 11 Oct 2026 12:00:00 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n"
            b"Cancel-Lock: sha256:" + LOCK + b"\r\n\r\n"
            b"a dead run body\r\n")


def cancel(message_id, target):
    return (b"From: dr@example.invalid\r\n"
            b"Newsgroups: fn.dr\r\n"
            b"Subject: cmsg cancel " + target + b"\r\n"
            b"Date: Sun, 11 Oct 2026 12:00:01 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n"
            b"Control: cancel " + target + b"\r\n"
            b"Cancel-Key: sha256:" + KEY + b"\r\n\r\n"
            b"cancel\r\n")


def p95(samples):
    ordered = sorted(samples)
    return ordered[min(len(ordered) - 1, int(len(ordered) * 0.95))]


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeDeadRun(unittest.TestCase):
    def ihave(self, peer, message_id, payload):
        first, reply = peer.post(payload, verb="IHAVE " + message_id.decode())
        self.assertTrue(first.startswith(b"335 "), (message_id, first))
        self.assertTrue(reply is not None and reply.startswith(b"235 "), (message_id, reply))

    def test_cancel_and_group_flat_over_a_dead_run(self):
        node = Node(self, IMAGE, listener=False, control=False)
        node.store("init", "fn.dr", "fn.ctl", "control.cancel", expect=EXIT_OK)
        configured = native_peer_add(
            IMAGE, node.store_path, ["source", "source.invalid", "127.0.0.1", "9", "fn.*",
                                     "-", "127.0.0.1", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())
        owner, port = node.start_store_owner(once=False)
        with Client(port, timeout=120) as peer:
            self.ihave(peer, b"<ctl-0@dr.invalid>", article(b"<ctl-0@dr.invalid>", b"fn.ctl"))
            for i in range(D):
                mid = b"<run-%06d@dr.invalid>" % i
                self.ihave(peer, mid, article(mid, b"fn.dr"))
            self.ihave(peer, b"<floor@dr.invalid>", article(b"<floor@dr.invalid>", b"fn.dr"))
            for i in range(D):
                mid = b"<run-%06d@dr.invalid>" % i
                cid = b"<run-c-%06d@dr.invalid>" % i
                self.ihave(peer, cid, cancel(cid, mid))

            stop = threading.Event()
            waits = {"fn.dr": [], "fn.ctl": []}
            errors = []

            def reader():
                try:
                    with Client(port, timeout=30, source="127.0.0.2") as r:
                        while not stop.is_set():
                            for g in ("fn.dr", "fn.ctl"):
                                asked = time.monotonic()
                                status = r.command("GROUP " + g)
                                waits[g].append(time.monotonic() - asked)
                                if not status.startswith(b"211"):
                                    errors.append((g, status))
                                    return
                except Exception as error:
                    errors.append(("exception", repr(error)))

            thread = threading.Thread(target=reader)
            thread.start()
            cancels = []
            try:
                for i in range(R):
                    mid = b"<top-%06d@dr.invalid>" % i
                    cid = b"<top-c-%06d@dr.invalid>" % i
                    self.ihave(peer, mid, article(mid, b"fn.dr"))
                    asked = time.monotonic()
                    self.ihave(peer, cid, cancel(cid, mid))
                    cancels.append(time.monotonic() - asked)
            finally:
                stop.set()
                thread.join(60)
        self.assertFalse(thread.is_alive(), "the reader did not stop")
        self.assertFalse(errors, errors[:3])
        first = sum(cancels[:WINDOW]) / WINDOW
        last = sum(cancels[-WINDOW:]) / WINDOW
        dr, ctl = p95(waits["fn.dr"]), p95(waits["fn.ctl"])
        print("DEAD-RUN d={} r={} cancel-first={:.4f}s cancel-last={:.4f}s group-dr-p95={:.4f}s "
              "group-ctl-p95={:.4f}s groups={}".format(D, R, first, last, dr, ctl,
                                                       len(waits["fn.dr"])), flush=True)
        self.assertLess(last, 2 * first, "per-cancel cost grew over the rounds")
        self.assertTrue(waits["fn.dr"] and waits["fn.ctl"], "the reader was never answered")
        self.assertLess(dr, 2 * ctl + 0.002, "GROUP over the dead run costs more than without one")
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
