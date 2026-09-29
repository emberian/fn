"""A held cursor response excludes catalog replacement until drain/cancel.

The productive expiry fixture leaves two reclaimable articles and three
retained articles.  Pausing after a cursor quantum, off the owner mutex,
exercises the real swap's :readers refusal.  Releasing or cancelling the
response settles the pin and the same real reclaim then installs.
"""
import re
import time
import unittest

from tests.native_harness import Client, EXIT, native_image, requires
from tests import test_native_expiry as expiry

GROUP, msgid = expiry.GROUP, expiry.msgid

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
class NativeOverPinsTests(unittest.TestCase):
    image = IMAGE
    # Reuse the existing productive fixture without inheriting its tests.
    setUp = expiry.ExpiryMixin.setUp
    node = expiry.ExpiryMixin.node
    post_all = expiry.ExpiryMixin.post_all
    filled = expiry.ExpiryMixin.filled
    reclaim = expiry.ExpiryMixin.reclaim
    owner_lines = expiry.ExpiryMixin.owner_lines
    recorded_base = expiry.DeveloperExpiryTests.recorded_base
    copy_of = expiry.DeveloperExpiryTests.copy_of

    def held_response(self, cancel):
        node = self.copy_of(self.recorded_base(), "held-over")
        stall = self.root / "over-stall"
        stall.touch()
        owner = node.start(timeout=600, env={
            "FN_NATIVE_OVER_WINDOW": "1",
            "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM": str(stall),
        })
        client = Client(node.port, timeout=300, greeting=None)
        try:
            self.assertTrue(client.command("GROUP " + GROUP).startswith(b"211 5 "))
            # Both OVER replies belong to the captured plan when pipelined;
            # STAT follows their complete bodies, never an error in a body.
            client.send(("OVER 1-100\r\nXOVER 1-100\r\nSTAT %s\r\n" % msgid("p0")).encode())
            held = self.owner_lines(owner, re.compile(rb"OVER quantum-held cid="), 1)
            self.assertEqual(len(held), 1, owner.stderr.since(0)[-3000:])
            refused = self.reclaim(node, "--recorded", expect=None)
            self.assertNotIn(b"installed", refused.stdout, refused.stdout)
            deferred = self.owner_lines(owner, re.compile(rb"RECLAIM deferred reason=readers"), 1)
            self.assertEqual(len(deferred), 1, owner.stderr.since(0)[-3000:])
            if cancel:
                client.close(False)
            stall.unlink()
            if not cancel:
                replies = []
                for _ in range(2):
                    self.assertTrue(client.line().startswith(b"224 "))
                    rows = []
                    while True:
                        line = client.line()
                        if line == b".\r\n":
                            break
                        rows.append(line)
                    self.assertEqual([int(row.split(b"\t", 1)[0]) for row in rows], [1, 2, 3, 4, 5])
                    replies.append(rows)
                self.assertEqual(replies[0], replies[1])
                self.assertTrue(client.line().startswith(b"223 "))
                client.close()
            # Synchronize with the connection loop's cancellation cleanup:
            # retry only the named :readers refusal, with a bounded deadline.
            deadline = time.monotonic() + 30
            while True:
                done = self.reclaim(node, "--recorded", expect=None)
                if b"installed" in done.stdout:
                    break
                self.assertLess(time.monotonic(), deadline, (done.stdout, owner.stderr.since(0)[-3000:]))
                time.sleep(0.05)
            self.assertEqual(done.returncode, EXIT.OK, done.stderr)
            with Client(node.port, timeout=300, greeting=None) as replacement:
                self.assertTrue(replacement.command("STAT " + msgid("p0")).startswith(b"430 article reclaimed"))
                self.assertTrue(replacement.command("STAT " + msgid("n0")).startswith(b"223 "))
        finally:
            stall.unlink(missing_ok=True)
            client.close(False)
            node.stop(expect=None, grace=300)

    def test_pipelined_over_drain_preserves_old_reply_then_reclaim_installs(self):
        self.held_response(False)

    def test_cancelled_over_settles_ownership_before_reclaim_installs(self):
        self.held_response(True)

    def test_sparse_quanta_retain_pipeline_and_hold_until_complete_reply(self):
        base = self.node("sparse-base")
        self.post_all(base, [("n0", GROUP, None, 0)] +
                      [("gap%d" % n, GROUP, expiry.PAST, 0) for n in range(32)] +
                      [("f0", GROUP, expiry.FUTURE, 0)])
        base.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
        reclaimed = self.reclaim(base)
        self.assertIn(b"reclaimed=32", reclaimed.stdout)
        replies = []
        for name, window in (("sparse-small", "1"), ("sparse-whole", "100000000")):
            node = self.copy_of(base, name)
            owner = node.start(timeout=600, env={
                "FN_NATIVE_OVER_WINDOW": window,
                # A nonexistent pause path enables ownership diagnostics;
                # this native exercises normal scheduling, without a stall.
                "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM": str(self.root / "absent-stall"),
            })
            try:
                with Client(node.port, timeout=300, greeting=None) as client:
                    self.assertTrue(client.command("GROUP " + GROUP).startswith(b"211 2 "))
                    at = len(owner.stderr.since(0))
                    client.send(("OVER 1-34\r\nSTAT %s\r\n" % msgid("f0")).encode())
                    status = client.line()
                    self.assertTrue(status.startswith(b"224 "), status)
                    rows = []
                    while True:
                        line = client.line()
                        if line == b".\r\n":
                            break
                        rows.append(line)
                    self.assertEqual([int(row.split(b"\t", 1)[0]) for row in rows], [1, 34])
                    self.assertTrue(client.line().startswith(b"223 "))
                    replies.append((status, rows))
                if window == "1":
                    log = owner.stderr.since(0)[at:]
                    yielded = re.search(rb"OVER empty-yield cid=(\d+)", log)
                    self.assertIsNotNone(yielded, log[-3000:])
                    settled = rb"OVER response-settled cid=" + yielded.group(1) + rb" status=released"
                    self.assertRegex(log[yielded.end():], settled)
            finally:
                node.stop(expect=None, grace=300)
        self.assertEqual(replies[0], replies[1])

    def test_service_stop_settles_a_paused_response(self):
        node = self.copy_of(self.recorded_base(), "stop-over")
        stall = self.root / "over-stop-stall"
        stall.touch()
        owner = node.start(timeout=600, env={
            "FN_NATIVE_OVER_WINDOW": "1",
            "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM": str(stall),
        })
        client = Client(node.port, timeout=300, greeting=None)
        try:
            self.assertTrue(client.command("GROUP " + GROUP).startswith(b"211 5 "))
            client.send(b"OVER 1-100\r\n")
            self.assertEqual(len(self.owner_lines(owner, re.compile(rb"OVER quantum-held cid="), 1)), 1)
            # Stop breaks the off-mutex pause even though the selector stays
            # present, and the mux unwind must release the captured response.
            node.stop(grace=300)
            log = owner.stderr.since(0)
            held = re.search(rb"OVER quantum-held cid=(\d+)", log)
            self.assertIsNotNone(held, log[-3000:])
            self.assertIn(b"OVER response-settled cid=" + held[1] + b" status=released", log[held.end():])
        finally:
            stall.unlink(missing_ok=True)
            client.close(False)
            if owner.poll() is None:
                node.stop(expect=None, grace=300)
