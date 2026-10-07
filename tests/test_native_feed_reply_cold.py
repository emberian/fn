"""A peer feed reply whose article is not in memory does not hold the owner
(lane feed-reply-cold, 2026-10-07; repair item
LOCK-R2-FEED-REPLY-PAYLOAD-PREAD).

A peer's 238/335 makes the owner read the article's payload.  That read used
to be a synchronous pread inside the feed's owner quantum, holding the owner
mutex and the extent mutex for as long as the disk took.  Now ACL2's pure
probe (fn-owner-feed-reply-article) reads it first with the extent realizer
in its no-I/O mode; a cold extent is issued and awaited holding neither lock
(host/native/owner.lisp fnn-owner-feed-reply-probe-locked, host/native/
feed-service.lisp fnn-feed-reply-step), then the reply is committed warm.

The case stores an article while the peer refuses connections, restarts the
node over it with the pread stalled (FN_NATIVE_TEST_READ_STALL_FILE), and lets
the peer answer 238 to the CHECK.  While that article read is stalled the
owner must still answer other clients (a greeting and DATE each, within
OTHER_SECONDS: the owner mutex is free).  Released, the peer receives the
article byte for byte.

Red before the change (the owner answers nothing while the pread is stalled),
green after: owed on a developer image (FN_NATIVE_DEVELOPER_HOST) built from
this change.
"""
import threading
import time
import unittest

from tests.native_harness import EXIT_OK, Client, Node, executable, native_image, scratch
from tests.test_native_peer_hostile_feed import GROUP, StreamingPeer, article

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
OTHERS = 6
OTHER_SECONDS = 1.5
DELIVERY_SECONDS = 120


class RefusingPeer(StreamingPeer):
    """A streaming peer that, while `down', drops every dial unanswered."""

    down = True

    def session(self, client, number):
        if self.down:
            client.close()
            return
        super().session(client, number)


@unittest.skipUnless(executable(DEVELOPER), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeFeedReplyColdTests(unittest.TestCase):
    def test_owner_answers_others_while_a_feed_reply_article_read_is_stalled(self):
        gate = threading.Event()
        peer = RefusingPeer(lambda mid, n: (gate.wait(120), "238 " + mid)[1],
                            lambda mid: ["239 " + mid])
        self.addCleanup(peer.close)
        base = scratch(self, "fn-feed-reply-cold-")
        node = Node(self, DEVELOPER, root=base / "source", name="feed-reply-cold")
        node.store("init", GROUP, expect=EXIT_OK)
        node.operator("peer", "add", "stranger", "stranger.example.invalid", "127.0.0.1",
                      str(peer.port), "-", "fn.*", "127.0.0.1", "true", expect=EXIT_OK)
        owner = node.start()
        message_id = "<feed-reply-cold@example.invalid>"
        body = article(message_id, "feed-reply-cold")
        node.post(message_id, body, group=GROUP, expect=EXIT_OK)
        deadline = time.monotonic() + 60
        while peer.connections < 1 and time.monotonic() < deadline:
            time.sleep(0.2)
        self.assertGreaterEqual(peer.connections, 1, "the feed never dialled the refusing peer")
        node.stop(process=owner)

        stall = node.root / "readstall"
        self.addCleanup(lambda: stall.unlink() if stall.exists() else None)
        peer.down = False
        owner = node.start(env={"FN_NATIVE_TEST_READ_STALL_FILE": str(stall)})
        with node.log_on_failure(owner):
            stall.write_bytes(b"")
            gate.set()
            deadline = time.monotonic() + 60
            while peer.checks.get(message_id, 0) < 1 and time.monotonic() < deadline:
                time.sleep(0.2)
            self.assertGreaterEqual(peer.checks.get(message_id, 0), 1,
                                    "the restarted feed never offered the stored article")
            time.sleep(1.0)  # the 238 has arrived; its article read is stalled
            waits = []
            for _ in range(OTHERS):
                started = time.monotonic()
                with Client(node.port, timeout=30) as other:
                    self.assertTrue(other.command("DATE").startswith(b"111"))
                waits.append(round(time.monotonic() - started, 3))
            print("FEED-REPLY-COLD waits={}".format(waits), flush=True)
            self.assertIsNone(peer.await_article(message_id, 0.0),
                              "the article was sent while its read was stalled")
            self.assertTrue(all(w < OTHER_SECONDS for w in waits), waits)
            stall.unlink()
            got = peer.await_article(message_id, DELIVERY_SECONDS)
            self.assertIsNotNone(got, "the stalled article never reached the peer")
            self.assertIn(b"feed-reply-cold body", got)
            node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
