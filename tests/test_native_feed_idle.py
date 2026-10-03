"""S145: an idle outbound feed does not enter the owner gate twenty times a
second, and a new article still leaves at once (lane served-live,
2026-10-03; ledger S145, acceptance services:idle-wait).

The worker used to poll every 50 ms whatever it had to do: each round
refreshed the peer list and ticked each ready link under the owner mutex,
about 20 x (1 + links) transit holds a second while idle.  Now an idle
worker sleeps on the owner's commit signal, its sleep growing to a second
(host/native/feed-service.lisp fnn-feed-idle-wait).  With one ready peer and
IDLE seconds of nothing to send, the owner's own account of its holds
(FN_OWNER_MEASURE=1: label other) stays under HOLD_LIMIT; an article
posted after the idle stretch reaches the peer within DELIVER_SECONDS (the
commit wakes the worker).  Before the change the idle stretch alone was
about 40 transit holds a second.
"""
import json
import re
import time
import unittest

from tests import test_native_peering as peer

IDLE = 10
HOLD_LIMIT = 150
DELIVER_SECONDS = 3
MEASURE = re.compile(rb"fn-owner-measure (\S+) holds=(\d+)")


@unittest.skipUnless(peer.READY, "set explicit native image/source and matching hashes")
class NativeFeedIdleTests(unittest.TestCase):
    setUp = peer.NativePeeringTests.setUp
    initialize = peer.NativePeeringTests.initialize
    process_identity = peer.NativePeeringTests.process_identity
    verify_process_identity = peer.NativePeeringTests.verify_process_identity
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post

    def test_idle_feed_sleeps_and_a_commit_wakes_it(self):
        scripted = peer.ScriptedTransitPeer("203 streaming permitted")
        self.addCleanup(scripted.close)
        source = self.initialize("idle-source")
        target = type("Target", (), {"name": "idle", "port": scripted.port})()
        peer.NativePeeringTests.configure_peer(self, source, target)
        owner = source.start(env={"FN_OWNER_MEASURE": "1"})
        self.verify_process_identity(source)
        first = "<feed-idle-1@example.invalid>"
        self.post(source, first, "feed-idle-1")
        self.assertIsNotNone(scripted.await_article(first, timeout=40))
        time.sleep(IDLE)
        second = "<feed-idle-2@example.invalid>"
        self.post(source, second, "feed-idle-2")
        posted = time.monotonic()
        got = scripted.await_article(second, timeout=40)
        delivered = time.monotonic() - posted
        self.assertIsNotNone(got)
        source.stop(process=owner)
        holds = {m.group(1).decode(): int(m.group(2))
                 for m in MEASURE.finditer(owner.stderr.since(0))}
        print("NATIVE-FEED-IDLE-WITNESS " + json.dumps(
            {"idle_seconds": IDLE, "holds": holds, "deliver_seconds": round(delivered, 3)},
            sort_keys=True), flush=True)
        # The feed's quanta carry no label of their own (FN_OWNER_MEASURE's
        # default, other); the run's few posts are control.  On 45e05c7fd:
        # other=506 over this run (about 40 a second while idle).
        self.assertLess(holds.get("other", 0) + holds.get("transit", 0), HOLD_LIMIT, holds)
        self.assertLess(delivered, DELIVER_SECONDS)


if __name__ == "__main__":
    unittest.main()
