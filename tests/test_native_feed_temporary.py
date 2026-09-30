"""PKT-599(d): a temporary MODE STREAM 400 backs off, then feeds on retry."""
import json
import time
import unittest

from tests import test_native_peering as peer
from tools.wire_stream import whole_stream


class TemporaryModePeer(peer.ScriptedTransitPeer):
    def __init__(self, refusals):
        self.refusals = refusals
        self.arrivals = []
        super().__init__("203 streaming permitted")

    def session(self, client, number):
        with self.lock:
            self.arrivals.append(time.monotonic())
        if number > self.refusals:
            return super().session(client, number)
        with client:
            client.settimeout(10)
            stream = whole_stream(client)
            stream.write(b"200 scratch temporarily unavailable peer\r\n")
            line = stream.readline()
            with self.lock:
                self.commands.append((number, line.decode("ascii", "replace").strip()))
            if line != b"MODE STREAM\r\n":
                return
            stream.write(b"400 temporarily unavailable\r\n")


@unittest.skipUnless(peer.READY, "set explicit native image/source and matching hashes")
class NativeFeedTemporaryTests(unittest.TestCase):
    setUp = peer.NativePeeringTests.setUp
    initialize = peer.NativePeeringTests.initialize
    start = peer.NativePeeringTests.start
    process_identity = peer.NativePeeringTests.process_identity
    verify_process_identity = peer.NativePeeringTests.verify_process_identity
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post

    def test_temporary_mode_refusals_back_off_and_then_deliver(self):
        scripted = TemporaryModePeer(3)
        self.addCleanup(scripted.close)
        source = self.initialize("temporary-source")
        target = type("Target", (), {"name": "temporary", "port": scripted.port})()
        peer.NativePeeringTests.configure_peer(self, source, target)
        self.start(source)
        message_id = "<temporary-mode@example.invalid>"
        self.post(source, message_id, "temporary-mode")
        got = scripted.await_article(message_id, timeout=40)
        with scripted.lock:
            commands, arrivals = list(scripted.commands), list(scripted.arrivals)
        diagnostics = {"commands": commands, "arrivals": arrivals,
                       "owner_exit": source.process.poll(),
                       "stderr": source.process.stderr.tail().decode("utf-8", "replace")}
        self.assertIsNotNone(got, json.dumps(diagnostics, sort_keys=True))
        self.assertEqual(got[0], "TAKETHIS")
        self.assertIn(b"\r\ntemporary-mode\r\n", got[1])
        self.assertEqual(len(arrivals), 4, diagnostics)
        gaps = [b-a for a,b in zip(arrivals, arrivals[1:])]
        # peer add's backoff is 1000 ms. Permit scheduler/clock resolution while
        # still detecting immediate retries or a constant delay after 400.
        for gap, minimum in zip(gaps, (0.8, 1.8, 3.8)):
            self.assertGreaterEqual(gap, minimum, diagnostics)
        self.assertEqual([command for n,command in commands if n <= 3],
                         ["MODE STREAM"] * 3, diagnostics)
        self.assertEqual([(n,command) for n,command in commands if n == 4],
                         [(4,"MODE STREAM"),(4,"CHECK " + message_id),
                          (4,"TAKETHIS " + message_id)], diagnostics)
        self.assertNotIn("stopped reason=mode-stream-refused", diagnostics["stderr"])
        self.assertIsNone(source.process.poll(), diagnostics)
        print("NATIVE-FEED-TEMPORARY-WITNESS " + json.dumps({
            "commands": commands, "retry_gaps": gaps, "identity": source.identities[-1],
            "source": peer.SOURCE}, sort_keys=True), flush=True)
