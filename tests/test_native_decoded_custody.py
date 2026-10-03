"""SCN-1129: pending decoded I/O, competing work, cancellation and reopen.

Requires the real default funded pool producer and current decoded controller.
Plain reads or legacy PAGE-IO labels cannot satisfy this selector. Python
transports literal native tokens and compares complete native replies; it does
not implement the decoder, admission or settlement decisions.
"""
import re
import time
import unittest

from tests.native_harness import Client, EXIT, Node, article, keep_diagnostics, native_image, requires
from tools.resilience.adapters.native_cuts import served_matches

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
GROUP = "fn.test"
MID = "<decoded-held@empirical.invalid>"
NEW = "<decoded-competing@empirical.invalid>"
BODY = ("actual decoded hold <&> " + "abcdefghijklmnop" * 4 + "\r\n") * 256


@requires(IMAGE)
class NativeDecodedCustodyTests(unittest.TestCase):
    def wait_event(self, owner, pattern, timeout=120):
        end = time.monotonic() + timeout
        while True:
            self.assertEqual(owner.stderr.dropped, 0, "native trace truncated")
            text = owner.stderr.since(0)
            match = re.search(pattern, text, re.S)
            if match:
                return match
            self.assertIsNone(owner.poll(), owner.diagnostics())
            self.assertLess(time.monotonic(), end, owner.diagnostics())
            time.sleep(0.05)

    def test_held_decoded_read_allows_post_then_cancel_return_release_and_reopen(self):
        nodes = []
        keep_diagnostics(self, nodes)
        node = Node(self, IMAGE, name="decoded-custody")
        nodes.append(node)
        node.operator("init", GROUP, timeout=600, expect=EXIT.OK)
        node.operator("policy", "set", "compress-min-octets", "64", expect=EXIT.OK)
        source = article(MID, groups=GROUP, subject="decoded custody", body=BODY)
        later = article(NEW, groups=GROUP, subject="competing accepted record", body="complete later body\r\n")
        node.start(timeout=600)
        with Client(node.port, timeout=120, greeting=None) as client:
            first, final = client.post(source)
            self.assertTrue((final or first).startswith(b"240 "), (first, final))
            expected = client.article(MID)
            self.assertIsNotNone(expected)
            self.assertTrue(served_matches(expected, source))
        node.stop(expect=EXIT.OK, grace=300)
        report = node.store("compression", expect=EXIT.OK)
        compressed = re.search(rb"compressed-records=(\d+)", report.stdout)
        self.assertIsNotNone(compressed, report.stdout)
        self.assertGreater(int(compressed.group(1)), 0, report.stdout)

        release = node.root / "decoded-physical-release"
        # Cleanup releases our physical hold before attempting owner shutdown.
        self.addCleanup(release.write_bytes, b"cleanup physical hold")
        owner = node.start(timeout=600, env={"FN_NATIVE_PAGE_IO_HOLD": str(release)})
        reader = Client(node.port, timeout=120, greeting=None)
        self.addCleanup(reader.close, False)
        reader.send(("ARTICLE " + MID + "\r\n").encode("ascii"))
        held = self.wait_event(owner, rb"DECODED-WINDOW held token=(\([^\r\n]+\)) file=\d+ fd=\d+ offset=\d+ count=\d+")
        # The exact observed token is opaque transport, never a Python alias.
        token = re.escape(held.group(1))
        wrapped = rb"\s+".join(re.escape(part) for part in held.group(1).split())
        terminal = rb"DECODED-WINDOW (?:physical|release) token=" + wrapped
        self.assertNotRegex(owner.stderr.since(0), terminal)
        with Client(node.port, timeout=120, greeting=None) as writer:
            begun = time.monotonic()
            self.assertTrue(writer.command("DATE").startswith(b"111 "))
            first, final = writer.post(later)
            self.assertTrue((final or first).startswith(b"240 "), (first, final))
            self.assertLess(time.monotonic() - begun, 30, "held decoder blocked independent owner work")
        self.assertNotRegex(owner.stderr.since(0), terminal)
        reader.close(False)
        cancelled = self.wait_event(owner, rb"DECODED-WINDOW cancel token=" + token + rb" word=:CANCELLED")
        self.assertNotRegex(owner.stderr.since(0), terminal)
        release.write_bytes(b"physical read may finish")
        returned = self.wait_event(owner, rb"DECODED-WINDOW read-return token=" + token + rb" status=:OK")
        # Physical and release token prints may wrap, so only whitespace in
        # this exact opaque print is allowed to vary. No missing event inferred.
        physical = self.wait_event(owner, rb"DECODED-WINDOW physical token=" + wrapped + rb"\s+scope=:PARTIAL-FIXED-STORAGE")
        settled = self.wait_event(owner, rb"DECODED-WINDOW release token=" + wrapped + rb"\s+scope=:PARTIAL-FIXED-STORAGE\s+word=:RELEASED")
        self.assertLess(cancelled.start(), returned.start())
        self.assertLess(returned.start(), physical.start())
        self.assertLess(physical.start(), settled.start())
        with Client(node.port, timeout=120, greeting=None) as client:
            self.assertEqual(client.article(MID), expected)
            accepted_later = client.article(NEW)
            self.assertIsNotNone(accepted_later)
            self.assertTrue(served_matches(accepted_later, later))
        node.stop(expect=EXIT.OK, grace=300)
        node.start(timeout=600)
        with Client(node.port, timeout=120, greeting=None) as client:
            self.assertEqual(client.article(MID), expected)
            self.assertEqual(client.article(NEW), accepted_later)
        node.stop(expect=EXIT.OK, grace=300)
