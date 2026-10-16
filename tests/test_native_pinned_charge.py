"""PIN charge from the node's capacity sentences, including a real reclaim.

The exercised core entries are fn-owner-memory-run-cfg and its called pure fn-owner-memory-run-cfg-of,
fn-adm-pinned-cfg-charges-every-stored-article, fn-hist-stored-most-carried, and
fn-owner-apply-limit-profile (whose logical transition is fn-osb-install). No memory figure comes from Python accounting.
"""
import os
from pathlib import Path
import re
import tempfile
import time
import unittest

from tests.native_harness import Client, EXIT, Node, ROOT, durable_root, native_image, requires

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
CAPACITY = re.compile(rb"(?:memory capacity=|refused memory-cannot-hold-the-store capacity=)[^\r\n]* large=(\d+)")


class PinnedChargeSourceTests(unittest.TestCase):
    def test_capacity_sentences_include_the_core_large_term(self):
        from tests.campaign.native_cuts import host_function
        source = (ROOT / "books/admission-memory.lisp").read_text()
        for name in ("fn-adm-capacity-line", "fn-adm-installed-capacity-line"):
            body = host_function(source, name)
            self.assertIn('" MB large="', body)
            self.assertIn("(fn-heap-decimal (fn-mm-large-reply profile cfg))", body)

    def test_reclaim_prints_after_the_committed_swap_and_refresh(self):
        from tests.campaign.native_cuts import host_function
        body = host_function((ROOT / "host/native/owner.lisp").read_text(), "fnn-owner-reclaim-pass")
        self.assertLess(body.index("'fn-owner-orcp-swap"), body.index("'fn-owner-memory-reclaim-complete"))
        self.assertLess(body.index("'fn-owner-memory-reclaim-complete"), body.index("(fnn-owner-memory-print-capacity)"))


@requires(DEVELOPER)
class NativePinnedChargeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="pinned-charge-", dir=durable_root())
        self.addCleanup(self.directory.cleanup)
        self.node = Node(self, DEVELOPER, root=Path(self.directory.name),
                         extra='[resources]\nreclaim_live = true\n[auth]\nrequired = false\nprotected_only = false\n')
        self.node.store("init", "--profile", "development", "--max-article-octets", "65536",
                        "--max-groups-per-article", "1", "--max-group-name-octets", "64",
                        "--max-header-fields", "32", "--max-header-lines", "32",
                        "--max-header-octets", "256", "fn.test", expect=EXIT.OK)
        self.reader = None
        self.capacity_cursor = 0
        self.addCleanup(self.close_reader)

    def start(self, expected=132096):
        self.capacity_cursor = 0
        owner = self.node.start(env={"SBCL_USER_ARGS": "--dynamic-space-size 4096",
                                     "FN_NATIVE_MEMORY_CAPACITY": "1"})
        pidfile = self.node.root / f"pinned-charge-owner-{owner.pid}.pid"
        pidfile.write_text(str(owner.pid) + "\n")
        # All harness cleanup signals read the PID recorded for this exact child.
        def recorded_signal(number):
            pid = int(pidfile.read_text())
            self.assertEqual(pid, owner.process.pid)
            if owner.process.poll() is None:
                try:
                    os.kill(pid, number)
                except ProcessLookupError:
                    pass
        owner.signal = recorded_signal
        self.capacity(expected)
        return owner

    def close_reader(self):
        if self.reader is not None:
            self.reader.close()
            self.reader = None

    def capacity(self, expected):
        target = str(expected).encode()
        def latest_matches(text):
            lines = CAPACITY.findall(text)
            return len(text) if len(lines) > self.capacity_cursor and lines[-1] == target else None
        self.node.process.stderr.wait_for(latest_matches, 0, time.monotonic() + 10)
        lines = CAPACITY.findall(self.node.process.stderr.since(0))
        self.assertGreater(len(lines), self.capacity_cursor, self.node.process.stderr.since(0)[-4000:])
        self.assertEqual(lines[-1], str(expected).encode(), self.node.process.stderr.since(0)[-4000:])
        self.capacity_cursor = len(lines)

    def mark_capacity(self):
        self.capacity_cursor = len(CAPACITY.findall(self.node.process.stderr.since(0)))

    def shrink(self):
        self.mark_capacity()
        result = self.node.operator("policy", "set", "max-article-octets", "10240", expect=EXIT.OK)
        self.assertIn(b"applied limit max-article-octets=10240", result.stdout + result.stderr)

    def record_shrink(self):
        # books/limits-live.lisp fn-lim-article-decision (2675f2609): a changed
        # max-article-octets is durable intent for the next start, never live.
        result = self.node.operator("policy", "set", "max-article-octets", "10240", expect=EXIT.OK)
        self.assertIn(b"recorded limit max-article-octets=10240 effective-at-next-start",
                      result.stdout + result.stderr)

    def refresh(self):
        self.mark_capacity()
        self.node.operator("policy", "set", "posting-policy", "open", expect=EXIT.OK)

    @unittest.skip("PIN-LIVE-APPLY-CAPACITY: waiting on A28 transition/locking statement; and " + "PIN-LIVE-A: fn-lim-article-decision (books/limits-live.lisp, 2675f2609) records every max-article-octets change for the next start, so no live connection holds a pin above the served A")
    def test_retained_64k_reader_is_charged_after_live_shrink(self):
        self.start()
        self.reader = Client(self.node.port)
        self.shrink()
        self.capacity(132096)

    @unittest.skip("PIN-LIVE-A: fn-lim-article-decision (books/limits-live.lisp, 2675f2609) records every max-article-octets change for the next start, so no live connection holds a pin above the served A")
    def test_closing_the_last_large_pin_restores_the_10k_term(self):
        self.start()
        self.reader = Client(self.node.port)
        self.shrink()
        self.refresh()
        self.capacity(132096)
        self.close_reader()
        self.refresh()
        self.capacity(21504)

    def test_60k_stored_article_keeps_the_charge_until_real_reclaim(self):
        message_id = "<pin60@example.invalid>"
        header = ("From: p@example.invalid\r\nNewsgroups: fn.test\r\nSubject: pin\r\n"
                  "Message-ID: " + message_id + "\r\n"
                  "Expires: Mon, 01 Jan 2024 00:00:00 +0000\r\n\r\n").encode()
        remaining = 61440 - len(header) - 2
        body = b"x" * 76 + b"\r\n"
        payload = header + body * (remaining // len(body)) + b"x" * (remaining % len(body)) + b"\r\n"
        self.assertEqual(len(payload), 61440)
        self.start()
        self.node.post(message_id, payload, expect=EXIT.OK)
        # MOST charges the STORED octets (fn-adm-stored-article-most over
        # fn-hf-octets): the posted payload plus the headers the node adds at
        # injection. The overview's Bytes field (RFC 3977 8.3.1) is that size;
        # ARTICLE is not, because it also carries the serve-time Xref line.
        with Client(self.node.port) as client:
            status_line, overview = client.multiline(b"OVER " + message_id.encode())
        self.assertTrue(status_line.startswith(b"224"), status_line)
        stored = int(overview.split(b"\t")[6])
        self.assertGreater(stored, len(payload))
        status = 132096 - 2 * 65536
        self.node.operator("retention", "expire", "fn.test", "purge", "30", expect=EXIT.OK)
        self.record_shrink()
        self.node.stop()
        # The owner starts at A=10240 over a store that still holds the 60k
        # article: stored MOST, not A, sets the large term.
        self.start(2 * stored + status)
        self.mark_capacity()
        result = self.node.operator("store", "reclaim", expect=EXIT.OK, timeout=120)
        self.assertIn(b"reclaim installed", result.stdout + result.stderr)
        # A live node's reply carries the receipt; the owner's install line
        # carries the count (as tests/test_native_expiry.py reads it).
        installed = re.compile(rb"RECLAIM installed records=[^\r\n]*")
        self.node.process.stderr.wait_for(
            lambda text: len(text) if installed.search(text) else None, 0, time.monotonic() + 30)
        line = installed.findall(self.node.process.stderr.since(0))
        self.assertEqual(len(line), 1, self.node.process.stderr.since(0)[-3000:])
        self.assertIn(b"reclaimed=1", line[0], line)
        self.capacity(21504)
        with Client(self.node.port) as client:
            self.assertTrue(client.command("STAT " + message_id).startswith(b"430 article reclaimed"))
