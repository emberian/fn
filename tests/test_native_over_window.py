"""OVER over a 100,000-article group, rendered one bounded quantum at a time
(lane join-f2-13, 2026-09-29; PRF-1020, PKT-733 (4), D27).

The served step answers an OVER/XOVER range with a CURSOR (books/served-
catalog.lisp fn-nntp-over-range-ovw: the range parsed and clamped once, no
number probed); the host's render loop runs one quantum of it under the
owner mutex per window the socket takes (books/served-plan-cursor.lisp
fn-splan-cursor-step; host/native/owner.lisp fnn-owner-cursor-step,
host/native/mux.lisp), at most W numbers per hold.  The keystone
fn-splan-cw-drain-is-the-expanded-reply says the bytes are the same for
every W; this module is the evidence the native host obeys it at scale: the
whole range of the synthetic 100,000-article store (tools/synth_log_store.py's
syn100k-2k, the fixture tests/test_native_open_depth.py serves) is read under
a SMALL quantum (FN_NATIVE_OVER_WINDOW, a developer-image selector; default
97: over a thousand holds of the mutex) and under one that holds the range
whole, and the two replies are byte-identical, one row per article, in
order, from the group's low to its high.

    FN_OPEN_DEPTH_FIXTURES=/tank/fn/scratch/fixtures FN_NATIVE_DEVELOPER_HOST=... \\
        python3 -m unittest tests.test_native_over_window

Skipped without the fixture directory or the developer image (the selector
is refused by a production image, as it should be).
"""
import os
import shutil
import tempfile
import time
import unittest
from pathlib import Path

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
FIXTURES = os.environ.get("FN_OPEN_DEPTH_FIXTURES")
# The largest synthetic store the fixture directory holds (syn100k-2k when it
# has been built; hbox holds n10k-2k, 10,000 articles: over a hundred quanta
# at the default small window), or FN_OVER_WINDOW_FIXTURE.
CANDIDATES = ("syn100k-2k", "n10k-2k")
NAME = os.environ.get("FN_OVER_WINDOW_FIXTURE") or next(
    (n for n in CANDIDATES if FIXTURES and (Path(FIXTURES) / n / "store").is_dir()), CANDIDATES[0])
SMALL = os.environ.get("FN_OVER_WINDOW_SMALL", "97")
WHOLE = "100000000"
OPEN_SECONDS = 3600


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeOverWindowTests(unittest.TestCase):
    def setUp(self):
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_OPEN_DEPTH_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        source = Path(FIXTURES) / NAME / "store"
        if not source.is_dir():
            self.skipTest("no fixture store {}".format(source))
        self.work = Path(tempfile.mkdtemp(prefix="fn-over-window-", dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)
        self.node = Node(self, IMAGE, root=self.work / NAME, name=NAME)
        shutil.copytree(source, self.node.store_path, symlinks=True)
        lock = self.node.store_path / "writer.lock"
        if not lock.exists():
            lock.touch(mode=0o600)
        rebound = self.node.store("rebind-filesystem", timeout=600)
        self.assertEqual(rebound.returncode, 0, rebound.stderr)

    def overview(self, window):
        """(group, low, high, count, the OVER low-high reply as bytes, seconds) under WINDOW."""
        started = time.monotonic()
        owner = self.node.start(env={"FN_NATIVE_OVER_WINDOW": window}, timeout=OPEN_SECONDS,
                                limit=64 << 20)
        try:
            client = Client(self.node.port, timeout=600, greeting=(b"200",))
            try:
                status = client.command("LIST ACTIVE")
                self.assertTrue(status.startswith(b"215 "), status)
                rows = []
                while True:
                    row = client.line(limit=4096)
                    if row == b".\r\n":
                        break
                    rows.append(row)
                self.assertTrue(rows, "LIST ACTIVE named no group")
                # RFC 3977 section 7.6.3: name high low status.
                group, high, low = rows[0].split()[:3]
                group = group.decode("ascii")
                status = client.command("GROUP " + group)
                self.assertTrue(status.startswith(b"211 "), status)
                count = int(status.split()[1])
                self.assertEqual((int(status.split()[2]), int(status.split()[3])),
                                 (int(low), int(high)), status)
                asked = time.monotonic()
                status = client.command("OVER {}-{}".format(int(low), int(high)))
                self.assertEqual(status, b"224 Overview information follows\r\n")
                reply = [status]
                while True:
                    row = client.line(limit=65536)
                    reply.append(row)
                    if row == b".\r\n":
                        break
                    self.assertLessEqual(len(reply), count + 2)
                self.assertEqual(client.command("QUIT")[:3], b"205")
                return (group, int(low), int(high), count, b"".join(reply),
                        time.monotonic() - asked)
            finally:
                client.close(False)
        finally:
            self.node.stop(process=owner, grace=OPEN_SECONDS)

    def test_whole_range_under_a_small_quantum_is_the_unbounded_reply(self):
        group, low, high, count, small, small_seconds = self.overview(SMALL)
        rows = small.split(b"\r\n")[1:-2]
        self.assertEqual(len(rows), count)
        self.assertEqual(count, high - low + 1)
        self.assertTrue(rows[0].startswith("{}\t".format(low).encode("ascii")), rows[0][:40])
        self.assertTrue(rows[-1].startswith("{}\t".format(high).encode("ascii")), rows[-1][:40])
        numbers = [int(row.split(b"\t", 1)[0]) for row in rows]
        self.assertEqual(numbers, list(range(low, high + 1)))
        whole = self.overview(WHOLE)
        self.assertEqual(whole[:4], (group, low, high, count))
        self.assertEqual(whole[4], small)
        print("OVER-WINDOW {} rows={} small={} seconds={:.1f} whole seconds={:.1f} bytes={}".format(
            group, count, SMALL, small_seconds, whole[5], len(small)), flush=True)


if __name__ == "__main__":
    unittest.main()
