"""What a quantized OVER of a whole group costs the owner, by store size
(lane served-catalog-live, 2026-10-02; Codex r67 F1; PRF-1020).

A MEASUREMENT, not a matrix module: it is skipped unless FN_OVER_COST_FIXTURES
names fixture stores (comma-separated names under FN_OPEN_DEPTH_FIXTURES;
hbox: n1k-2k,n10k-2k,syn100k-2k).  For each store it serves one
`OVER low-high` of the first group twice, at ACL2's own quantum
(fn-splan-cursor-window, no override) and at one quantum for the whole range
(FN_NATIVE_OVER_WINDOW=100000000), under FN_OWNER_MEASURE=1, and prints one
line per run from the owner's own account of its cursor quanta
(host/native/owner.lisp, label :over-cursor: holds of the owner mutex, their
total and longest duration, the octets allocated while held):

    OVER-CURSOR-COST store=... rows=N window=acl2|whole seconds=S
        holds=H held-us=T max-us=M bytes=B us-per-hold=... bytes-per-hold=...

The guard of the host-called quantum (fn-splan-cursor-step) is evaluated in
every hold, so a guard that walks the catalog shows as us-per-hold growing
with N.  The module asserts only what does not depend on the box's load: the
reply is one row per article, and the two windows' replies are equal.

    FN_OPEN_DEPTH_FIXTURES=/tank/fn/scratch/fixtures \\
    FN_OVER_COST_FIXTURES=n1k-2k,n10k-2k,syn100k-2k FN_NATIVE_DEVELOPER_HOST=... \\
        python3 -m unittest tests.test_native_over_cursor_cost
"""
import os
import re
import shutil
import tempfile
import time
import unittest
from pathlib import Path

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
FIXTURES = os.environ.get("FN_OPEN_DEPTH_FIXTURES")
NAMES = [n for n in os.environ.get("FN_OVER_COST_FIXTURES", "").split(",") if n]
WHOLE = "100000000"
OPEN_SECONDS = 3600
MEASURE = re.compile(rb"fn-owner-measure over-cursor holds=(\d+) held-us=(\d+) max-us=(\d+) bytes=(\d+)")


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
@unittest.skipUnless(FIXTURES and NAMES, "a measurement: set FN_OPEN_DEPTH_FIXTURES and FN_OVER_COST_FIXTURES")
class NativeOverCursorCost(unittest.TestCase):
    def node(self, name):
        source = Path(FIXTURES) / name / "store"
        self.assertTrue(source.is_dir(), source)
        work = Path(tempfile.mkdtemp(prefix="fn-over-cost-", dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, work, True)
        node = Node(self, IMAGE, root=work / name, name=name)
        shutil.copytree(source, node.store_path, symlinks=True)
        lock = node.store_path / "writer.lock"
        if not lock.exists():
            lock.touch(mode=0o600)
        rebound = node.store("rebind-filesystem", timeout=600)
        self.assertEqual(rebound.returncode, 0, rebound.stderr)
        return node

    def overview(self, node, window):
        env = {"FN_OWNER_MEASURE": "1"}
        if window:
            env["FN_NATIVE_OVER_WINDOW"] = window
        owner = node.start(env=env, timeout=OPEN_SECONDS, limit=64 << 20)
        try:
            client = Client(node.port, timeout=3600, greeting=(b"200",))
            try:
                self.assertTrue(client.command("LIST ACTIVE").startswith(b"215 "))
                rows = []
                while True:
                    row = client.line(limit=4096)
                    if row == b".\r\n":
                        break
                    rows.append(row)
                group, high, low = rows[0].split()[:3]
                status = client.command("GROUP " + group.decode("ascii"))
                self.assertTrue(status.startswith(b"211 "), status)
                count = int(status.split()[1])
                asked = time.monotonic()
                status = client.command("OVER {}-{}".format(int(low), int(high)))
                self.assertTrue(status.startswith(b"224 "), status)
                reply = []
                while True:
                    row = client.line(limit=65536)
                    if row == b".\r\n":
                        break
                    reply.append(row)
                seconds = time.monotonic() - asked
                self.assertEqual(client.command("QUIT")[:3], b"205")
            finally:
                client.close(False)
        finally:
            node.stop(process=owner, grace=OPEN_SECONDS)
        found = MEASURE.search(owner.stderr.since(0))
        self.assertIsNotNone(found, owner.stderr.since(0)[-2000:])
        holds, held, most, consed = (int(g) for g in found.groups())
        self.assertEqual(len(reply), count)
        return count, reply, seconds, holds, held, most, consed

    def test_cost_by_store_size(self):
        for name in NAMES:
            node = self.node(name)
            replies = []
            for label, window in (("acl2", None), ("whole", WHOLE)):
                count, reply, seconds, holds, held, most, consed = self.overview(node, window)
                replies.append(reply)
                print("OVER-CURSOR-COST store={} rows={} window={} seconds={:.3f} holds={} held-us={} "
                      "max-us={} bytes={} us-per-hold={:.1f} bytes-per-hold={:.0f}".format(
                          name, count, label, seconds, holds, held, most, consed,
                          held / max(holds, 1), consed / max(holds, 1)), flush=True)
            self.assertEqual(replies[0], replies[1])


if __name__ == "__main__":
    unittest.main()
