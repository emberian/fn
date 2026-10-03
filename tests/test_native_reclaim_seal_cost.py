"""The reclaim swap quantum's added seal cost (lane arena-forget).

The pass seals its K tombstones under the owner mutex in the swap quantum
(books/owner-reclaim-seal.lisp).  This measures that seal (the installed
line's seal-us=) at several K on a quiet node, to fit the curve.  Opt in:
FN_NATIVE_RECLAIM_SEAL_SCALE="500,2000,8000" (the K values); each K posts K
expired articles and three kept ones, expires, and reclaims while serving.
"""
import os
import re
import unittest

from tests.native_harness import Client, EXIT, native_image, requires
from tests import test_native_expiry as expiry

GROUP = expiry.GROUP
IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
SCALE = [int(k) for k in os.environ.get("FN_NATIVE_RECLAIM_SEAL_SCALE", "").split(",") if k]


@requires(IMAGE)
@unittest.skipUnless(SCALE, "FN_NATIVE_RECLAIM_SEAL_SCALE names the K values")
class NativeReclaimSealCost(unittest.TestCase):
    image = IMAGE
    setUp = expiry.ExpiryMixin.setUp
    node = expiry.ExpiryMixin.node
    post_all = expiry.ExpiryMixin.post_all
    reclaim = expiry.ExpiryMixin.reclaim
    owner_lines = expiry.ExpiryMixin.owner_lines

    def test_seal_cost_curve(self):
        rows = []
        for k in SCALE:
            node = self.node("k%d" % k)
            self.post_all(node, [("n%d" % i, GROUP, None, 0) for i in range(3)] +
                          [("p%d" % i, GROUP, expiry.PAST, 0) for i in range(k)])
            owner = node.start(timeout=1200)
            try:
                done = self.reclaim(node, "--recorded", expect=None)
                self.assertEqual(done.returncode, EXIT.OK, (done.stdout, done.stderr[-2000:]))
                pattern = re.compile(rb"RECLAIM installed .*reclaimed=(\d+) .*ms=(\d+) sealed=(\d+) seal-us=(\d+)")
                line = self.owner_lines(owner, pattern, 1, deadline=600)
                self.assertEqual(len(line), 1, owner.stderr.since(0)[-3000:])
                m = pattern.search(line[0])
                reclaimed, ms, sealed, us = (int(g) for g in m.groups())
                self.assertEqual(reclaimed, k)
                self.assertEqual(sealed, k)
                rows.append((k, us, ms))
                with Client(node.port, timeout=300, greeting=None) as c:
                    self.assertTrue(c.command("STAT %s" % expiry.msgid("p0")).startswith(b"430"))
                    self.assertTrue(c.command("STAT %s" % expiry.msgid("n0")).startswith(b"223"))
            finally:
                node.stop(expect=None, grace=300)
        for k, us, ms in rows:
            print("RECLAIM-SEAL-COST k=%d seal-us=%d pass-ms=%d us-per-tombstone=%.2f"
                  % (k, us, ms, us / max(k, 1)))
