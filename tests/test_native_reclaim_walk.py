"""The live reclaim pass over the pinned history in chunks, on the native
developer image (lane reclaim, PRF-1315; specs/storage.md "Reclaim's walk in
chunks"; the decided GROUP count, planning/design/group-count-after-reclaim-
2026-10-03.md).

This replaces tests/native_history_root_raw-mock.lisp as the walk's evidence:
the mock drives the host walk against a hand-written ACL2 case table, and
these cases run the real owner, real ACL2 and the real P3 history root.

* A history longer than two walk chunks (+fnn-reclaim-chunk-rows+ = 1024
  rows), every other article expired by a posted Expires: in the past: the
  live `store reclaim` installs, reclaims exactly the expired half, and the
  connection open across the swap reads the survivors and refuses the
  reclaimed by name.
* GROUP after the swap reports the exact AVAILABLE count with the true first
  and last available numbers (decision 2'): `211 N F L`, N the survivors, not
  the allocation count.  On an image without the available projection, GROUP
  answers the allocation count: that is the red-before.
* The reopen after a stop serves the same.
* FN_RUN_RECLAIM_RSS=1 adds the measurement the reclaim-design packet asks
  for (its slice 3): the owner's resident set before and after a pass at 1k
  and 10k articles (Linux /proc only), recorded in the test's output and not
  asserted.
"""
from __future__ import annotations

import os
import re
import time
import unittest
from pathlib import Path

from tests.native_harness import Client, EXIT, Node, native_image, requires
from tests import test_native_expiry as expiry

GROUP, PAST = expiry.GROUP, expiry.PAST
IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
CHUNK = 1024
# The store's profile: the default developer profile's heap reservation does
# not fund the pass's credit estimate (fn-orcp-estimate) over a 2,100-article
# history -- the red-before run on 45e05c7f answered `deferred-credit`,
# estimate=452968896 -- so the store is initialized with an explicit history
# bound whose reservation does.
PROFILE = ("--profile", "development", "--max-transactions", "16384",
           "--max-history-octets", str(64 << 20))


def tag(i: int) -> str:
    return "w%05d" % i


def post_many(node, n: int, expired) -> None:
    """Post N small articles to GROUP; article i carries a past Expires: when
    EXPIRED(i)."""
    with Client(node.port, timeout=300, greeting=None) as c:
        for i in range(n):
            first, final = c.post(expiry.article(tag(i), GROUP, PAST if expired(i) else None))
            assert (final or first).startswith(b"240"), (i, first, final)


def rss_kib(pid: int):
    try:
        for line in Path("/proc/%d/status" % pid).read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1])
    except OSError:
        return None
    return None


@requires(IMAGE)
class NativeReclaimWalkTests(unittest.TestCase):
    image = IMAGE
    setUp = expiry.ExpiryMixin.setUp
    reclaim = expiry.ExpiryMixin.reclaim
    owner_lines = expiry.ExpiryMixin.owner_lines

    def node(self, name="node"):
        node = Node(self, self.image, root=self.root / name)
        node.operator("init", *PROFILE, GROUP, expiry.KEEP, timeout=600, expect=EXIT.OK)
        secret = node.store("node-secret", "create", timeout=600)
        self.assertIn(secret.returncode, (EXIT.OK, EXIT.REFUSED), secret.stderr[-600:])
        return node

    def group_line(self, client) -> bytes:
        return client.command("GROUP " + GROUP)

    def test_a_pass_longer_than_two_chunks_installs_and_counts_the_available(self):
        n = 2 * CHUNK + 52
        expired = lambda i: i % 2 == 1
        survivors = [i + 1 for i in range(n) if not expired(i)]  # article numbers from 1
        node = self.node("walk")
        owner = node.start(timeout=600)
        try:
            post_many(node, n, expired)
            node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
            c = Client(node.port, timeout=300, greeting=None)
            self.assertTrue(self.group_line(c).startswith(b"211 %d 1 %d " % (n, n)))
            self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(1)).startswith(b"223"))
            done = self.reclaim(node)
            self.assertIn(b"installed", done.stdout, (done.stdout, owner.stderr.since(0)[-3000:]))
            line = self.owner_lines(owner, re.compile(rb"RECLAIM installed records="), 1)
            self.assertEqual(len(line), 1, owner.stderr.since(0)[-3000:])
            self.assertIn(b"reclaimed=%d " % (n - len(survivors)), line[0], line)
            # The connection open across the swap: reclaimed by name, the
            # survivors read, posting continues.
            self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(1))
                            .startswith(b"430 article reclaimed"))
            self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(n - 2))
                            .startswith(b"223"))
            # Decision 2': the exact available count, true first and last.
            want = b"211 %d %d %d " % (len(survivors), survivors[0], survivors[-1])
            got = self.group_line(c)
            self.assertTrue(got.startswith(want), (got, want))
            first, final = c.post(expiry.article("after", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            c.close()
        finally:
            node.stop(expect=None, grace=300)
        node.start(timeout=600)
        try:
            with Client(node.port, timeout=300, greeting=None) as c:
                got = self.group_line(c)
                # the post after the swap took the next number: n + 1
                want = b"211 %d %d %d " % (len(survivors) + 1, survivors[0], n + 1)
                self.assertTrue(got.startswith(want), (got, want))
                self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(3))
                                .startswith(b"430 article reclaimed"))
        finally:
            node.stop(expect=None, grace=300)

    @unittest.skipUnless(os.environ.get("FN_RUN_RECLAIM_RSS") == "1",
                         "FN_RUN_RECLAIM_RSS=1 runs the walk's resident-set measurement")
    def test_resident_set_of_a_pass_at_1k_and_10k(self):
        for n in (1000, 10000):
            node = self.node("rss-%d" % n)
            owner = node.start(timeout=1800)
            try:
                post_many(node, n, lambda i: i % 2 == 1)
                node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
                pid = owner.pid
                before = rss_kib(pid)
                started = time.monotonic()
                done = self.reclaim(node)
                elapsed = time.monotonic() - started
                after = rss_kib(pid)
                self.assertIn(b"installed", done.stdout, done.stdout)
                print("RECLAIM-RSS n=%d rss_before_kib=%s rss_after_kib=%s seconds=%.2f"
                      % (n, before, after, elapsed), flush=True)
            finally:
                node.stop(expect=None, grace=600)


if __name__ == "__main__":
    unittest.main()
