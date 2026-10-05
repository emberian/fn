"""The live reclaim pass over the pinned history in chunks, on the native
developer image (lane reclaim, PRF-1315; specs/storage.md "Reclaim's walk in
chunks"; the decided GROUP count, planning/design/group-count-after-reclaim-
2026-10-03.md).

This replaces tests/native_history_root_raw-mock.lisp as the walk's evidence:
the mock drives the host walk against a hand-written ACL2 case table, and
these cases run the real owner, real ACL2 and the real P3 history root.

* A history longer than two walk chunks (fnn-reclaim-chunk-rows = 1024
  rows), every other article expired by a posted Expires: in the past: the
  live `store reclaim` installs, reclaims exactly the expired half, and the
  connection open across the swap reads the survivors and refuses the
  reclaimed by name.
* GROUP after the swap reports the exact AVAILABLE count with the true first
  and last available numbers (decision 2'): `211 N F L`, N the survivors, not
  the allocation count.  On an image without the available projection, GROUP
  answers the allocation count: that is the red-before.
* The reopen after a stop serves the same.
* Live reclaim is the operator's opt-in (D53, `[resources] reclaim_live`):
  every pass above runs on a node that asks for it.  Without the key the
  same live `store reclaim` (and `--recorded`) is refused by name,
  offline-only, before anything is recorded or reserved, the history is
  untouched and the offline verbs still reclaim; and the next run's heap
  figure (`status`, heap=) is the store's alone, smaller than the opted-in
  one.
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
# The store's profile: the development preset with room for the 2,100
# records (its own T is 128).  Until lane reclaim-funding (S152,
# planning/design/reclaim-funding-2026-10-04.md) the pass reserved 64 x its
# history's octets out of the articles' pool -- the red-before runs on
# 45e05c7f answered `deferred-credit`, estimate=452968896, at the preset's H
# and at an explicit 64 MiB alike -- so no history bound funded it; the pass
# now borrows its second generation's demand from the owner's work reserve,
# which the launcher's figure holds at the profile's bounds.
PROFILE = ("--profile", "development", "--max-transactions", "16384")


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

    def node(self, name="node", live=True):
        node = Node(self, self.image, root=self.root / name, extra=expiry.reclaim_extra(live))
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

    def test_a_capacity_free_node_reclaims_live(self):
        """S152 on a node without a profile: `init` sizes the store itself (the
        friend ladder), the articles' pool is the defaults' (a few MiB), and a
        history of 1,100 articles is two orders of magnitude past what the
        pass's former reservation (64 x the history's octets out of that pool)
        admitted.  The live pass installs and reclaims exactly the expired."""
        n = CHUNK + 76
        expired = lambda i: i % 2 == 0
        node = Node(self, self.image, root=self.root / "capacity-free",
                    extra=expiry.reclaim_extra(True))
        node.operator("init", GROUP, expiry.KEEP, timeout=600, expect=EXIT.OK)
        secret = node.store("node-secret", "create", timeout=600)
        self.assertIn(secret.returncode, (EXIT.OK, EXIT.REFUSED), secret.stderr[-600:])
        owner = node.start(timeout=600)
        try:
            post_many(node, n, expired)
            node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
            done = self.reclaim(node)
            self.assertIn(b"installed", done.stdout, (done.stdout, owner.stderr.since(0)[-3000:]))
            self.assertNotIn(b"reason=credit", owner.stderr.since(0))
            line = self.owner_lines(owner, re.compile(rb"RECLAIM installed records="), 1)
            self.assertEqual(len(line), 1, owner.stderr.since(0)[-3000:])
            self.assertIn(b"reclaimed=%d " % sum(1 for i in range(n) if expired(i)), line[0], line)
            with Client(node.port, timeout=300, greeting=None) as c:
                self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(0))
                                .startswith(b"430 article reclaimed"))
                self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(1))
                                .startswith(b"223"))
        finally:
            node.stop(expect=None, grace=300)

    def test_without_the_opt_in_a_live_pass_is_refused_by_name(self):
        """D53: no `[resources] reclaim_live`: the serving node refuses
        `store reclaim` and `--recorded` by name (offline-only), records no
        instant and reclaims nothing; the dry run still answers; stopped, the
        offline `store reclaim` reclaims the expired as ever."""
        n = 64
        expired = lambda i: i % 2 == 0
        node = self.node("off", live=False)
        self.assertNotIn("reclaim_live", node.config.read_text())
        owner = node.start(timeout=600)
        try:
            post_many(node, n, expired)
            node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
            for flags in ((), ("--recorded",)):
                refused = self.reclaim(node, *flags, expect=None)
                self.assertEqual(refused.returncode, EXIT.REFUSED,
                                 (flags, refused.stdout, refused.stderr[-600:]))
                self.assertIn(b"offline-only", refused.stdout + refused.stderr,
                              (flags, refused.stdout, refused.stderr[-600:]))
            answers = self.owner_lines(owner, re.compile(rb"RECLAIM request mode="), 2)
            self.assertEqual(len(answers), 2, owner.stderr.since(0)[-3000:])
            self.assertTrue(all(b"answer=offline-only" in a for a in answers), answers)
            self.assertNotIn(b"RECLAIM installed", owner.stderr.since(0))
            dry = self.reclaim(node, "--dry-run")
            self.assertEqual(dry.returncode, EXIT.OK, dry.stderr[-600:])
            with Client(node.port, timeout=300, greeting=None) as c:
                self.assertTrue(c.command("STAT <xpy-%s@example.invalid>" % tag(0))
                                .startswith(b"223"))
        finally:
            node.stop(expect=None, grace=300)
        done = self.reclaim(node)
        self.assertIn(b"reclaimed=%d " % sum(1 for i in range(n) if expired(i)), done.stdout,
                      done.stdout)

    def test_the_opt_in_is_the_only_change_to_the_figure(self):
        """The next run's figure (`status` heap=) on the same store: without
        the key it is the store's alone; with it, larger by the owner's work
        reserve.  Their numbers are printed for the record (the off figure is
        compared with the release image's on the box, by hand)."""
        line = re.compile(rb"^heap=(\d+) MB", re.M)
        off = self.node("figure", live=False)
        status = off.operator("status", timeout=600, expect=EXIT.OK)
        a = line.search(status.stdout)
        self.assertIsNotNone(a, status.stdout)
        on = Node(self, self.image, root=self.root / "figure", extra=expiry.reclaim_extra(True))
        status = on.operator("status", timeout=600, expect=EXIT.OK)
        b = line.search(status.stdout)
        self.assertIsNotNone(b, status.stdout)
        print("RECLAIM-OPTIN-FIGURE off=%s on=%s" % (a.group(1).decode(), b.group(1).decode()),
              flush=True)
        self.assertLess(int(a.group(1)), int(b.group(1)), (a.group(0), b.group(0)))

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
