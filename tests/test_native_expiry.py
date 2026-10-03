"""The operator's per-group expiry policy, on the native images (Q14; RFC 5536
section 3.2.5; books/expiry-policy.lisp, books/expiry.lisp,
books/expiry-verdict.lisp; the reclaim path books/store-reclaim-pack.lisp).

`retention expire GROUP ...` writes a group's policy (configuration quota
rows); `store reclaim` releases what the policy expires at its instant
through the one reclaim path (tombstone, checkpoint, drop).  The cases, each
over a store the served node filled (the clock cannot be moved, so age is
exercised through posted Expires: headers in the past, which a policy with an
age rule honours at once, and size through the octets window):

* Expires: honoured: articles whose Expires: has passed leave, the others
  (no Expires:, a future one) stay; a cross-post to a group with no policy
  stays; the served answers keep expired distinct from absent (430/423
  `article reclaimed`, never `no article`); a re-offer of an expired
  Message-ID is refused (the duplicate history keeps it, never
  resurrected); GROUP's high water and the next POST's number are unchanged
  (numbers never reused);
* no policy, nothing expires (D03's default); `clear` removes a policy;
* the size window: the newest articles whose octets fit stay;
* a process death at each state-checkpoint cut of an expiring reclaim: the
  store reopens and `store reclaim --recorded` (or a rerun) completes the
  same expiry;
* on the SERVING node (Q16, books/owner-reclaim.lisp): `store reclaim
  --dry-run` is a request the owner answers (the fold over its rows off its
  mutex; posts and reads continue), naming what the offline dry run names
  once the node stops; `store reclaim` itself is refused by name
  (offline-only) until the online pass lands.
"""
from __future__ import annotations

import re
import shutil
import threading
import time
import unittest

from tests.native_harness import EXIT, Client, Node, native_image, requires, scratch

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
PRODUCTION = native_image("FN_NATIVE_HOST")
GROUP, KEEP = "fn.test", "fn.keep"
PAST = "Mon, 01 Jan 2024 00:00:00 +0000"
FUTURE = "Fri, 01 Jan 2100 00:00:00 +0000"


def msgid(tag: str) -> str:
    return "<xpy-%s@example.invalid>" % tag


def article(tag: str, groups=GROUP, expires=None, pad: int = 0) -> bytes:
    head = ("From: xpy@example.invalid\r\nNewsgroups: %s\r\nSubject: expiry %s\r\n"
            "Message-ID: %s\r\n" % (groups, tag, msgid(tag)))
    if expires:
        head += "Expires: %s\r\n" % expires
    filler = "".join("%s\r\n" % ("x" * 76) for _ in range(pad // 78))
    return (head + "\r\nbody of %s\r\n%s" % (tag, filler)).encode("ascii")


def words(stdout: bytes) -> dict:
    line = stdout.decode("utf-8", "replace").splitlines()[0]
    return dict(w.split("=", 1) for w in line.split() if "=" in w)


class ExpiryMixin:
    image = None

    def setUp(self):
        self.root = scratch(self, "fn-xpy-")

    def node(self, name="node"):
        node = Node(self, self.image, root=self.root / name)
        node.operator("init", GROUP, KEEP, timeout=600, expect=EXIT.OK)
        secret = node.store("node-secret", "create", timeout=600)
        self.assertIn(secret.returncode, (EXIT.OK, EXIT.REFUSED), secret.stderr[-600:])
        return node

    def post_all(self, node, items):
        node.start(timeout=600)
        try:
            c = Client(node.port, timeout=300, greeting=None)
            for tag, groups, expires, pad in items:
                first, final = c.post(article(tag, groups, expires, pad))
                self.assertTrue((final or first).startswith(b"240"), (tag, first, final))
            c.close()
        finally:
            node.stop(expect=None, grace=300)

    def served(self, node, commands):
        node.start(timeout=600)
        try:
            c = Client(node.port, timeout=300, greeting=None)
            out = [c.command(cmd) for cmd in commands]
            c.close()
            return out
        finally:
            node.stop(expect=None, grace=300)

    def reclaim(self, node, *flags, env=None, expect=EXIT.OK):
        return node.operator("store", "reclaim", *flags, env=env, timeout=1200, expect=expect)

    def filled(self, name="node"):
        node = self.node(name)
        self.post_all(node, [
            ("p0", GROUP, PAST, 0), ("p1", GROUP, PAST, 0),
            ("n0", GROUP, None, 0), ("f0", GROUP, FUTURE, 0),
            ("x0", "%s,%s" % (GROUP, KEEP), PAST, 0),
        ])
        return node

    def test_expires_is_honoured_and_expired_stays_distinct(self):
        node = self.filled()
        # No policy: nothing expires (D03).
        dry = self.reclaim(node, "--dry-run")
        self.assertTrue(dry.stdout.startswith(b"reclaimed=0 expired=0 "), dry.stdout)
        # An age rule for fn.test (purge 30): a posted Expires: in the past
        # is honoured at once; fn.keep has none.
        node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
        # Words that are no policy are refused as usage, by name.
        node.operator("retention", "expire", "no.such/group!", "purge", "30",
                      expect=EXIT.USAGE)
        node.operator("retention", "expire", GROUP, "keep", "30", "purge", "7",
                      expect=EXIT.USAGE)
        dry = self.reclaim(node, "--dry-run")
        self.assertIn(b"would-expire=2", dry.stdout, dry.stdout)
        listed = set(dry.stdout.decode().split("would-reclaim ")[1:])
        self.assertEqual({l.strip() for l in listed}, {msgid("p0"), msgid("p1")}, dry.stdout)
        done = self.reclaim(node)
        self.assertEqual(words(done.stdout)["reclaimed"], "2", done.stdout)
        self.assertEqual(words(done.stdout)["expired"], "2", done.stdout)
        replies = self.served(node, [
            "ARTICLE %s" % msgid("p0"), "STAT %s" % msgid("p1"),
            "STAT %s" % msgid("n0"), "STAT %s" % msgid("f0"), "STAT %s" % msgid("x0"),
            "STAT %s" % msgid("never"), "GROUP %s" % GROUP, "STAT 1", "STAT 9"])
        self.assertTrue(replies[0].startswith(b"430 article reclaimed"), replies)
        self.assertTrue(replies[1].startswith(b"430 article reclaimed"), replies)
        for r in replies[2:5]:
            self.assertTrue(r.startswith(b"223"), replies)
        self.assertTrue(replies[5].startswith(b"430 no article"), replies)
        self.assertTrue(replies[6].startswith(b"211 "), replies)
        self.assertEqual(replies[6].split()[3], b"5", replies)       # high water kept
        self.assertTrue(replies[7].startswith(b"423 article reclaimed"), replies)
        self.assertTrue(replies[8].startswith(b"423 no article"), replies)
        # The re-offer of an expired article is refused (never resurrected),
        # and the next article takes the next number (none reused).
        node.start(timeout=600)
        try:
            c = Client(node.port, timeout=300, greeting=None)
            first, final = c.post(article("p0", GROUP, PAST))
            self.assertFalse((final or first).startswith(b"240"), (first, final))
            first, final = c.post(article("n1", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            self.assertTrue(c.command("GROUP %s" % GROUP).split()[3] == b"6")
            c.close()
        finally:
            node.stop(expect=None, grace=300)
        # A rerun expires nothing more; `clear' removes the policy.
        again = self.reclaim(node)
        self.assertTrue(again.stdout.startswith(b"reclaimed=0 expired=0 "), again.stdout)
        node.operator("retention", "expire", GROUP, "clear", expect=EXIT.OK)
        dry = self.reclaim(node, "--dry-run")
        self.assertTrue(dry.stdout.startswith(b"reclaimed=0 expired=0 "), dry.stdout)

    def test_size_window_keeps_the_newest(self):
        node = self.node()
        self.post_all(node, [("s%d" % i, GROUP, None, 2000) for i in range(4)])
        one = len(article("s0", GROUP, None, 2000))
        # A window of two and a half posted articles (the stored one adds the
        # injecting agent's few header lines): the two oldest leave.
        node.operator("retention", "expire", GROUP, "octets", str(2 * one + one // 2),
                      expect=EXIT.OK)
        dry = self.reclaim(node, "--dry-run")
        self.assertIn(b"would-expire=2", dry.stdout, dry.stdout)
        listed = {l.strip() for l in dry.stdout.decode().split("would-reclaim ")[1:]}
        self.assertEqual(listed, {msgid("s0"), msgid("s1")}, dry.stdout)

    def owner_lines(self, owner, pattern, count, deadline=60.0):
        """The owner's stderr lines matching PATTERN once COUNT are there."""
        end = time.monotonic() + deadline
        while True:
            found = [l for l in owner.stderr.since(0).splitlines() if pattern.search(l)]
            if len(found) >= count or time.monotonic() > end:
                return found
            time.sleep(0.2)

    def test_a_dry_run_on_the_serving_node(self):
        node = self.filled()
        owner = node.start(timeout=600)
        try:
            # The policy is written live (the owner publishes the record).
            node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
            c = Client(node.port, timeout=300, greeting=None)
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"223"))
            dry = self.reclaim(node, "--dry-run")
            self.assertIn(b"reclaim dry-run", dry.stdout, dry.stdout)
            summary = self.owner_lines(owner, re.compile(rb"RECLAIM dry-run records="), 1)
            self.assertEqual(len(summary), 1, owner.stderr.since(0)[-2000:])
            self.assertIn(b"would-reclaim=2 would-expire=2", summary[0], summary)
            listed = {l.split(b"RECLAIM would-reclaim ", 1)[1].strip().decode()
                      for l in self.owner_lines(owner, re.compile(rb"RECLAIM would-reclaim "), 2)}
            self.assertEqual(listed, {msgid("p0"), msgid("p1")})
            # Nothing was written: the expired article is still served, and a
            # post and a read on the same connection continue.
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"223"))
            first, final = c.post(article("n9", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            self.assertTrue(c.command("STAT %s" % msgid("n9")).startswith(b"223"))
            c.close()
        finally:
            node.stop(expect=None, grace=300)
        # Stopped, the offline dry run names the same articles.
        offline = self.reclaim(node, "--dry-run")
        self.assertIn(b"would-expire=2", offline.stdout, offline.stdout)
        listed = {l.strip() for l in offline.stdout.decode().split("would-reclaim ")[1:]}
        self.assertEqual(listed, {msgid("p0"), msgid("p1")}, offline.stdout)


@requires(DEVELOPER)
class DeveloperExpiryTests(ExpiryMixin, unittest.TestCase):
    image = DEVELOPER

    def test_a_death_mid_expiry_completes_the_same_expiry(self):
        base = self.filled("base")
        base.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
        for point in ("created", "written", "staged-durable", "replaced", "durable"):
            with self.subTest(point=point):
                copy = Node(self, self.image, root=self.root / ("cut-" + point))
                shutil.rmtree(copy.store_path, ignore_errors=True)
                shutil.copytree(base.store_path, copy.store_path)
                cut = self.reclaim(copy, env={"FN_NATIVE_STATE_CHECKPOINT_FAULT":
                                              "state-checkpoint-%s:kill" % point},
                                   expect=None)
                self.assertNotEqual(cut.returncode, EXIT.OK, (point, cut.stdout))
                status = copy.operator("status", timeout=600)
                self.assertEqual(status.returncode, EXIT.OK, (point, status.stderr[-600:]))
                # The instant was recorded before the rewrite: --recorded
                # completes it (or, from the install on, finds nothing left).
                # Never a fresh reclaim in its place (sweep 2026-10-03 S131:
                # a refused, uncertain or faulting --recorded fell back to a
                # new instant, which expires the same p0/p1 and passed).
                done = self.reclaim(copy, "--recorded", expect=None)
                self.assertEqual(done.returncode, EXIT.OK,
                                 (point, done.stdout[-600:], done.stderr[-600:]))
                installed = point in ("replaced", "durable")
                self.assertEqual(b"reclaimed=0 " in done.stdout, installed,
                                 (point, done.stdout[-600:]))
                replies = self.served(copy, ["STAT %s" % msgid("p0"), "STAT %s" % msgid("p1"),
                                             "STAT %s" % msgid("n0"), "STAT %s" % msgid("x0")])
                self.assertTrue(replies[0].startswith(b"430 article reclaimed"), (point, replies))
                self.assertTrue(replies[1].startswith(b"430 article reclaimed"), (point, replies))
                self.assertTrue(replies[2].startswith(b"223"), (point, replies))
                self.assertTrue(replies[3].startswith(b"223"), (point, replies))


    # Q16 (a) (lane online-reclaim-3): the pass that installs on a serving
    # node.  The instant is recorded by an offline `store reclaim' killed
    # after it published the instant and before its checkpoint (the live
    # `store reclaim' that records the instant itself is the next step).
    def recorded_base(self, name="rbase"):
        base = self.filled(name)
        base.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
        cut = self.reclaim(base, env={"FN_NATIVE_STATE_CHECKPOINT_FAULT":
                                      "state-checkpoint-created:kill"}, expect=None)
        self.assertNotEqual(cut.returncode, EXIT.OK, cut.stdout)
        status = base.operator("status", timeout=600)
        self.assertEqual(status.returncode, EXIT.OK, status.stderr[-600:])
        return base

    def copy_of(self, base, name):
        copy = Node(self, self.image, root=self.root / name)
        shutil.rmtree(copy.store_path, ignore_errors=True)
        shutil.copytree(base.store_path, copy.store_path)
        return copy

    def assert_reclaimed(self, node, label):
        replies = self.served(node, ["STAT %s" % msgid("p0"), "STAT %s" % msgid("p1"),
                                     "STAT %s" % msgid("n0"), "STAT %s" % msgid("x0")])
        self.assertTrue(replies[0].startswith(b"430 article reclaimed"), (label, replies))
        self.assertTrue(replies[1].startswith(b"430 article reclaimed"), (label, replies))
        self.assertTrue(replies[2].startswith(b"223"), (label, replies))
        self.assertTrue(replies[3].startswith(b"223"), (label, replies))

    def test_a_recorded_reclaim_installs_on_the_quiet_serving_node(self):
        node = self.copy_of(self.recorded_base(), "live")
        owner = node.start(timeout=600)
        try:
            c = Client(node.port, timeout=300, greeting=None)
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"223"))
            done = self.reclaim(node, "--recorded")
            self.assertIn(b"installed", done.stdout, done.stdout)
            line = self.owner_lines(owner, re.compile(rb"RECLAIM installed records="), 1)
            self.assertEqual(len(line), 1, owner.stderr.since(0)[-3000:])
            self.assertIn(b"reclaimed=2", line[0], line)
            # Served NOW, on the connection open across the swap: the expired
            # articles are reclaimed, the others read; posting continues.
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"430 article reclaimed"))
            self.assertTrue(c.command("STAT %s" % msgid("n0")).startswith(b"223"))
            first, final = c.post(article("n9", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            self.assertTrue(c.command("STAT %s" % msgid("n9")).startswith(b"223"))
            c.close()
            # A second pass finds nothing more (the rerun rewrites nothing).
            again = self.reclaim(node, "--recorded")
            self.assertNotIn(b"installed", again.stdout, again.stdout)
            # The NEXT publication after the swap (no H0 noted: the whole
            # capture of the canonical rows, fn-owner-orcp-swap) is the one
            # the reopen reads.
            auto = re.compile(rb"CHECKPOINT auto sequence=(\d+) ")
            before = len(self.owner_lines(owner, auto, 0))
            asked = node.operator("store", "checkpoint", timeout=600, expect=EXIT.OK)
            self.assertIn(b"accepted operator checkpoint", asked.stdout + asked.stderr)
            published = self.owner_lines(owner, auto, before + 1)
            self.assertEqual(len(published), before + 1, owner.stderr.since(0)[-3000:])
            sequence = int(auto.search(published[-1]).group(1))
        finally:
            node.stop(expect=None, grace=300)
        status = node.operator("status", timeout=600, expect=EXIT.OK)
        opened = [l for l in status.stdout.decode("ascii").splitlines() if l.startswith("open=")]
        self.assertEqual(opened, ["open=checkpoint:%d suffix=0" % sequence], status.stdout)
        # Reopened from it: the durable publication is the one served before the stop.
        self.assert_reclaimed(node, "reopened")
        self.assertTrue(self.served(node, ["STAT %s" % msgid("n9")])[0].startswith(b"223"))

    # Q16 (lane online-reclaim-6): `store reclaim' on the serving node records
    # the instant through the live reconfiguration, then the pass installs.
    def test_a_live_reclaim_records_the_instant_and_installs(self):
        node = self.filled("live-reclaim")
        owner = node.start(timeout=600)
        try:
            node.operator("retention", "expire", GROUP, "purge", "30", expect=EXIT.OK)
            c = Client(node.port, timeout=300, greeting=None)
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"223"))
            done = self.reclaim(node)
            self.assertIn(b"installed", done.stdout, done.stdout)
            line = self.owner_lines(owner, re.compile(rb"RECLAIM installed records="), 1)
            self.assertEqual(len(line), 1, owner.stderr.since(0)[-3000:])
            self.assertIn(b"reclaimed=2", line[0], line)
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"430 article reclaimed"))
            self.assertTrue(c.command("STAT %s" % msgid("n0")).startswith(b"223"))
            first, final = c.post(article("n9", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            c.close()
        finally:
            node.stop(expect=None, grace=300)
        self.assert_reclaimed(node, "reopened")
        self.assertTrue(self.served(node, ["STAT %s" % msgid("n9")])[0].startswith(b"223"))

    # Q16 item 5 (lane online-reclaim-7): posting continues through a pass.
    # Posts commit between the capture and the swap (the pass held at its
    # :rebuilt cut, off the owner mutex, by the developer selector
    # FN_NATIVE_TEST_RECLAIM_STALL_FILE): the swap is taken only over exactly
    # the captured Store (PRF-939 fn-orcp-swap-only-over-the-capture), so the
    # pass defers BY NAME, reason=delta -- refused, nothing installed -- and
    # every post is accepted and served.  The rerun on the quiet node
    # installs and keeps them.  Until the swap absorbs the delta a pass under
    # steady posting defers; it never installs a Store that lost a post.  The
    # absorbing resume is proved (PRF-968, books/store-finalize-incremental,
    # lane incremental-finalize-2: fn-sfi-cpr-resume-carried-is-sco-cpr-resume,
    # fn-sfi-extend-open-carried-is-rii-extend-open and the bound
    # fn-sfi-cpr-resume-carried-steps-bounded, at most |configs| + |Q| steps
    # with no node term; PRF-946 the incremental finalize).  Once
    # incremental-finalize-3 wires it into the swap, this case expects the
    # install over the delta.
    def test_posting_through_a_pass_defers_by_name_then_installs(self):
        node = self.copy_of(self.recorded_base(), "posting")
        stall = self.root / "reclaim-stall"
        stall.write_bytes(b"")
        owner = node.start(timeout=600, env={"FN_NATIVE_TEST_RECLAIM_STALL_FILE": str(stall)})
        tags = ["c%d" % i for i in range(5)]
        try:
            c = Client(node.port, timeout=300, greeting=None)
            result = {}
            worker = threading.Thread(
                target=lambda: result.setdefault("done", self.reclaim(node, "--recorded", expect=None)))
            worker.start()
            held = self.owner_lines(owner, re.compile(rb"RECLAIM stalled at=rebuilt"), 1, deadline=600)
            self.assertEqual(len(held), 1, owner.stderr.since(0)[-3000:])
            for tag in tags:
                first, final = c.post(article(tag, GROUP, None))
                self.assertTrue((final or first).startswith(b"240"), (tag, first, final))
            stall.unlink()
            worker.join(timeout=1300)
            self.assertFalse(worker.is_alive())
            done = result["done"]
            self.assertEqual(done.returncode, EXIT.REFUSED, (done.stdout, done.stderr[-600:]))
            self.assertNotIn(b"installed", done.stdout, done.stdout)
            deferred = self.owner_lines(owner, re.compile(rb"RECLAIM deferred reason=delta"), 1)
            self.assertEqual(len(deferred), 1, owner.stderr.since(0)[-3000:])
            self.assertEqual(self.owner_lines(owner, re.compile(rb"RECLAIM installed"), 1, deadline=0), [])
            # Nothing installed: the expired article is still served, and every post.
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"223"))
            for tag in tags:
                self.assertTrue(c.command("STAT %s" % msgid(tag)).startswith(b"223"), tag)
            # Quiet now: the rerun installs over a Store that has the posts.
            again = self.reclaim(node, "--recorded")
            self.assertIn(b"installed", again.stdout, again.stdout)
            self.assertTrue(c.command("STAT %s" % msgid("p0")).startswith(b"430 article reclaimed"))
            for tag in tags:
                self.assertTrue(c.command("STAT %s" % msgid(tag)).startswith(b"223"), tag)
            first, final = c.post(article("c9", GROUP, None))
            self.assertTrue((final or first).startswith(b"240"), (first, final))
            c.close()
        finally:
            node.stop(expect=None, grace=300)
        self.assert_reclaimed(node, "posting")
        replies = self.served(node, ["STAT %s" % msgid(t) for t in tags + ["c9"]])
        self.assertTrue(all(r.startswith(b"223") for r in replies), replies)

    def test_a_death_at_each_pass_cut_is_old_or_new(self):
        base = self.recorded_base()
        for cut in ("captured", "rewritten", "staged", "interned", "rebuilt",
                    "installed", "swapped", "released"):
            with self.subTest(cut=cut):
                node = self.copy_of(base, "pass-cut-" + cut)
                node.start(timeout=600, env={"FN_NATIVE_RECLAIM_FAULT": cut + ":kill"})
                self.reclaim(node, "--recorded", expect=None)
                node.process.wait(timeout=300)
                node.process.finish()
                # Old before the install (the articles are still there, and
                # the rerun reclaims them), new from it; the offline rerun
                # completes either to the same result.
                served = self.served(node, ["STAT %s" % msgid("p0")])[0]
                if cut in ("installed", "swapped", "released"):
                    self.assertTrue(served.startswith(b"430 article reclaimed"), (cut, served))
                else:
                    self.assertTrue(served.startswith(b"223"), (cut, served))
                done = self.reclaim(node, "--recorded", expect=None)
                self.assertIn(done.returncode, (EXIT.OK, EXIT.REFUSED), (cut, done.stdout))
                self.assert_reclaimed(node, cut)


@requires(PRODUCTION)
class ProductionExpiryTests(ExpiryMixin, unittest.TestCase):
    image = PRODUCTION


if __name__ == "__main__":
    unittest.main()
