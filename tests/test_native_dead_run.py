"""Post-and-cancel in one group costs the same at the end as at the start, and
GROUP over a cancelled run costs what it costs over none (lane
spans-dead-runs, RED-2, 2026-10-11).

A group's live summary keeps its least and greatest live numbers.  Two walks
crossed the dead numbers between them: a withdrawal of the greatest found the
next one below by probing every number (the reference catalog's
fn-cat$c-scan-down; the paged catalog every image runs reads its link table,
fn-cat$p-prev), and a reader's summary at a view below the count stepped down
number by number from the greatest past every number in X or dead
(books/served-catalog-view.lisp, before this lane).  Both now read the live
list (fn-cat-live-prev, fn-scv-link-down), so neither mentions the run.

The case first posts a surviving floor, then D articles (FN_DEAD_RUN_D,
default 1200) to fn.dr through a configured peer, each with an RFC 8315
Cancel-Lock, and cancels every one in
ascending order: a run of D dead numbers.  The store is the scale profile
(4096 transactions; the case spends 2D + 2R + 3), so D and R default to
1200 and 400; the counting method needs only D >= 64.  Then R rounds (FN_DEAD_RUN_R,
default 400) each post one article to fn.dr above the run and cancel it
(the cancel withdraws the group's greatest, whose live neighbour below is
the run's floor), while a reader repeats GROUP fn.dr and GROUP fn.ctl (a
group with no run).  The developer-image timing method asserts:
  * every post and cancel is accepted (235);
  * the mean cancel time over the last 200 rounds is within 2x of the first
    200 (flatness alone does not exclude a constant D probes per cancel);
  * GROUP fn.dr's p95 is within 2x (plus 2 ms) of GROUP fn.ctl's.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_dead_run

The separate counting method needs build/fn-host-prof (override with
FN_DEAD_RUN_PROF_HOST).  Without it that method explicitly skips.  It loads
count-hook only in the measured owner, stalls each top's barrier, and serves
GROUP until live-prev/next proves the high-in-X branch ran.  Exact counter
snapshots exclude setup.  Membership calls must be <= 16 * (GROUPs + R),
also checked per GROUP pair so idle polls cannot dilute a D-sized scan.
16 allows two summaries per GROUP, three endpoint tests per summary, and
both raw and *1* wrappers (12), with four calls of slack.  There is no D term.
No absolute cancel-time ceiling is asserted: disk latency is unbounded and
there is no measured machine-specific budget here.
"""
import base64
import hashlib
import os
from pathlib import Path
import threading
import time
import unittest

from tests.native_harness import (
    EXIT_OK, ROOT, Client, Node, dot_stuff, executable, native_image, native_peer_add)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
PROF_IMAGE = Path(os.environ.get("FN_DEAD_RUN_PROF_HOST", ROOT / "build/fn-host-prof"))
D = int(os.environ.get("FN_DEAD_RUN_D", "1200"))
R = int(os.environ.get("FN_DEAD_RUN_R", "400"))
WINDOW = 200
COUNT_FACTOR = 16
# The live-link exports are defabsstobj exports: their raw-Lisp calls go to
# the attached implementation's :exec functions, the paged catalog's in every
# image (books/catalog-paged.lisp fn-cat$p-live-next/-prev), the reference
# catalog's (fn-cat$c-*) only where none is attached.  Those are counted.
LINK_NAMES = ("FN-CAT$P-LIVE-PREV", "FN-CAT$P-LIVE-NEXT",
              "FN-CAT$C-LIVE-PREV", "FN-CAT$C-LIVE-NEXT")
COUNT_NAMES = LINK_NAMES + ("FN-SCV-IN-XP",)
REQUIRED_WRAPS = ("FN-CAT$P-LIVE-PREV", "FN-CAT$P-LIVE-NEXT", "FN-SCV-IN-XP")
KEY = base64.b64encode(hashlib.sha256(b"dead run poster").digest())
LOCK = base64.b64encode(hashlib.sha256(KEY).digest())


def article(message_id, group):
    return (b"From: dr@example.invalid\r\n"
            b"Newsgroups: " + group + b"\r\n"
            b"Subject: dead run\r\n"
            b"Date: Sun, 11 Oct 2026 12:00:00 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n"
            b"Cancel-Lock: sha256:" + LOCK + b"\r\n\r\n"
            b"a dead run body\r\n")


def cancel(message_id, target):
    return (b"From: dr@example.invalid\r\n"
            b"Newsgroups: fn.dr\r\n"
            b"Subject: cmsg cancel " + target + b"\r\n"
            b"Date: Sun, 11 Oct 2026 12:00:01 +0000\r\n"
            b"Path: source.invalid!not-for-mail\r\n"
            b"Message-ID: " + message_id + b"\r\n"
            b"Control: cancel " + target + b"\r\n"
            b"Cancel-Key: sha256:" + KEY + b"\r\n\r\n"
            b"cancel\r\n")


def p95(samples):
    ordered = sorted(samples)
    return ordered[min(len(ordered) - 1, int(len(ordered) * 0.95))]


class NativeDeadRun(unittest.TestCase):
    def ihave(self, peer, message_id, payload):
        first, reply = peer.post(payload, verb="IHAVE " + message_id.decode())
        self.assertTrue(first.startswith(b"335 "), (message_id, first))
        self.assertTrue(reply is not None and reply.startswith(b"235 "), (message_id, reply))

    def prepared_node(self, image):
        self.assertGreater(D, 0, "FN_DEAD_RUN_D must leave a nonempty dead run")
        node = Node(self, image, listener=False, control=False, env={
            "FN_PROF_HOOK": None, "FN_PROF_OUT": None, "FN_COUNT_OUT": None,
            "FN_COUNT_SNAPSHOT": None, "FN_COUNT_TRIGGER": None})
        node.store("init", "--profile", "scale", "fn.dr", "fn.ctl", "control.cancel", expect=EXIT_OK)
        configured = native_peer_add(
            image, node.store_path, ["source", "source.invalid", "127.0.0.1", "9", "fn.*",
                                     "-", "127.0.0.1", "true"], node.environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())
        owner, port = node.start_store_owner(once=False)
        with Client(port, timeout=120) as peer:
            self.ihave(peer, b"<ctl-0@dr.invalid>", article(b"<ctl-0@dr.invalid>", b"fn.ctl"))
            self.ihave(peer, b"<floor@dr.invalid>", article(b"<floor@dr.invalid>", b"fn.dr"))
            for i in range(D):
                mid = b"<run-%06d@dr.invalid>" % i
                self.ihave(peer, mid, article(mid, b"fn.dr"))
            for i in range(D):
                mid = b"<run-%06d@dr.invalid>" % i
                cid = b"<run-c-%06d@dr.invalid>" % i
                self.ihave(peer, cid, cancel(cid, mid))
            self.assertEqual(peer.command("GROUP fn.dr").split(),
                             [b"211", b"1", b"1", b"1", b"fn.dr"])
        node.stop(process=owner)
        return node

    @unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
    def test_cancel_and_group_flat_over_a_dead_run(self):
        self.assertGreaterEqual(R, 2 * WINDOW, "flatness needs two disjoint 200-round windows")
        node = self.prepared_node(IMAGE)
        owner, port = node.start_store_owner(once=False)
        with Client(port, timeout=120) as peer:
            stop = threading.Event()
            waits = {"fn.dr": [], "fn.ctl": []}
            errors = []

            def reader():
                try:
                    with Client(port, timeout=30, source="127.0.0.2") as r:
                        while not stop.is_set():
                            for g in ("fn.dr", "fn.ctl"):
                                asked = time.monotonic()
                                status = r.command("GROUP " + g)
                                waits[g].append(time.monotonic() - asked)
                                if not status.startswith(b"211"):
                                    errors.append((g, status))
                                    return
                except Exception as error:
                    errors.append(("exception", repr(error)))

            thread = threading.Thread(target=reader)
            thread.start()
            cancels = []
            try:
                for i in range(R):
                    mid = b"<top-%06d@dr.invalid>" % i
                    cid = b"<top-c-%06d@dr.invalid>" % i
                    self.ihave(peer, mid, article(mid, b"fn.dr"))
                    asked = time.monotonic()
                    self.ihave(peer, cid, cancel(cid, mid))
                    cancels.append(time.monotonic() - asked)
            finally:
                stop.set()
                thread.join(60)
        self.assertFalse(thread.is_alive(), "the reader did not stop")
        self.assertFalse(errors, errors[:3])
        self.assertTrue(waits["fn.dr"] and waits["fn.ctl"], "the reader was never answered")
        first = sum(cancels[:WINDOW]) / WINDOW
        last = sum(cancels[-WINDOW:]) / WINDOW
        dr, ctl = p95(waits["fn.dr"]), p95(waits["fn.ctl"])
        print("DEAD-RUN d={} r={} cancel-first={:.4f}s cancel-last={:.4f}s group-dr-p95={:.4f}s "
              "group-ctl-p95={:.4f}s groups={}".format(D, R, first, last, dr, ctl,
                                                       len(waits["fn.dr"])), flush=True)
        self.assertLess(last, 2 * first, "per-cancel cost grew over the rounds")
        self.assertLess(dr, 2 * ctl + 0.002, "GROUP over the dead run costs more than without one")
        node.stop(process=owner)

    def count_snapshot(self, prefix):
        # A token and END distinguish a fresh, complete snapshot from the
        # preceding one or a file being written.  Never accept a periodic log
        # as the end-of-round observation.
        self.snapshot_token = getattr(self, "snapshot_token", 0) + 1
        token = str(self.snapshot_token)
        request = prefix.with_suffix(".request")
        temporary = prefix.with_suffix(".request.tmp")
        temporary.write_text(token + "\n", encoding="ascii")
        temporary.replace(request)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            path = prefix.with_suffix(".snapshot")
            if path.exists():
                lines = path.read_text(encoding="ascii").splitlines()
                if lines and lines[0] == token and lines[-1] == "END":
                    counts = {}
                    for line in lines[1:-1]:
                        symbol, value = line.split()
                        package, name = symbol.split("::")
                        if package in ("ACL2", "ACL2_*1*_ACL2") and name in COUNT_NAMES:
                            counts[symbol] = int(value)
                    for name in REQUIRED_WRAPS:
                        self.assertIn("ACL2::" + name, counts,
                                      "count hook did not wrap " + name)
                    return {name: sum(value for symbol, value in counts.items()
                                      if symbol.split("::")[1] == name)
                            for name in COUNT_NAMES}
            time.sleep(0.01)
        self.fail("RED-2 count snapshot missing: prof image must load tools/profile/count-hook.lisp")

    @unittest.skipUnless(executable(PROF_IMAGE),
                         "RED-2 executable complexity tooth requires build/fn-host-prof "
                         "(FN_DEAD_RUN_PROF_HOST); build with --images developer,prof")
    def test_group_execution_counts_over_a_lagging_dead_run(self):
        self.assertGreaterEqual(D, 64, "RED-2 mutation tooth needs FN_DEAD_RUN_D >= 64")
        self.assertGreater(R, 0, "RED-2 needs at least one measured round")
        node = self.prepared_node(PROF_IMAGE)
        prefix = node.root / "round-counts"
        stall = node.root / "round-barrier-stall"
        # Only this owner is instrumented; store init, peer setup and the
        # D setup cancels cannot satisfy the observed-branch assertion.
        owner, port = node.start_store_owner(once=False, env={
            "FN_PROF_HOOK": ROOT / "tools/profile/count-hook.lisp",
            "FN_COUNT_OUT": prefix, "FN_COUNT_SNAPSHOT": prefix,
            "FN_COUNT_PREFIXES": ":".join(COUNT_NAMES),
            "FN_NATIVE_TEST_DISK_STALL_FILE": stall})
        groups = 0
        with Client(port, timeout=120) as peer, \
                Client(port, timeout=30, source="127.0.0.2") as reader:
            initial = self.count_snapshot(prefix)
            for i in range(R):
                previous = self.count_snapshot(prefix)
                mid = b"<top-%06d@dr.invalid>" % i
                cid = b"<top-c-%06d@dr.invalid>" % i
                stall.touch()
                try:
                    first = peer.command("IHAVE " + mid.decode())
                    self.assertTrue(first.startswith(b"335 "), (mid, first))
                    peer.send(dot_stuff(article(mid, b"fn.dr")) + b".\r\n")
                    deadline = time.monotonic() + 2
                    observed = False
                    while time.monotonic() < deadline:
                        for group in ("fn.dr", "fn.ctl"):
                            status = reader.command("GROUP " + group)
                            self.assertEqual(status.split(),
                                             [b"211", b"1", b"1", b"1", group.encode()],
                                             "in-flight top escaped the completed reader view")
                            groups += 1
                        now = self.count_snapshot(prefix)
                        probes = now["FN-SCV-IN-XP"] - previous["FN-SCV-IN-XP"]
                        # Check each pair before accepting its branch evidence:
                        # number-wise scans cannot hide among pre-START polls.
                        self.assertLessEqual(probes, COUNT_FACTOR * 2,
                                             "a GROUP pair probed the dead numbers")
                        observed = any(now[name] > previous[name] for name in LINK_NAMES)
                        previous = now
                        if observed:
                            break
                    self.assertTrue(observed, "RED-2 high-in-X branch was not observed in round {}".format(i))
                finally:
                    # Remove only this test's stall file, including on assertion
                    # failure, so the harness can shut down its own owner.
                    stall.unlink()
                reply = peer.line()
                self.assertTrue(reply.startswith(b"235 "), (mid, reply))
                self.ihave(peer, cid, cancel(cid, mid))
            final = self.count_snapshot(prefix)
        delta = {name: final[name] - initial[name] for name in COUNT_NAMES}
        print("DEAD-RUN-COUNTS d={} r={} groups={} counts={} factor={}".format(
            D, R, groups, delta, COUNT_FACTOR), flush=True)
        self.assertGreater(sum(delta[name] for name in LINK_NAMES), 0,
                           "RED-2 lagging-view live-link branch never ran")
        self.assertGreater(delta["FN-SCV-IN-XP"], 0, "membership calls were not observed")
        self.assertLessEqual(delta["FN-SCV-IN-XP"], COUNT_FACTOR * (groups + R),
                             "membership work grew with the dead run")
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
