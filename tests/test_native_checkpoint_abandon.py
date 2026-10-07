"""RL-02, native: a checkpoint publication that captured and ended before
its history's NEXT existed releases its slot, and ACL2 classifies the ending
by what could make another attempt meaningful
(books/owner-publication-lifecycle.lisp; the coordinator's ruling D52).

Before the fix the done step cleared the slot (fn-owner-sco-inflight) only
when NEXT existed, so a history image refused by name left it set for the
run: no automatic checkpoint, every `store compact' answered "coalesced", the
record log without bound.  Releasing alone would re-arm a full history walk
and a log rotation on every POST.

The refusal is forced on a real store by the developer-only selector
FN_NATIVE_CHECKPOINT_IMAGE_REFUSAL (host/native/io.lisp
fnn-checkpoint-image-refusal-test, a labelled MUTATION witness: ACL2's
finished history image answered as refused by name).  A development
profile, K = 128, so the owner publishes after 64 POSTs.

* image-count (not a dependency): one `CHECKPOINT auto abandoned' line naming
  the reason and class=blocked; no further CHECKPOINT line on more POSTs (no
  storm); `store compact' refused as blocked (not coalesced); `status' and
  `health' name the deferral; a restart (the record is the owner's) publishes.
* pending-suffix (a dependency): class=await-change; a commit inside the
  30 s backoff does not re-arm it; once the backoff has elapsed after the
  history advanced, the owner's maintenance retries with no further POST, and
  the second attempt counts attempts=2.  (That the clock alone, without the
  advance, never re-arms it is ACL2's fn-opl-await-change-needs-the-history-
  to-advance and the raw witness's case 4.)
"""
import re
import time
import unittest

from tests.native_harness import EXIT_OK
from tests.test_native_checkpoint_auto import (AutoCheckpointFixture, CHECKPOINT_ANY,
                                               CHECKPOINT_AUTO)

ABANDONED = re.compile(
    rb"CHECKPOINT auto abandoned sequence=(\d+) reason=([a-z-]+) class=([a-z-]+) "
    rb"attempts=(\d+) not-before-ms=(\d+)")
STUCK = "a refused publication left fn-owner-sco-inflight set for the run"


class CheckpointAbandonTests(AutoCheckpointFixture):
    def abandoned(self, owner, deadline=180.0):
        line = self.owner_line(owner, ABANDONED, deadline=deadline)
        self.assertIsNotNone(line, STUCK + " (no CHECKPOINT auto abandoned line)")
        return (int(line.group(1)), line.group(2).decode("ascii"),
                line.group(3).decode("ascii"), int(line.group(4)), int(line.group(5)))

    def test_a_refused_history_image_releases_the_slot_and_blocks_by_name(self):
        self.init_development()
        owner = self.node.start(env={"FN_NATIVE_CHECKPOINT_IMAGE_REFUSAL": "image-count"})
        self.ids = self.post_batch(0, 64)
        sequence, reason, klass, attempts, _ = self.abandoned(owner)
        self.assertEqual((sequence, reason, klass, attempts),
                         (64, "blocked-history-image-refused", "blocked", 1))
        # No storm: more commits start no walk and no rotation.
        self.ids += self.post_batch(64, 2)
        self.assertIsNone(self.owner_line(owner, CHECKPOINT_ANY, deadline=5.0))
        # The operator is told by name: blocked, never "coalesced" behind a
        # publication that ended long ago.
        asked = self.op("store", "compact")
        said = (asked.stdout + asked.stderr).decode("utf-8", "replace")
        self.assertNotIn("coalesced", said, STUCK)
        self.assertIn("blocked", said)
        lines = [l for l in self.status_lines() if l.startswith("checkpoint-file")]
        self.assertEqual(len(lines), 1, lines)
        self.assertIn(" deferred=blocked-history-image-refused ", lines[0] + " ")
        health = self.op("health")
        text = health.stdout.decode("ascii")
        self.assertIn("\ncheckpoint-deferred held reason=blocked-history-image-refused ", text)
        self.assertTrue(20 <= health.returncode <= 29, (health.returncode, text))
        self.node.stop(process=owner)
        # The record is the owner's: a restart without the refusal publishes.
        owner = self.node.start()
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication after the restart")
        self.assertEqual(int(line.group(1)), 66)
        self.node.stop(process=owner)

    def test_a_pending_suffix_waits_for_the_history_and_the_backoff(self):
        self.init_development()
        owner = self.node.start(env={"FN_NATIVE_CHECKPOINT_IMAGE_REFUSAL": "pending-suffix"})
        self.ids = self.post_batch(0, 64)
        started = time.monotonic()
        sequence, reason, klass, attempts, _ = self.abandoned(owner)
        self.assertEqual((sequence, reason, klass, attempts),
                         (64, "retry-on-history-advance-image-suffix", "await-change", 1))
        # A commit inside the backoff does not re-arm it.
        self.ids += self.post_batch(64, 1)
        self.assertIsNone(self.owner_line(owner, CHECKPOINT_ANY, deadline=5.0))
        # Once the backoff has elapsed after that advance, the owner's
        # maintenance retries by itself, with no further POST: the second
        # attempt, at the advanced count.
        sequence, reason, klass, attempts, _ = self.abandoned(owner, deadline=60.0)
        self.assertGreaterEqual(time.monotonic() - started, 25.0)
        self.assertEqual((sequence, klass, attempts), (65, "await-change", 2))
        self.node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
