"""The ONE fence boundary of every owner quantum and worker thread, native
(lane failure-scope, t45; r71 F1/F2; sweep S016, S017, S019; r72 F6;
books/failure-scope.lisp).  Each case injects a fault or an uncertain outcome
on a developer image and shows the fence: the owner stops with the exit code
ACL2 classifies (3 uncertain, 4 fault), the line names it, the control reply's
`owner fenced' is true, and a fresh process recovers and serves.

* the committer thread (S016): an injected store fault off any owner quantum
  stops the owner as a fault (exit 4), an injected uncertain outcome fences
  it (exit 3) -- never a silent thread death with the batch in flight;
* the publication thread (S019): an EIO at the checkpoint's root barrier
  after its rename (`state-checkpoint-replaced:eio', the install's uncertain
  interval) fences the owner (exit 3) -- never `CHECKPOINT auto failed' and
  serving on;
* the reclaim pass (r71 F1, S017): the same cut inside the install/swap
  quantum fences the owner BEFORE the mutex is released; `store reclaim
  --recorded' exits 3 and the owner's `owner fenced' line precedes the
  control reply's;
* the node secret (r72 F6): an EIO at the directory barrier after the
  secret's publication is uncertain (exit 3), not a raw OS fault (exit 4).
"""
import os
import re
import shutil
import unittest

from tests import test_native_checkpoint_auto as auto
from tests import test_native_expiry as expiry
from tests.native_harness import (EXIT, EXIT_FAULT, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN,
                                  EXIT_USAGE, Client, Node, article, native_image, requires,
                                  scratch)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


class CommitterBoundaryTests(auto.AutoCheckpointFixture):
    """FN_NATIVE_COMMITTER_FAULT raises once on the committer thread, off any
    owner quantum, before its next commit pipeline (host/native/owner.lisp
    fnn-owner-committer-test-fault)."""

    def committer_failure(self, selector, expected_exit, line):
        self.init_development()
        owner = self.node.start(env={"FN_NATIVE_COMMITTER_FAULT": selector})
        mid = "<committer-{}@example.invalid>".format(selector)
        # The submission wakes the committer; its first act is the injected
        # condition.  The reply (if any) is not the witness: the exit is.
        self.node.post(mid, article(mid), expect=None)
        self.node.exited(expected_exit, timeout=180, process=owner)
        log = owner.stderr.since(0)
        self.assertIn(line, log, log.decode("utf-8", "replace"))
        # The old handler returned nil here: the thread died, nothing said.
        self.assertNotIn(b"stopping: the close is not joined: the committer is alive", log)
        # A fresh process: the unacknowledged article is absent, and a new
        # commit is accepted.
        self.node.start()
        absent = self.store_cli("inspect", mid)
        self.assertEqual(absent.returncode, EXIT_REFUSED, absent.stderr.decode())
        accepted = self.node.post(mid, article(mid))
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        self.node.stop()

    def test_an_injected_committer_fault_stops_the_owner_as_a_fault(self):
        self.committer_failure("fault", EXIT_FAULT,
                               b"owner core/store fault; process stopped: FN_NATIVE_COMMITTER_FAULT")

    def test_an_injected_committer_uncertain_outcome_fences_the_owner(self):
        self.committer_failure("indeterminate", EXIT_UNCERTAIN,
                               b"committer uncertain; recovery required: FN_NATIVE_COMMITTER_FAULT")


class PublicationBoundaryTests(auto.AutoCheckpointFixture):
    """The publication thread's boundary (sweep S019): the checkpoint's rename
    landed and the root's barrier failed (fn-bs-scp-program's replaced cut,
    an EIO): the outcome is uncertain and the owner fences."""

    def test_an_uncertain_checkpoint_install_in_the_publication_fences_the_owner(self):
        self.init_development()
        self.keep_log()
        owner = self.node.start(env={"FN_NATIVE_STATE_CHECKPOINT_FAULT":
                                     "state-checkpoint-replaced:eio"})
        self.ids = self.post_batch(0, 6)  # Below automatic publication's threshold.
        with self.node.session() as client:
            expected = [client.article(mid) for mid in self.ids]
        asked = self.op("store", "compact")
        self.assertEqual(asked.returncode, EXIT_OK, asked.stderr.decode())
        self.node.exited(EXIT_UNCERTAIN, timeout=180, process=owner)
        log = owner.stderr.since(0)
        self.assertIn(b"CHECKPOINT auto uncertain; recovery required:", log,
                      log.decode("utf-8", "replace"))
        # Before: `CHECKPOINT auto failed sequence=N: ...' and serving on.
        self.assertNotIn(b"CHECKPOINT auto failed sequence=", log)
        # A fresh process recovers (the old or the new checkpoint, never a
        # torn one) and serves every acknowledged article.
        self.node.start()
        with self.node.session() as client:
            self.assertEqual([client.article(mid) for mid in self.ids], expected)
        later = "<after-publication-fence@example.invalid>"
        accepted = self.node.post(later, article(later))
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        self.node.stop()


@requires(DEVELOPER)
class ReclaimInstallFenceTests(expiry.ExpiryMixin, unittest.TestCase):
    """r71 F1 / sweep S017: the reclaim pass's install/swap quantum runs inside
    the fence boundary; an uncertain install fences the owner before the
    mutex is released, and the control reply's `owner fenced' is true."""
    image = DEVELOPER

    def recorded_base(self, name="rbase"):
        base = self.filled(name)
        base.operator("retention", "expire", expiry.GROUP, "purge", "30", expect=EXIT.OK)
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

    def test_an_uncertain_reclaim_install_fences_the_owner_before_the_reply(self):
        node = self.copy_of(self.recorded_base(), "live")
        owner = node.start(timeout=600, env={"FN_NATIVE_STATE_CHECKPOINT_FAULT":
                                             "state-checkpoint-replaced:eio"})
        try:
            done = self.reclaim(node, "--recorded", expect=None)
            self.assertEqual(done.returncode, EXIT.UNCERTAIN, done.stdout + done.stderr[-800:])
            self.assertNotIn(b"installed", done.stdout, done.stdout)
            node.exited(EXIT.UNCERTAIN, timeout=300, process=owner)
            log = owner.stderr.since(0)
            text = log.decode("utf-8", "replace")
            fenced = log.find(b"owner quantum uncertain; owner fenced:")
            replied = log.find(b"control request uncertain; owner fenced:")
            self.assertGreaterEqual(fenced, 0, text)
            self.assertGreaterEqual(replied, 0, text)
            # The quantum fenced under its mutex; only then was the reply made.
            self.assertLess(fenced, replied, text)
            self.assertNotIn(b"RECLAIM installed", log)
        finally:
            node.stop(expect=None, grace=300)
        # A fresh process: the durable publication is the new one or the old
        # one, never served over by the old state; the store opens and serves.
        status = node.operator("status", timeout=600)
        self.assertEqual(status.returncode, EXIT.OK, status.stderr[-600:])
        replies = self.served(node, ["STAT %s" % expiry.msgid("n0"),
                                     "STAT %s" % expiry.msgid("p0")])
        self.assertTrue(replies[0].startswith(b"223"), replies)
        self.assertTrue(replies[1].startswith(b"430") or replies[1].startswith(b"223"), replies)


@requires(DEVELOPER)
class NodeSecretBoundaryTests(unittest.TestCase):
    """r72 F6: the directory barrier after a node secret's publication."""

    def setUp(self):
        self.root = scratch(self, "fn-fsb-")

    def test_a_barrier_failure_after_the_secrets_publication_is_uncertain(self):
        node = Node(self, DEVELOPER, root=self.root / "node")
        node.operator("init", "fn.test", timeout=600, expect=EXIT.OK)
        fault = {"FN_NATIVE_NODE_SECRET_FAULT": "fsync-dir:eio"}
        created = node.store("node-secret", "create", env=fault, timeout=600, expect=None)
        self.assertEqual(created.returncode, EXIT.UNCERTAIN, created.stderr[-600:])
        self.assertIn(b"node secret creation outcome is indeterminate", created.stderr)
        # The secret was published (its link landed): a second create refuses
        # by name, and a rotation under the same fault is uncertain too.
        again = node.store("node-secret", "create", timeout=600, expect=None)
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stderr[-600:])
        rotated = node.store("node-secret", "rotate", env=fault, timeout=600, expect=None)
        self.assertEqual(rotated.returncode, EXIT.UNCERTAIN, rotated.stderr[-600:])
        self.assertIn(b"node secret rotation outcome is indeterminate", rotated.stderr)
        # Without the fault the next rotation completes.
        rotated = node.store("node-secret", "rotate", timeout=600, expect=None)
        self.assertEqual(rotated.returncode, EXIT.OK, rotated.stderr[-600:])

    def test_production_refuses_the_selector_before_dispatch(self):
        production = native_image("FN_NATIVE_HOST")
        if not os.access(production, os.X_OK):
            self.skipTest("production image is required for the startup gate witness")
        node = Node(self, DEVELOPER, root=self.root / "prod")
        result = node.operator("run", image=production,
                               env={"FN_NATIVE_NODE_SECRET_FAULT": "fsync-dir:eio"})
        self.assertEqual(result.returncode, EXIT_USAGE, result.stderr.decode())
        self.assertIn(b"FN_NATIVE_NODE_SECRET_FAULT", result.stderr)


if __name__ == "__main__":
    unittest.main()
