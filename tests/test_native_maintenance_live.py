"""Row S3 (lane operability-2): maintenance while serving.

`recover' and `store inspect' used to open the store under its lock and
answer `store is already locked' on a running node; `status' and `health'
on a stopped store replayed the whole log on every call.  Now
(books/owner-maintenance-request.lisp):

* `recover' on a running owner is accepted by name (the owner's open
  recovered the store; its status follows), never a second open;
* `store inspect ID' on a running owner is the owner's own lookup, and the
  line printed is the offline verb's (KEYSTONE
  fn-omr-inspect-live-is-the-offline-report);
* `status' on a stopped store reads the checkpoint header and the journal's
  sizes: `stopped checkpoint=N journal-octets=B transactions-at-most=M'
  (KEYSTONE fn-omr-transactions-at-most-bounds-the-count: M is never below
  the replayed count); `status --replay' is the report over the replayed
  log; `health' on a stopped store carries the same lines under its
  not-running header.

Run with a native image (tests.native_harness): FN_NATIVE_IMAGE=... python3
-m unittest tests.test_native_maintenance_live
"""

import re
import unittest

from tests import test_native_checkpoint_auto as auto
from tests.native_harness import EXIT_OK

STOPPED = re.compile(rb"^stopped checkpoint=(none|\d+) journal-octets=(\d+) transactions-at-most=(\d+)$", re.M)
TRANSACTIONS = re.compile(rb"^transactions=(\d+) ", re.M)


class MaintenanceLiveTests(auto.AutoCheckpointFixture):

    def test_recover_and_inspect_answer_on_the_running_owner_and_a_stopped_status_reads_the_header(self):
        self.init_development()
        self.keep_log()
        owner = self.node.start()
        self.ids = self.post_batch(0, 3)
        # `recover' on the running owner: accepted by name, then the owner's
        # own status (a `transactions=' line the owner answered).
        recovered = self.op("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertIn(b"recover accepted owner=serving", recovered.stdout)
        self.assertNotIn(b"already locked", recovered.stdout + recovered.stderr)
        self.assertIsNotNone(TRANSACTIONS.search(recovered.stdout), recovered.stdout)
        self.assertEqual(int(TRANSACTIONS.search(recovered.stdout).group(1)), 3)
        # `store inspect' on the running owner: the owner's lookup, rendered
        # as the offline verb renders it (accepted / absent, exit 0 / 1).
        found = self.op("store", "inspect", self.ids[0])
        self.assertEqual(found.returncode, EXIT_OK, found.stderr.decode())
        self.assertIn(b"accepted " + self.ids[0].encode("ascii"), found.stdout)
        self.assertIn(b"an article is stored here", found.stdout)
        absent = self.op("store", "inspect", "<never-posted@fn.example.invalid>")
        self.assertEqual(absent.returncode, 1, absent.stderr.decode())
        self.assertIn(b"absent <never-posted@fn.example.invalid>", absent.stdout)
        self.assertNotIn(b"already locked", absent.stdout + absent.stderr)
        # serving continued
        self.ids += self.post_batch(3, 2)
        self.node.stop(process=owner)
        # A stopped store's status is its checkpoint header's and its
        # journal's sizes; the bound covers the replayed count.
        stopped = self.op("status")
        self.assertEqual(stopped.returncode, EXIT_OK, stopped.stderr.decode())
        line = STOPPED.search(stopped.stdout)
        self.assertIsNotNone(line, stopped.stdout)
        self.assertIsNone(TRANSACTIONS.search(stopped.stdout), stopped.stdout)
        self.assertIn(b"\nprofile ", stopped.stdout)
        replayed = self.op("status", "--replay")
        self.assertEqual(replayed.returncode, EXIT_OK, replayed.stderr.decode())
        exact = int(TRANSACTIONS.search(replayed.stdout).group(1))
        self.assertEqual(exact, 5)
        self.assertGreaterEqual(int(line.group(3)), exact)
        # The offline inspect still answers, from the store.
        offline = self.op("store", "inspect", self.ids[0])
        self.assertEqual(offline.returncode, EXIT_OK, offline.stderr.decode())
        self.assertIn(b"an article is stored here", offline.stdout)
        # `health' on the stopped store: the not-running header, then the
        # same stopped lines; nothing replayed.
        health = self.op("health")
        self.assertIn(b"state=not-running", health.stdout)
        self.assertIsNotNone(STOPPED.search(health.stdout), health.stdout)
        # After a checkpoint the header names the covered count.
        owner = self.node.start()
        asked = self.op("store", "checkpoint")
        self.assertEqual(asked.returncode, EXIT_OK, asked.stderr.decode())
        published = self.owner_line(owner, auto.CHECKPOINT_AUTO)
        self.assertIsNotNone(published, "the requested publication did not run")
        self.node.stop(process=owner)
        stopped = self.op("status")
        self.assertEqual(stopped.returncode, EXIT_OK, stopped.stderr.decode())
        line = STOPPED.search(stopped.stdout)
        self.assertIsNotNone(line, stopped.stdout)
        self.assertEqual(line.group(1), b"5")
        self.assertGreaterEqual(int(line.group(3)), 5)

    def test_inspect_group_lists_the_memberships_live_and_offline(self):
        """Row S3d (lane operability-5): `store inspect --group GROUP` prints
        the group's memberships, article numbers to Message-IDs, from the
        archive the running owner serves, and the same lines offline from
        the checkpoint and its suffix; a group the node does not carry is
        refused by name, exit 1 (books/owner-inspect-group.lisp)."""
        self.init_development()
        self.keep_log()
        owner = self.node.start()
        ids = self.post_batch(0, 3)

        def lines(count):
            return [("inspect group=fn.test members=%d" % count).encode("ascii")] + [
                ("%d %s" % (n + 1, ids[n])).encode("ascii") for n in range(count)]

        live = self.op("store", "inspect", "--group", "fn.test")
        self.assertEqual(live.returncode, EXIT_OK, live.stderr.decode())
        self.assertEqual(live.stdout.splitlines()[:4], lines(3), live.stdout)
        self.assertNotIn(b"already locked", live.stdout + live.stderr)
        unknown = self.op("store", "inspect", "--group", "fn.nosuch")
        self.assertEqual(unknown.returncode, 1, unknown.stderr.decode())
        self.assertIn(b"refused unknown-group group=fn.nosuch", unknown.stdout)
        # A checkpoint, then two more posts: the offline report reads the
        # checkpoint and its suffix.
        asked = self.op("store", "checkpoint")
        self.assertEqual(asked.returncode, EXIT_OK, asked.stderr.decode())
        self.assertIsNotNone(self.owner_line(owner, auto.CHECKPOINT_AUTO),
                             "the requested publication did not run")
        ids += self.post_batch(3, 2)
        self.node.stop(process=owner)
        offline = self.op("store", "inspect", "--group", "fn.test")
        self.assertEqual(offline.returncode, EXIT_OK, offline.stderr.decode())
        self.assertEqual(offline.stdout.splitlines()[:6], lines(5), offline.stdout)
        unknown = self.op("store", "inspect", "--group", "fn.nosuch")
        self.assertEqual(unknown.returncode, 1, unknown.stderr.decode())
        self.assertIn(b"refused unknown-group group=fn.nosuch", unknown.stdout)
        # Serving again: the owner's report carries the suffix too.
        owner = self.node.start()
        live = self.op("store", "inspect", "--group", "fn.test")
        self.assertEqual(live.returncode, EXIT_OK, live.stderr.decode())
        self.assertEqual(live.stdout.splitlines()[:6], lines(5), live.stdout)
        self.node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
