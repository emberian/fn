"""The owner's AUTOMATIC checkpoint publication, native (lane
checkpoint-capture-stream, 2026-09-26; PKT-492; PRF-183; SCN-112).

The served owner publishes the state checkpoint itself, between accepts,
when the suffix since the newest durable checkpoint reaches half the
profile's K (`fn-ock-publication-duep`, books/owner-checkpoint-open.lisp).
Before this lane the publication encoded the file as octet lists
(`fn-ock-publication`) and killed the owner by heap exhaustion at N of about
33,000 x 2 KiB (planning/evidence/service-envelope-2026-09-26.md).  Now the
publication thread calls `fn-ock-publication-stream`
(books/owner-checkpoint-stream.lisp) with the PUBLICATION buffer, a second
octet stobj congruent to the served one: ACL2 first decides BY NAME whether
the file fits the profile's checkpoint budget (the reader's file bound), then
encodes the frozen checkpoint into that buffer once and answers a plan whose
octets are the list codec's file (`fn-ock-publication-stream-writes-the-file`,
by `fn-sccb-plan-is-file-octets`); the host writes the plan straight from the
buffer through the unchanged byte program (`fnn-state-checkpoint-write`,
`fn-bs-scp-program`'s five cuts).

The witnesses (a development-profile store, K = 128, so the owner publishes
after 64 POSTs):

* the owner logs `CHECKPOINT auto sequence=64 suffix=64 octets=N ms=M`, the
  file on disk has N octets, the next open reads it (`open=checkpoint:64
  suffix=0`), the state it opens to equals the full replay's with the file
  moved aside, and the offline verb (`store checkpoint`, the same
  `fn-sccb-plan`) republishes it byte for byte;
* under a checkpoint budget the file exceeds (the developer-only selector
  FN_NATIVE_CHECKPOINT_BUDGET_TEST stands in for the profile's; the
  comparison and both numbers are ACL2's) the owner logs `CHECKPOINT
  deferred reason=exceeds-budget estimate=E budget=B sequence=64 ms=M`,
  writes nothing, keeps serving, does not retry at the next commit (the
  deferral blocks until the budget covers E), and `status` names the
  deferral on its checkpoint-file line while the owner runs.
"""
import hashlib
import re
import select
import socket
import time
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs
from tests import test_native_state_checkpoint as scp

ROOT = verbs.ROOT
DEVELOPER = verbs.DEVELOPER
EXIT_OK = verbs.EXIT_OK

CHECKPOINT_AUTO = re.compile(rb"CHECKPOINT auto sequence=(\d+) suffix=(\d+) octets=(\d+) ms=(\d+)")
CHECKPOINT_DEFERRED = re.compile(
    rb"CHECKPOINT deferred reason=([a-z-]+) estimate=(\d+) budget=(\d+) sequence=(\d+) ms=(\d+)")
CHECKPOINT_ANY = re.compile(rb"CHECKPOINT ")


class AutoCheckpointSourceTests(unittest.TestCase):
    def test_the_publication_thread_calls_the_stream_entry_over_its_own_buffer(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        owner_host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        publish = native_cuts.host_function(owner, "fnn-owner-publish-captured")
        # The keystone's subject, with the publication buffer, never the
        # served one; the plan's octets written from that buffer through the
        # unchanged byte program; the list entry no longer called.
        self.assertIn("(fnn-call 'fn-ock-publication-stream base configs records", publish)
        self.assertIn("(fnn-live-octets-pub)", publish)
        self.assertNotIn("(fnn-live-octets)", publish)
        self.assertNotIn("'fn-ock-publication ", publish)
        self.assertIn("(fnn-plan-write-all fd plan (fnn-live-octets-pub))", publish)
        self.assertIn("(fnn-state-checkpoint-write", publish)
        self.assertIn("CHECKPOINT deferred reason=", publish)
        self.assertNotIn("fnn-plan-octets", publish)
        # The decision's due half and the budget's derivation are ACL2's, on
        # the due path.
        due = native_cuts.host_function(owner_host, "fn-owner-sco-due")
        self.assertIn("(fn-ock-publication-blockedp", due)
        self.assertIn("(fn-owner-sco-budget override profile)", due)
        capture = native_cuts.host_function(owner_host, "fn-owner-sco-capture")
        self.assertIn("(fn-owner-sco-budget override profile)", capture)
        budget = native_cuts.host_function(owner_host, "fn-owner-sco-budget")
        self.assertIn("(fn-ock-capture-budget profile)", budget)
        maybe = native_cuts.host_function(owner, "fnn-owner-maybe-publish")
        self.assertEqual(maybe.count("(fnn-checkpoint-budget-test-override nil)"), 2)
        self.assertNotIn("fnn-checkpoint-budget-test-override", publish)
        # The staged write's two cuts still bracket the write, whether a
        # vector or the plan writer is handed in; the cut map is unchanged.
        staged = native_cuts.host_function(io, "fnn-write-staged-at")
        self.assertLess(staged.index("(fnn-at store created)"), staged.index("(funcall contents fd)"))
        self.assertLess(staged.index("(funcall contents fd)"), staged.index("(fnn-at store written)"))
        native_cuts.verify_state_checkpoint_cut_map()


class AutoCheckpointFixture(scp.StateCheckpointFixture):
    image = DEVELOPER
    ids = ()

    def setUp(self):
        super().setUp()
        self.control = self.root / "control.sock"

    def init_development(self):
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())

    def post_batch(self, first, count):
        ids = ["<auto-{}@example.invalid>".format(n) for n in range(first, first + count)]
        self.assertEqual(self.post_many(ids), ["240 article received OK"] * len(ids))
        return ids

    def owner_line(self, owner, pattern, deadline=180.0, nudge=True):
        """The first stderr line of OWNER matching PATTERN within DEADLINE
        seconds, opening a connection now and then (the owner publishes
        between accepts), or None."""
        seen = []
        end = time.monotonic() + deadline
        while time.monotonic() < end:
            ready = select.select([owner.stderr], [], [], 0.25)[0]
            if ready:
                line = owner.stderr.readline()
                if not line:
                    self.fail("the owner closed its stderr; lines so far: {!r}".format(seen))
                seen.append(line)
                match = pattern.search(line)
                if match:
                    return match
                continue
            if nudge:
                with socket.create_connection(("127.0.0.1", self.port), timeout=30) as conn:
                    conn.recv(256)
        return None

    def status_lines(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        return status.stdout.decode("ascii").splitlines()


class AutoCheckpointTests(AutoCheckpointFixture):
    def test_the_owner_publishes_after_half_k_and_the_file_reopens_as_the_full_replay(self):
        self.init_development()
        owner = self.start_owner(self.image)
        self.ids = self.post_batch(0, 64)
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication within the deadline")
        sequence, suffix, octets, ms = (int(line.group(i)) for i in range(1, 5))
        self.assertEqual((sequence, suffix), (64, 64))
        self.assertGreater(octets, 0)
        self.stop(owner)
        # The file the owner wrote has the octets ACL2 named (the estimate,
        # the plan's octets and the list codec's file are one length).
        self.assertTrue(self.path().exists())
        self.assertEqual(self.path().stat().st_size, octets)
        published = self.digest()
        self.assertEqual(self.open_line(), "open=checkpoint:64 suffix=0")
        self.assertEqual(self.checkpoint_file_line(),
                         "checkpoint-file octets={} modified={}".format(
                             octets, int(self.path().stat().st_mtime)))
        from_checkpoint = self.observation()
        aside = self.root / "aside.fnsc"
        self.path().rename(aside)
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.observation(), from_checkpoint)
        aside.rename(self.path())
        # The verb (the same fn-sccb-plan over the same frozen checkpoint)
        # republishes the automatic publication byte for byte.
        made = self.checkpoint()
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertIn("checkpoint sequence=64 octets={} ".format(octets).encode("ascii"),
                      made.stdout)
        self.assertEqual(self.digest(), published)
        self.assertEqual(self.open_line(), "open=checkpoint:64 suffix=0")

    def test_a_publication_past_the_budget_is_deferred_by_name_and_serving_continues(self):
        self.init_development()
        budget = 1024
        owner = self.start_owner(self.image,
                                 extra_env={"FN_NATIVE_CHECKPOINT_BUDGET_TEST": str(budget)})
        self.ids = self.post_batch(0, 64)
        line = self.owner_line(owner, CHECKPOINT_DEFERRED)
        self.assertIsNotNone(line, "no deferral within the deadline")
        reason = line.group(1).decode("ascii")
        estimate, named_budget, sequence, ms = (int(line.group(i)) for i in range(2, 6))
        self.assertEqual(reason, "exceeds-budget")
        self.assertEqual((named_budget, sequence), (budget, 64))
        self.assertGreater(estimate, budget)
        # Nothing was written, and the owner keeps serving.
        self.assertFalse(self.path().exists())
        self.ids += self.post_batch(64, 2)
        # The deferral blocks the retry at the next commits: no further
        # CHECKPOINT line within a few accepts.
        self.assertIsNone(self.owner_line(owner, CHECKPOINT_ANY, deadline=5.0))
        # The running owner's status names the deferral on its
        # checkpoint-file line, with ACL2's two numbers.
        lines = [l for l in self.status_lines() if l.startswith("checkpoint-file")]
        self.assertEqual(lines, ["checkpoint-file=absent deferred=exceeds-budget estimate={} budget={}"
                                 .format(estimate, budget)])
        self.assertEqual(self.headroom()["transactions-used"], 66)
        self.stop(owner)
        self.assertFalse(self.path().exists())
        # Offline: no owner, no publisher, no deferral; the store opens by
        # full replay with every article.
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.checkpoint_file_line(), "checkpoint-file=absent")
        self.assertEqual(self.headroom()["transactions-used"], 66)
        # A fresh owner under the profile's own budget publishes at once (the
        # suffix is past K/2 and the deferral was this process's).
        owner = self.start_owner(self.image)
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication after the restart")
        self.assertEqual(int(line.group(1)), 66)
        self.stop(owner)
        self.assertEqual(self.open_line(), "open=checkpoint:66 suffix=0")


if __name__ == "__main__":
    unittest.main()
