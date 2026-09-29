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
import re
import time
import unittest

from tests.campaign import native_cuts
from tests import test_native_state_checkpoint as scp
from tests.native_harness import EXIT_OK, ROOT, native_image

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")

CHECKPOINT_AUTO = re.compile(rb"CHECKPOINT auto sequence=(\d+) suffix=(\d+) octets=(\d+) steps=(\d+) ms=(\d+)")
CHECKPOINT_DEFERRED = re.compile(
    rb"CHECKPOINT deferred reason=([a-z-]+) estimate=(\d+) budget=(\d+) sequence=(\d+) ms=(\d+)")
CHECKPOINT_ANY = re.compile(rb"CHECKPOINT ")


class AutoCheckpointSourceTests(unittest.TestCase):
    def test_the_publication_thread_calls_the_stream_entry_over_its_own_buffer(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        owner_host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        publish = native_cuts.host_function(owner, "fnn-owner-publish-captured")
        # checkpoint-pipeline: NEXT (fn-ock-next-checkpoint), then the setup
        # (fn-ockp-setup: the tables, the estimate, the decision BEFORE any
        # allocation), then the batch loop over the PUBLICATION buffer, never
        # the served one; each step's frames written through the unchanged
        # byte program; the list entry and the whole-file plan are gone.
        # records flip (checkpoint-arena-2): NEXT and the setup come from
        # fn-owner-sco-prepare (host/owner-host.lisp), which READS the live
        # arena: fn-scka-next-checkpoint (the base extended over the canonical
        # suffix, KEYSTONE fn-scka-next-checkpoint-is-capture), the arena
        # run's setup and fn-scka-publication-setup (fn-ockp-setup with the
        # decision over the whole file); the arena run is written first.
        self.assertIn("(fnn-core 'fn-owner-sco-prepare base base-payloads configs records", publish)
        self.assertIn("(fnn-live-octets-pub) arun)", publish)
        prepare = native_cuts.host_function(owner_host, "fn-owner-sco-prepare")
        # (the base is kept stripped of its event index and restored here:
        # fn-scka-restore-base-of-strip-of-capture, PKT-PRS-2)
        self.assertIn("(fn-scka-next-checkpoint (fn-scka-restore-base base) h0 configs records", prepare)
        self.assertIn("(fn-scka-publication-setup next frontier revision log seg budget free", prepare)
        # checkpoint-arena-3: the arena run's setup from the host's bounded
        # walk (fn-scka-srcs-n: lengths and sources in one pass, no alpha
        # in the write), not a second walk of the rows.
        self.assertIn("(fn-scka-lens-setup (reverse (nth 1 walked)) seg)", prepare)
        self.assertIn("(fn-scka-initial-state (reverse (nth 2 walked)) (nth 1 ws) 0)", prepare)
        self.assertIn("(fnn-checkpoint-walk records)", publish)
        walk = native_cuts.host_function(io, "fnn-checkpoint-walk")
        self.assertIn("(fnn-core 'fn-scka-srcs-n (first walk) +fnn-checkpoint-batch-rows+", walk)
        self.assertIn("(fnn-live-octets-pub)", publish)
        self.assertNotIn("(fnn-live-octets)", publish)
        self.assertNotIn("'fn-ock-publication ", publish)
        self.assertNotIn("'fn-ock-publication-stream", publish)
        self.assertIn("(fnn-checkpoint-write-steps", publish)
        self.assertIn("(fnn-state-checkpoint-write", publish)
        self.assertIn("CHECKPOINT deferred reason=", publish)
        self.assertNotIn("fnn-plan-octets", publish)
        # The decision's due half and the budget's derivation are ACL2's, on
        # the due path; the space is observed once and handed to both.
        due = native_cuts.host_function(owner_host, "fn-owner-sco-due")
        self.assertIn("(fn-ock-publication-blockedp", due)
        self.assertIn("(fn-owner-sco-budget override profile)", due)
        self.assertIn("(fn-ockp-space free)", due)
        capture = native_cuts.host_function(owner_host, "fn-owner-sco-capture")
        self.assertIn("(fn-owner-sco-budget override profile)", capture)
        self.assertIn("(fn-sf-frontier (fn-sn-files st))", capture)
        budget = native_cuts.host_function(owner_host, "fn-owner-sco-budget")
        self.assertIn("(fn-ock-capture-budget profile)", budget)
        maybe = native_cuts.host_function(owner, "fnn-owner-maybe-publish")
        self.assertEqual(maybe.count("(fnn-checkpoint-budget-test-override nil)"), 2)
        self.assertIn("(fnn-disk-free-octets (fnn-owner-service-store service))", maybe)
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

    def init_development(self):
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())

    def post_batch(self, first, count):
        ids = ["<auto-{}@example.invalid>".format(n) for n in range(first, first + count)]
        self.assertEqual(self.post_many(ids), ["240 article received OK"] * len(ids))
        return ids

    def nudge(self, timeout):
        """Open a connection and read the greeting (the owner publishes
        between accepts)."""
        with self.node.session(timeout=timeout, greeting=None):
            pass

    def owner_line(self, owner, pattern, deadline=180.0, nudge=True):
        """The first stderr line of OWNER matching PATTERN within DEADLINE
        seconds, nudging now and then, or None.  OWNER's stderr is drained
        from birth (tests/native_harness.py); each complete line is read
        once, from this owner's cursor on, and only the owner's exit fails
        the wait."""
        end = time.monotonic() + deadline
        offset = getattr(owner, "stderr_cursor", 0)
        while True:
            text = owner.stderr.since(offset)
            for line in text[:text.rfind(b"\n") + 1].splitlines(keepends=True):
                offset += len(line)
                match = pattern.search(line)
                if match:
                    owner.stderr_cursor = offset
                    return match
            owner.stderr_cursor = offset
            status = owner.poll()
            if status is not None:
                self.fail("the owner exited with status {} before the line; stderr: {}"
                          .format(status, owner.stderr.tail().decode("utf-8", "replace")))
            if time.monotonic() >= end:
                return None
            time.sleep(0.25)
            if nudge:
                self.nudge(30)

    def status_lines(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        return status.stdout.decode("ascii").splitlines()


class AutoCheckpointTests(AutoCheckpointFixture):
    def test_the_owner_publishes_after_half_k_and_the_file_reopens_as_the_full_replay(self):
        self.init_development()
        # the segments the publication will drop (T8) stay readable
        self.keep_log()
        owner = self.node.start()
        self.ids = self.post_batch(0, 64)
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication within the deadline")
        sequence, suffix, octets, steps, ms = (int(line.group(i)) for i in range(1, 6))
        self.assertEqual((sequence, suffix), (64, 64))
        self.assertGreater(octets, 0)
        # The four tables are written in at least four steps (one per table
        # at the development profile's batch), never as one file.
        self.assertGreaterEqual(steps, 4)
        self.node.stop(process=owner)
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
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.observation(), from_checkpoint)
        aside.rename(self.path())
        # The verb (the same fn-sccb-plan over the same frozen checkpoint)
        # republishes the automatic publication byte for byte.
        made = self.checkpoint()
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertIn("checkpoint sequence=64 octets={} steps=".format(octets).encode("ascii"),
                      made.stdout)
        self.assertEqual(self.digest(), published)
        self.assertEqual(self.open_line(), "open=checkpoint:64 suffix=0")

    def test_a_configuration_record_on_a_full_store_after_a_checkpoint_reopens(self):
        """The operability review's walk F3 (2026-09-29): posts refused on a
        full transaction budget leave their txids unrecorded, so a
        configuration record accepted next stands above every event; the
        open's frontier is joined with the configuration history's
        (fn-store-cfg-next-txid), or the reopen over the checkpoint refused
        `checkpoint-damaged' and no verb could open the store."""
        created = self.op("init", "--profile", "development", "--max-transactions", "12",
                          "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start()
        outcomes = []
        for n in range(13):
            message_id = "<full-{}@example.invalid>".format(n)
            payload = ("From: a <a@example.invalid>\r\nNewsgroups: fn.test\r\n"
                       "Subject: full {}\r\nMessage-ID: {}\r\n"
                       "Date: Tue, 29 Sep 2026 00:00:00 +0000\r\n\r\nbody\r\n"
                       .format(n, message_id)).encode("ascii")
            done = self.node.post(message_id, payload)
            outcomes.append(done.returncode)
        self.assertIn(EXIT_OK, outcomes)
        self.assertEqual(outcomes[-1], 1, "the thirteenth post is refused: the budget is full")
        self.assertIsNotNone(self.owner_line(owner, CHECKPOINT_AUTO),
                             "no automatic publication within the deadline")
        made = self.op("group", "create", "fn.live")
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.node.stop(process=owner)
        lines = self.status_lines()
        self.assertTrue(any(line.startswith("open=checkpoint:") for line in lines), lines)
        again = self.node.start()
        self.node.stop(process=again)

    def test_a_publication_past_the_budget_is_deferred_by_name_and_serving_continues(self):
        self.init_development()
        budget = 1024
        owner = self.node.start(env={"FN_NATIVE_CHECKPOINT_BUDGET_TEST": str(budget)})
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
        self.node.stop(process=owner)
        self.assertFalse(self.path().exists())
        # Offline: no owner, no publisher, no deferral; the store opens by
        # full replay with every article.
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.checkpoint_file_line(), "checkpoint-file=absent")
        self.assertEqual(self.headroom()["transactions-used"], 66)
        # A fresh owner under the profile's own budget publishes at once (the
        # suffix is past K/2 and the deferral was this process's).
        owner = self.node.start()
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication after the restart")
        self.assertEqual(int(line.group(1)), 66)
        self.node.stop(process=owner)
        self.assertEqual(self.open_line(), "open=checkpoint:66 suffix=0")

    def test_a_kill_between_two_batches_reopens_with_the_old_checkpoint_and_sweeps_the_stage(self):
        # SCN-129 (design 2.4): the pipeline writes many segments between the
        # `created' and `written' cuts of fn-bs-scp-program; a death between
        # two steps is the `created' cut's verdict (old), never a torn file.
        # First a durable checkpoint at 8 (the old one, by the verb: the same
        # pipeline in a fresh process), then a publication, due when the
        # suffix reaches K/2 = 64 (fn-ock-publication-duep), killed after its
        # first step's frames were written.  The old checkpoint is early so
        # that the 64 posts that make the publication due stay well under the
        # development profile's transaction budget (hbox native-r2: an old
        # checkpoint at 64 needed 128 posts and the budget refused the last
        # of them with 441 before the publication was due).
        self.init_development()
        owner = self.node.start()
        self.ids = self.post_batch(0, 8)
        self.node.stop(process=owner)
        made = self.checkpoint()
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        old = self.digest()
        self.assertIsNotNone(old)
        self.assertEqual(self.open_line(), "open=checkpoint:8 suffix=0")
        owner = self.node.start(env={"FN_NATIVE_CHECKPOINT_BATCH_FAULT": "0:kill"})
        self.ids += self.post_batch(8, 64)
        # The owner is killed by its own publication thread after the first
        # step; wait for the process to end.
        deadline = time.monotonic() + 180.0
        while owner.poll() is None and time.monotonic() < deadline:
            time.sleep(0.25)
            try:
                self.nudge(5)
            except (OSError, EOFError):
                pass
        self.assertIsNotNone(owner.poll(), "the owner survived the batch fault")
        self.node.stop(expect=None, process=owner)
        # A staging orphan (the partial file) exists; the old checkpoint is
        # what the open reads, byte for byte; the writer's recover sweeps.
        self.assertEqual(self.digest(), old)
        self.assertEqual(self.open_line(), "open=checkpoint:8 suffix=64")
        recovered = self.op("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertEqual(list((self.store / "staging").iterdir()), [])
        self.assertEqual(self.digest(), old)
        # A fresh owner is due at once (suffix 64) and publishes the whole
        # history at 72.
        owner = self.node.start()
        line = self.owner_line(owner, CHECKPOINT_AUTO)
        self.assertIsNotNone(line, "no automatic publication after the restart")
        self.assertEqual(int(line.group(1)), 72)
        self.node.stop(process=owner)
        self.assertEqual(self.open_line(), "open=checkpoint:72 suffix=0")


if __name__ == "__main__":
    unittest.main()
