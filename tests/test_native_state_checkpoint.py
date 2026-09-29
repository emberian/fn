"""The exact-state checkpoint (P3), native, through both entries.

`operator CONFIG store checkpoint` and the developer `store ROOT checkpoint`
open the store as `recover` does, ask ACL2 for the pipeline's setup
(host/store-node-host.lisp `fn-store-sco-publish-setup`: the open's
checkpoint extended over the records after it, or the capture of the whole
history, its schema-3 tables, the estimate and the decision by name) and
write the tables step by step (`fnn-checkpoint-write-steps`) through
`fnn-state-checkpoint-write`, the byte program `fn-bs-scp-program`.  Every later open reads it range by range, selects it
under the profile's K (`fn-sco-select`), reads only the transaction files at
or after its sequence S and opens through `fn-sco-open`
(`fn-sn-recover-from-checkpoint-equals-full-recover`).  A missing or corrupt
checkpoint falls back to full replay, and `status` says which open ran.

The witnesses:

* three articles, a checkpoint at 3, two more: `status` reads
  open=checkpoint:3 suffix=2, and the counts, the configuration, the
  retention ledger and every article agree with the full-replay open of the
  same store with the checkpoint moved aside;
* a corrupt checkpoint (one byte flipped) and a missing one open by full
  replay and say so;
* at every cut of the program (tests/campaign/native_cuts.py
  STATE_CHECKPOINT_CUTS), SIGKILL or EIO, through either entry, the next
  open reads the old checkpoint (S=3) or the new one (S=5), byte for byte,
  as the cut's candidate column says, and opens to the same state.
"""
import hashlib
import os
import re
import signal
import shutil
import sys
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, ROOT, executable, native_image)

sys.path.insert(0, str(ROOT / "tools" / "fixtures"))
import damaged_checkpoint  # noqa: E402

IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
NAME = "store-checkpoint.fnsc"


class StateCheckpointSourceTests(unittest.TestCase):
    def test_the_host_calls_the_keystone_subject_and_writes_the_program(self):
        node_host = (ROOT / "host" / "store-node-host.lisp").read_text(encoding="ascii")
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        recover = native_cuts.host_function(node_host, "fn-store-sn-recover-from-checkpoint")
        # fn-sco-open is fn-sco-finalize of this extension; the open is read
        # off it once (fn-store-sn-open-extended, fn-sco-store-open).
        # records-flip (checkpoint-arena-2): the entry opens over the ROWS the
        # host interned on top of the loaded arena (fnn-recover-suffix-rows);
        # fn-rii-sco-extend is fn-sco-extend (fn-rii-sco-extend-is-sco-extend).
        # snapshot-open-2 (PRF-321): the extension and its open are one call,
        # fn-rii-sco-extend-open (KEYSTONE
        # fn-rii-sco-extend-open-is-extend-then-open: the extension and
        # fn-rii-classified-open of it), opened by fn-store-sn-open-classified
        # (fn-store-sn-open-extended's body).
        self.assertIn("(fn-rii-sco-extend-open checkpoint config-records rows frontier)", recover)
        self.assertNotIn("fn-arena", recover)
        self.assertIn("(fn-store-sn-open-classified", recover)
        rii0 = (ROOT / "books" / "replay-identity-index.lisp").read_text(encoding="ascii")
        self.assertIn("(defthm fn-rii-sco-extend-open-is-extend-then-open", rii0)
        # The open the host takes is fn-sco-store-open over the same
        # arguments, called directly or through the one ACL2 function the
        # host calls in its place (since 2e25e21b fn-sopc-classified-open,
        # books/store-open-pre-c1.lisp, which refuses a pre-C1 control
        # record first and otherwise answers fn-sco-store-open's open).
        extended = native_cuts.host_function(node_host, "fn-store-sn-open-extended")
        # Since flip-bridge the host calls the replay-identity twin
        # fn-rii-classified-open (books/replay-identity-index.lisp), which
        # calls fn-rii-sco-store-open; its keystone
        # fn-rii-classified-open-is-classified-open equates it with
        # fn-sopc-classified-open, which calls fn-sco-store-open.
        self.assertTrue(
            native_cuts.calls_through_book(
                extended, "fn-sco-store-open", "e config-records frontier")
            or native_cuts.calls_through_book(
                extended, "fn-rii-sco-store-open", "e config-records frontier"),
            extended[:400])
        rii = (ROOT / "books" / "replay-identity-index.lisp").read_text(encoding="ascii")
        self.assertIn("(defthm fn-rii-classified-open-is-classified-open", rii)
        # The per-file open went with format 8 (lane log-recovery-2,
        # PKT-838): the log's open over a checkpoint without a log position.
        opened = native_cuts.host_function(io, "fnn-recover-log-from-state-checkpoint")
        self.assertIn("'fn-store-sco-select", opened)
        self.assertIn("(fnn-recover-suffix-rows store suffix config-records)", opened)
        suffix_rows = native_cuts.host_function(io, "fnn-recover-suffix-rows")
        self.assertIn("(fnn-recover-suffix-intern suffix configs 0)", suffix_rows)
        self.assertIn("'fn-store-sn-recover-from-checkpoint", suffix_rows)
        self.assertNotIn("fn-arena-clear", suffix_rows)
        # heap-bounds (B3): the suffix is decoded and interned a chunk at a
        # time on top of the loaded arena (fn-srs-intern-step is the
        # fn-intern-events of fn-scka-recover-rows over any chunking:
        # fn-srs-steps-are-one-step-of-the-concatenation), never whole.
        suffix_intern = native_cuts.host_function(io, "fnn-recover-suffix-intern")
        self.assertIn("'fn-store-sn-recover-records nil configs", suffix_intern)
        self.assertIn("(fnn-recover-record-chunks suffix)", suffix_intern)
        self.assertIn("(fnn-call 'fn-srs-intern-step rows decoded (fnn-live-arena))", suffix_intern)
        self.assertIn("(fnn-core 'fn-srs-rows rows)", suffix_intern)
        self.assertNotIn("fn-arena-clear", suffix_intern)
        self.assertNotIn("(mapcar #'fnn-octet-list suffix)", suffix_intern)
        # rep-wave-d-3: the file is read into the octet buffer as the
        # writer's plan shape, each segment admitted by ACL2 against the
        # profile's bounds before it is read; checkpoint-pipeline (schema 3):
        # the plan is loaded by the tables reader by index over the buffer
        # (fn-store-sco-decode calls fn-sct-load, books/store-checkpoint-
        # tables-reader.lisp; the tables mean the capture,
        # fn-sct-capture-of-tables); no octet list of the file is built.
        plan = native_cuts.host_function(io, "fnn-state-checkpoint-plan")
        self.assertIn("'fn-store-sco-segment-admit", plan)
        self.assertIn("(fnn-octets-append-vector chunk)", plan)
        self.assertNotIn("fnn-octet-list (concatenate", plan)
        load = native_cuts.host_function(io, "fnn-state-checkpoint-load")
        self.assertIn("(fnn-core-buffer-state 'fn-store-sco-decode value)", load)
        self.assertIn("(:schema :schema)", load)
        # records-flip (checkpoint-arena-2): the arena run first
        # (fn-scka-open-run), the payloads sealed by the host through the
        # guard-verified fn-scka-seal-n a bounded number per call, then the
        # tables (fn-scka-finish calls fn-sct-load): fn-scka-load's three
        # calls, KEYSTONE fn-scka-load-of-written-file.
        node_decode = native_cuts.host_function(node_host, "fn-store-sco-decode")
        self.assertIn("(fn-scka-open-run plan fn-octets)", node_decode)
        self.assertIn("(list :arena (nth 1 o) (nth 2 o) (nth 3 o))", node_decode)
        node_finish = native_cuts.host_function(node_host, "fn-store-sco-decode-finish")
        self.assertIn("(fn-scka-finish (car load) (cadr load) i end fn-octets)", node_finish)
        self.assertIn("(fn-sct-capture-of-tables (cadr loaded))", node_finish)
        load_arena = native_cuts.host_function(io, "fnn-state-checkpoint-load-arena")
        self.assertIn("(fnn-call 'fn-arena-clear arena)", load_arena)
        self.assertIn("(fnn-call 'fn-scka-seal-n i end k octets arena)", load_arena)
        self.assertIn("'fn-store-sco-decode-finish", load_arena)
        node_admit = native_cuts.host_function(node_host, "fn-store-sco-segment-admit")
        self.assertIn("(fn-sccr-admit-segment header total", node_admit)
        node_select = native_cuts.host_function(node_host, "fn-store-sco-select")
        # (fn-scka-select-named: fn-sco-select-named with the arena
        # refusal named, books/store-checkpoint-arena-load.lisp)
        self.assertIn("(fn-scka-select-named status sequence count", node_select)
        command = native_cuts.host_function(io, "fnn-command-state-checkpoint")
        # checkpoint-pipeline: the verb is the SAME pipeline as the owner's
        # thread: ACL2 decides by name before anything is allocated
        # (fn-store-sco-publish-setup -> fn-ockp-setup), then the batch loop
        # (fnn-checkpoint-write-steps: fn-ockp-step per step, the step's
        # frames written straight from the publication buffer) inside the
        # same byte program's staged writer.
        # Since log-recovery (2026-09-27) the verb and `store compact' share
        # one publication, fnn-state-checkpoint-publish-steps (the log's
        # rotation first, the covered segments' drop after the install).
        self.assertIn("(fnn-state-checkpoint-publish-steps", command)
        self.assertNotIn("fnn-plan-octets", command)
        publish = native_cuts.host_function(io, "fnn-state-checkpoint-publish-steps")
        self.assertIn("'fn-store-sco-publish-setup", publish)
        self.assertIn("(fnn-checkpoint-write-steps fd setup segment sequence", publish)
        self.assertIn("(fnn-state-checkpoint-write", publish)
        self.assertNotIn("fnn-plan-octets", publish)
        steps = native_cuts.host_function(io, "fnn-checkpoint-write-steps")
        self.assertIn("(fnn-call 'fn-ockp-step setup state +fnn-checkpoint-batch-rows+", steps)
        self.assertIn("(fnn-plan-write-all fd frames st)", steps)
        self.assertIn("(fnn-core 'fn-ockp-donep state)", steps)
        self.assertIn("(fnn-checkpoint-write-arena-steps fd arun sequence", steps)
        arena_steps = native_cuts.host_function(io, "fnn-checkpoint-write-arena-steps")
        self.assertIn("(fnn-call 'fn-scka-write-step state n count sequence", arena_steps)
        self.assertIn("(fnn-plan-write-all fd frames st)", arena_steps)
        node_setup = native_cuts.host_function(node_host, "fn-store-sco-publish-setup")
        # checkpoint-arena-3: NEXT is the open's E extended over the rows
        # after it (fn-scka-next-checkpoint, no second canonicalization);
        # the arena run's setup and sources come from the bounded walk.
        self.assertIn("(fn-scka-next-checkpoint e (len lens) configs records fn-arena)", node_setup)
        self.assertIn("(fn-scka-publication-setup next (fn-sf-frontier (fn-sn-files st))", node_setup)
        self.assertIn("(fn-scka-lens-setup lens segment-octets)", node_setup)
        self.assertIn("(fn-scka-initial-state srcs (nth 1 ws) 0)", node_setup)
        publish_steps = native_cuts.host_function(io, "fnn-state-checkpoint-publish-steps")
        self.assertIn("(fnn-core-state 'fn-store-sco-pass-begin)", publish_steps)
        self.assertIn("(fnn-core-arena-state 'fn-store-sco-pass-step", publish_steps)
        pass_step = native_cuts.host_function(node_host, "fn-store-sco-pass-step")
        self.assertIn("(fn-scka-srcs-n (nth 0 pass) n (nth 1 pass) (nth 2 pass) fn-arena)", pass_step)
        native_cuts.verify_state_checkpoint_cut_map()


# books/frame-octets.lisp *fn-frame-trailer-octets*: the chained seal that
# ends every FNSC segment.
FRAME_TRAILER_OCTETS = 32


class StateCheckpointFixture(verbs.NativeOperatorVerbFixture):
    image = IMAGE
    listener = True

    def setUp(self):
        if not executable(self.image):
            self.skipTest("{} is required".format(self.image))
        super().setUp()
        self.node.image = self.image

    headroom = verbs.NativeOperatorCapacityTests.headroom
    post_many = verbs.NativeOperatorCapacityTests.post_many

    def op(self, *words, env=None):
        return self.operator(*words, env=env)

    def store_cli(self, *words, env=None):
        return self.node.store(*words, env=env, timeout=600)

    def checkpoint(self, entry="operator", env=None):
        if entry == "operator":
            return self.op("store", "checkpoint", env=env)
        return self.store_cli("checkpoint", env=env)

    def path(self):
        return self.store / NAME

    def digest(self):
        return hashlib.sha256(self.path().read_bytes()).hexdigest() if self.path().exists() else None

    def post(self, ids):
        self.node.start()
        self.assertEqual(self.post_many(ids), ["240 article received OK"] * len(ids))
        self.node.stop()

    def open_line(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        lines = [l for l in status.stdout.decode("ascii").splitlines() if l.startswith("open=")]
        self.assertEqual(len(lines), 1, status.stdout.decode())
        return lines[0]

    def checkpoint_file_line(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        lines = [l for l in status.stdout.decode("ascii").splitlines()
                 if l.startswith("checkpoint-file")]
        self.assertEqual(len(lines), 1, status.stdout.decode())
        return lines[0]

    def observation(self):
        """What an open reconstructs, through four verbs that each reopen."""
        words = []
        for verb in (("status",), ("retention",), ("config",)):
            out = self.store_cli(*verb)
            self.assertEqual(out.returncode, EXIT_OK, out.stderr.decode())
            # How the store opened and the checkpoint file's size and
            # time are not reconstructed state.
            words.append([l for l in out.stdout.decode("ascii").splitlines()
                          if not l.startswith(("open=", "checkpoint-file"))])
        for message_id in self.ids:
            out = self.store_cli("inspect", message_id)
            words.append((out.returncode, hashlib.sha256(out.stdout).hexdigest()))
        return words

    # T8: a checkpoint's publication drops the log segments it
    # covers, so with the checkpoint gone or refused no full replay is left
    # and the open refuses by name.  A test that compares an open from the
    # checkpoint with the full replay keeps the covered segments through a
    # second hard link made before the publication (the writer only
    # appends to a segment, and the drop unlinks journal/'s name), shows
    # the refusal, then links them back.
    def keep_log(self):
        kept = self.root / "kept-log"
        kept.mkdir(exist_ok=True)
        for segment in (self.store / "journal").iterdir():
            if segment.is_file() and not (kept / segment.name).exists():
                os.link(segment, kept / segment.name)

    def dropped_segments(self):
        kept = self.root / "kept-log"
        return sorted(p.name for p in kept.iterdir()
                      if not (self.store / "journal" / p.name).exists())

    def refused_then_restore_log(self):
        """The open without a usable checkpoint over the dropped log refuses
        by name; the kept segments are linked back.  The reason."""
        self.assertTrue(self.dropped_segments())
        status = self.op("status")
        self.assertNotEqual(status.returncode, EXIT_OK, status.stdout.decode())
        match = re.search(rb"open refused reason=([a-z-]+)", status.stderr)
        self.assertIsNotNone(match, status.stderr.decode())
        for name in self.dropped_segments():
            os.link(self.root / "kept-log" / name, self.store / "journal" / name)
        return match.group(1).decode("ascii")

    def init_with_checkpoint_at_three(self, entry="operator"):
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.ids = ["<scp-{}@example.invalid>".format(n) for n in range(5)]
        self.post(self.ids[:3])
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.checkpoint_file_line(), "checkpoint-file=absent")
        self.keep_log()
        made = self.checkpoint(entry)
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertIn(b"checkpoint sequence=3", made.stdout)
        # T8: the segments the checkpoint covers are gone.
        self.assertTrue(self.dropped_segments())
        self.assertRegex(self.checkpoint_file_line(),
                         r"^checkpoint-file octets=[1-9][0-9]* modified=[1-9][0-9]*$")
        self.assertEqual(int(self.checkpoint_file_line().split()[1].split("=")[1]),
                         self.path().stat().st_size)
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=0")
        self.post(self.ids[3:])
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")


class StateCheckpointTests(StateCheckpointFixture):
    def test_checkpoint_open_equals_full_replay(self):
        self.init_with_checkpoint_at_three()
        from_checkpoint = self.observation()
        aside = self.root / "aside.fnsc"
        self.path().rename(aside)
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.observation(), from_checkpoint)
        self.assertEqual(self.headroom()["transactions-used"], 5)
        aside.rename(self.path())
        # The next checkpoint extends the one the open used.
        made = self.checkpoint()
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertIn(b"checkpoint sequence=5 ", made.stdout)
        self.assertIn(b"open=checkpoint:3 suffix=2", made.stdout)
        self.assertEqual(self.open_line(), "open=checkpoint:5 suffix=0")
        self.assertEqual(self.observation(), from_checkpoint)

    def test_a_corrupt_checkpoint_falls_back_to_full_replay(self):
        self.init_with_checkpoint_at_three()
        expected = self.observation()
        data = bytearray(self.path().read_bytes())
        # The last octet before the file's final trailer: the last segment's
        # chunk (or, when that chunk is empty, the previous trailer the chain
        # seals over), so the flipped bit is under a seal whichever table the
        # segment carries.  The file's middle octet was a chunk octet under
        # schema 2 (one run of segments); under schema 3 (four runs, each with
        # a 37-octet header) it can land in a header's length field, which the
        # reader refuses by name as `checkpoint-exceeds-bound' before it can
        # read the seal (hbox native-r2, checkpoint-pipeline-2): a different
        # refusal, the same fallback.
        data[-(FRAME_TRAILER_OCTETS + 1)] ^= 0x01
        self.path().write_bytes(bytes(data))
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(), "open=full-replay reason=corrupt")
        self.assertEqual(self.observation(), expected)
        truncated = bytes(data[: len(data) - 7])
        self.path().write_bytes(truncated)
        self.assertEqual(self.open_line(), "open=full-replay reason=corrupt")
        self.path().unlink()
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.observation(), expected)

    def test_a_file_without_the_arena_run_is_refused_by_name(self):
        """Records flip (checkpoint-arena-2): the file opens with the arena
        run.  The same file with that run cut away is the tables-only file a
        writer before the flip produced (the four runs chained from the
        genesis, intact): the open refuses it BY NAME, reason=checkpoint-arena
        (books/store-checkpoint-arena-load.lisp fn-scka-select-named), never
        `corrupt', replays the journal, and reconstructs the same state."""
        self.init_with_checkpoint_at_three()
        expected = self.observation()
        data = self.path().read_bytes()
        # FNSC segment: magic(4) schema(1) index count length sequence (u64 LE
        # each), the chunk, the 32-octet trailer; the first segment's count
        # is the arena run's segment count.
        count = int.from_bytes(data[13:21], "little")
        at = 0
        for _ in range(count):
            length = int.from_bytes(data[21 + at:29 + at], "little")
            at += 37 + length + FRAME_TRAILER_OCTETS
        self.assertEqual(data[:4], b"FNSC")
        self.assertEqual(data[37:41], b"fnA1")
        self.assertEqual(data[at:at + 4], b"FNSC")
        self.path().write_bytes(data[at:])
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(), "open=full-replay reason=checkpoint-arena")
        self.assertEqual(self.observation(), expected)

    def test_a_checkpoint_past_the_profile_bound_is_refused_by_name(self):
        # rep-wave-d-3: the first segment's LENGTH field (u64 LE at octet 21)
        # claims a chunk past the profile's segment bound.  ACL2 refuses the
        # segment before the host reads it (fn-sccr-admit-segment), the
        # open replays the journal, and `status' names the refusal.
        self.init_with_checkpoint_at_three()
        expected = self.observation()
        good = self.path().read_bytes()
        data = bytearray(good)
        data[21:29] = b"\xff" * 8
        self.path().write_bytes(bytes(data))
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(),
                         "open=full-replay reason=checkpoint-exceeds-bound")
        self.assertEqual(self.observation(), expected)
        # A LENGTH within the segment bound but not the chunk's: corrupt.
        data = bytearray(good)
        data[21] ^= 0x01
        self.path().write_bytes(bytes(data))
        self.assertEqual(self.open_line(), "open=full-replay reason=corrupt")
        self.path().write_bytes(good)
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")
        self.assertEqual(self.observation(), expected)

    def test_a_watermark_past_the_bound_refuses_the_start_by_name(self):
        """The open's article-number check (books/owner-number-bound.lisp
        fn-onb-open-okp, host/owner-host.lisp fn-owner-install-extended,
        host/native/owner.lisp fnn-owner-recover-core).  No verb sets a
        watermark and replay only increments one, so the damaged store is
        the published checkpoint re-written by ACL2 with the group's next
        article number at 2147483648 (tools/fixtures/damaged_checkpoint.py).
        The file still decodes and verifies -- the Store opens from it --
        and the owner refuses to start on it BY NAME; the same file with the
        watermark at the bound, 2147483647, starts."""
        self.init_with_checkpoint_at_three()
        good = self.path().read_bytes()
        try:
            damaged_checkpoint.acl2_executable()
        except damaged_checkpoint.FixtureError as error:
            self.skipTest(str(error))
        group, old = damaged_checkpoint.damage(self.path(), 2147483648)
        self.assertTrue(0 < old < 2147483647, (group, old))
        self.assertNotEqual(self.path().read_bytes(), good)
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")
        process, err = self.node.try_start()
        self.assertEqual(process.returncode, EXIT_REFUSED, err)
        self.assertIn("is damaged: an article-number watermark exceeds RFC 3977's bound "
                      "(2147483647)", err)
        # At the bound: the same re-write, the start proceeds.
        self.path().write_bytes(good)
        self.assertEqual(damaged_checkpoint.damage(self.path(), 2147483647), (group, old))
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")
        process, err = self.node.try_start()
        self.assertIsNone(err, "a watermark at the bound starts")
        self.node.stop(process=process)

    def test_a_running_owner_refuses_the_verb(self):
        self.init_with_checkpoint_at_three()
        self.node.start()
        held = self.checkpoint()
        self.assertNotEqual(held.returncode, EXIT_OK)
        self.node.stop()


class StateCheckpointCutTests(StateCheckpointFixture):
    """Every STATE_CHECKPOINT_CUTS cut, SIGKILL and EIO, through both entries."""
    image = DEVELOPER

    def run_cut(self, cut, action, entry):
        self.init_with_checkpoint_at_three(entry)
        old = self.digest()
        expected = self.observation()
        died = self.checkpoint(entry, env={
            "FN_NATIVE_STATE_CHECKPOINT_FAULT": "{}:{}".format(cut.name, action)})
        if action == "kill":
            self.assertEqual(died.returncode, -signal.SIGKILL, died.stderr.decode())
        else:
            wanted = EXIT_REFUSED if cut.candidate == "old" else EXIT_UNCERTAIN
            self.assertEqual(died.returncode, wanted, died.stderr.decode())
        line = self.open_line()
        allowed = {"old": {"open=checkpoint:3 suffix=2"},
                   "new": {"open=checkpoint:5 suffix=0"},
                   "either": {"open=checkpoint:3 suffix=2", "open=checkpoint:5 suffix=0"}}
        self.assertIn(line, allowed[cut.candidate])
        if line.startswith("open=checkpoint:3"):
            self.assertEqual(self.digest(), old)
        # A death before the rename leaves a staging orphan, which a
        # read-only status reports; the writer's recover sweeps it.  The
        # reconstructed state is compared after that sweep.
        recovered = self.op("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertEqual(list((self.store / "staging").iterdir()), [])
        self.assertEqual(self.observation(), expected)
        retried = self.checkpoint(entry)
        self.assertEqual(retried.returncode, EXIT_OK, retried.stderr.decode())
        self.assertEqual(self.open_line(), "open=checkpoint:5 suffix=0")
        return line

    def test_a_killed_owner_reopens_from_the_checkpoint_without_replay(self):
        """Records flip (checkpoint-arena-2): the checkpoint carries the arena,
        so after the serving owner dies (SIGKILL) the next open reads the
        checkpoint (its arena run sealed from the file, the suffix interned on
        top), replays only the suffix, and reconstructs what the full replay
        does."""
        self.init_with_checkpoint_at_three("store")
        expected = self.observation()
        owner = self.node.start()
        owner.kill()
        owner.wait(timeout=60)
        owner.finish()
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")
        self.assertEqual(self.observation(), expected)
        aside = self.root / "aside.fnsc"
        self.path().rename(aside)
        self.assertEqual(self.refused_then_restore_log(), "checkpoint-damaged")
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.observation(), expected)

    def test_a_kill_inside_the_arena_run_never_trusts_the_torn_file(self):
        """The arena run is the file's first steps: a kill after the run's
        head step (FN_NATIVE_CHECKPOINT_BATCH_FAULT=0:kill) leaves the staged
        file unrenamed, and the next open reads the old checkpoint, byte for
        byte, never the torn one."""
        self.init_with_checkpoint_at_three("store")
        old = self.digest()
        expected = self.observation()
        died = self.checkpoint("store", env={"FN_NATIVE_CHECKPOINT_BATCH_FAULT": "0:kill"})
        self.assertEqual(died.returncode, -signal.SIGKILL, died.stderr.decode())
        self.assertEqual(self.open_line(), "open=checkpoint:3 suffix=2")
        self.assertEqual(self.digest(), old)
        recovered = self.op("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertEqual(list((self.store / "staging").iterdir()), [])
        self.assertEqual(self.observation(), expected)

    def test_every_cut_reopens_with_the_old_or_the_new_checkpoint(self):
        seen = {}
        for cut in native_cuts.STATE_CHECKPOINT_CUTS:
            for action in ("kill", "eio"):
                for entry in ("operator", "store"):
                    with self.subTest(cut=cut.name, action=action, entry=entry):
                        if self.store.exists():
                            shutil.rmtree(self.store)
                        seen[(cut.name, action, entry)] = self.run_cut(cut, action, entry)
        print("state checkpoint cuts:", sorted(seen.items()))


if __name__ == "__main__":
    unittest.main()
