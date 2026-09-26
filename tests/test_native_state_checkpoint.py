"""The exact-state checkpoint (P3), native, through both entries.

`operator CONFIG store checkpoint` and the developer `store ROOT checkpoint`
open the store as `recover` does, ask ACL2 for the checkpoint file
(host/store-node-host.lisp `fn-store-sco-publish-octets`: the open's
checkpoint extended over the records after it, or the capture of the whole
history) and write it through `fnn-state-checkpoint-write`, the byte program
`fn-bs-scp-program`.  Every later open reads it range by range, selects it
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
from pathlib import Path
import signal
import subprocess
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
IMAGE = verbs.IMAGE
DEVELOPER = verbs.DEVELOPER
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = verbs.EXIT_OK, verbs.EXIT_REFUSED, verbs.EXIT_UNCERTAIN
NAME = "store-checkpoint.fnsc"


class StateCheckpointSourceTests(unittest.TestCase):
    def test_the_host_calls_the_keystone_subject_and_writes_the_program(self):
        node_host = (ROOT / "host" / "store-node-host.lisp").read_text(encoding="ascii")
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        recover = native_cuts.host_function(node_host, "fn-store-sn-recover-from-checkpoint")
        # fn-sco-open is fn-sco-finalize of this extension; the open is read
        # off it once (fn-store-sn-open-extended, fn-sco-store-open).
        self.assertIn("(fn-sco-extend checkpoint config-records records)", recover)
        self.assertIn("(fn-store-sn-open-extended", recover)
        extended = native_cuts.host_function(node_host, "fn-store-sn-open-extended")
        self.assertIn("(fn-sco-store-open e config-records frontier)", extended)
        opened = native_cuts.host_function(io, "fnn-recover-from-state-checkpoint")
        self.assertIn("'fn-store-sco-select", opened)
        self.assertIn("'fn-store-sn-recover-from-checkpoint", opened)
        self.assertIn("'fn-store-sco-covered-count", opened)
        # rep-wave-d-3: the file is read into the octet buffer as the
        # writer's plan shape, each segment admitted by ACL2 against the
        # profile's bounds before it is read, and decoded by index
        # (fn-store-sco-decode over the buffer, books/store-checkpoint-reader.lisp
        # fn-sccr-decode-plan); no octet list of the file is built.
        plan = native_cuts.host_function(io, "fnn-state-checkpoint-plan")
        self.assertIn("'fn-store-sco-segment-admit", plan)
        self.assertIn("(fnn-octets-append-vector chunk)", plan)
        self.assertNotIn("fnn-octet-list (concatenate", plan)
        load = native_cuts.host_function(io, "fnn-state-checkpoint-load")
        self.assertIn("(fnn-core-buffer-state 'fn-store-sco-decode value)", load)
        node_decode = native_cuts.host_function(node_host, "fn-store-sco-decode")
        self.assertIn("(fn-sccr-decode-plan plan fn-octets)", node_decode)
        node_admit = native_cuts.host_function(node_host, "fn-store-sco-segment-admit")
        self.assertIn("(fn-sccr-admit-segment header total", node_admit)
        command = native_cuts.host_function(io, "fnn-command-state-checkpoint")
        # rep-wave-d-2: the publication is a plan over the octet buffer
        # (fn-store-sco-publish-plan, books/store-checkpoint-buffer.lisp
        # fn-sccb-plan); the host assembles the plan's octets from the
        # buffer's array (fnn-plan-octets, fn-sccb-plan-octets transcribed)
        # and writes them through the same byte program as before.
        self.assertIn("'fn-store-sco-publish-plan", command)
        self.assertIn("(fnn-plan-octets (first answer))", command)
        self.assertIn("(fnn-state-checkpoint-write store octets)", command)
        node_plan = native_cuts.host_function(node_host, "fn-store-sco-publish-plan")
        self.assertIn("(fn-sccb-plan (fn-sco-freeze next) segment-octets fn-octets)", node_plan)
        native_cuts.verify_state_checkpoint_cut_map()


class StateCheckpointFixture(verbs.NativeOperatorVerbFixture):
    image = IMAGE

    def setUp(self):
        if not verbs.executable(self.image):
            self.skipTest("{} is required".format(self.image))
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = verbs.free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")

    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap
    headroom = verbs.NativeOperatorCapacityTests.headroom
    post_many = verbs.NativeOperatorCapacityTests.post_many
    stop = verbs.NativeOperatorCapacityTests.stop

    def op(self, *words, env=None):
        return self.operator(*words, image=self.image, env=env)

    def store_cli(self, *words, env=None):
        return subprocess.run(
            [str(self.image), "--fn", "store", str(self.store), *words],
            cwd=ROOT, env=env or verbs.environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=600, check=False)

    def checkpoint(self, entry="operator", env=None):
        if entry == "operator":
            return self.op("store", "checkpoint", env=env)
        return self.store_cli("checkpoint", env=env)

    def path(self):
        return self.store / NAME

    def digest(self):
        return hashlib.sha256(self.path().read_bytes()).hexdigest() if self.path().exists() else None

    def post(self, ids):
        owner = self.start_owner(self.image)
        self.assertEqual(self.post_many(ids), ["240 article received OK"] * len(ids))
        self.stop(owner)

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

    def init_with_checkpoint_at_three(self, entry="operator"):
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.ids = ["<scp-{}@example.invalid>".format(n) for n in range(5)]
        self.post(self.ids[:3])
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
        self.assertEqual(self.checkpoint_file_line(), "checkpoint-file=absent")
        made = self.checkpoint(entry)
        self.assertEqual(made.returncode, EXIT_OK, made.stderr.decode())
        self.assertIn(b"checkpoint sequence=3", made.stdout)
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
        data[len(data) // 2] ^= 0x01
        self.path().write_bytes(bytes(data))
        self.assertEqual(self.open_line(), "open=full-replay reason=corrupt")
        self.assertEqual(self.observation(), expected)
        truncated = bytes(data[: len(data) - 7])
        self.path().write_bytes(truncated)
        self.assertEqual(self.open_line(), "open=full-replay reason=corrupt")
        self.path().unlink()
        self.assertEqual(self.open_line(), "open=full-replay reason=absent")
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

    def test_a_running_owner_refuses_the_verb(self):
        self.init_with_checkpoint_at_three()
        owner = self.start_owner(self.image)
        held = self.checkpoint()
        self.assertNotEqual(held.returncode, EXIT_OK)
        self.stop(owner)


class StateCheckpointCutTests(StateCheckpointFixture):
    """Every STATE_CHECKPOINT_CUTS cut, SIGKILL and EIO, through both entries."""
    image = DEVELOPER

    def run_cut(self, cut, action, entry):
        self.init_with_checkpoint_at_three(entry)
        old = self.digest()
        expected = self.observation()
        env = verbs.environment()
        env["FN_NATIVE_STATE_CHECKPOINT_FAULT"] = "{}:{}".format(cut.name, action)
        died = self.checkpoint(entry, env=env)
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

    def test_every_cut_reopens_with_the_old_or_the_new_checkpoint(self):
        seen = {}
        for cut in native_cuts.STATE_CHECKPOINT_CUTS:
            for action in ("kill", "eio"):
                for entry in ("operator", "store"):
                    with self.subTest(cut=cut.name, action=action, entry=entry):
                        if self.store.exists():
                            subprocess.run(["rm", "-rf", str(self.store)], check=True)
                        seen[(cut.name, action, entry)] = self.run_cut(cut, action, entry)
        print("state checkpoint cuts:", sorted(seen.items()))


if __name__ == "__main__":
    unittest.main()
