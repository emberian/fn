"""Checkpoint generation publication, selection, crash cuts and recovery.

These tests run the real store, the real ACL2 bridge and real syscalls.
Process-death cases kill a helper's process group after a named cut with
the OS cache retained; they claim nothing about power loss.
"""
import contextlib
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import checkpoint, run_store  # noqa: E402
from tools.run_store import Acl2Store, Store  # noqa: E402


def post_many(store_path, count, prefix):
    """Post `count` articles through one live owner and one bridge."""
    store, bridge, records = run_store.open_live_store(store_path, writable=True)
    try:
        # `group_codes` takes the Store: it reads the allocation domain the
        # core handed it at recover, not the configuration dict.
        codes = run_store.group_codes(["fn.letters"], store)
        for index in range(count):
            msgid = "<{}-{}@example.invalid>".format(prefix, index).encode("ascii")
            payload = "article {} of {}\r\n".format(index, prefix).encode("ascii")
            charge = run_store.conservative_charge(payload)
            run_store.validate_post_boundary(msgid, payload, codes, charge, store.config)
            # `fn-store-sn-existing-action` answers `:absent` when nothing
            # is stored under this identity; `duplicate` and `conflict` are
            # the two the production path in `run_store.post` refuses on.
            # `"new"` is not in the model vocabulary any more.
            assert bridge.existing_action(msgid, payload, codes) == "absent"
            store.advance_frontier(bridge, bridge.next_txid())
            obligation, subject, evidence = run_store.metadata(msgid, payload)
            action = bridge.prepare(msgid, payload, codes, obligation, subject,
                                    evidence, charge)
            assert action == "prepared", action
            record = bridge.pending_record()
            store.publish(bridge, len(records), record)
            store.fenced = True
            store.finish(bridge)
            records.append(record)
        return len(records)
    finally:
        bridge.close()
        store.close()


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-checkpoint-test-")
        self.root = Path(self.temp.name)
        self.path = self.root / "store"
        self.invoke("tools/run_store.py", "init")

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, script, command, *args, expected=0, env=None):
        environment = dict(os.environ)
        if env:
            environment.update(env)
        result = subprocess.run(
            [sys.executable, script, "--store", str(self.path), command, *map(str, args)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            env=environment, timeout=600)
        if result.returncode != expected:
            self.fail("{} {} returned {}\nstdout={}\nstderr={}".format(
                script, command, result.returncode,
                result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result.stdout.decode("utf-8", "replace")

    @contextlib.contextmanager
    def recovered(self, differential=True):
        previous = os.environ.get("FN_CHECKPOINT_DIFFERENTIAL")
        os.environ["FN_CHECKPOINT_DIFFERENTIAL"] = "1" if differential else ""
        host = Store(self.path, writable=True)
        bridge = None
        try:
            host.acquire()
            bridge = Acl2Store()
            records = host.recover(bridge)
            self.assertFalse(host.fenced)
            yield host, bridge, records
        finally:
            if bridge is not None:
                bridge.close()
            host.close()
            if previous is None:
                del os.environ["FN_CHECKPOINT_DIFFERENTIAL"]
            else:
                os.environ["FN_CHECKPOINT_DIFFERENTIAL"] = previous

    # -- publication, selection and the differential -----------------------

    def test_publish_select_and_suffix_replay_on_128_records(self):
        # The store's configured transaction bound is 128: the checkpoint
        # covers 120 records and the suffix is the remaining 8.
        self.assertEqual(post_many(self.path, 120, "base"), 120)
        output = self.invoke("tools/checkpoint.py", "publish", "--select")
        self.assertIn("published generation=0 records=120 selected=yes", output)
        self.assertEqual(post_many(self.path, 8, "suffix"), 128)
        output = self.invoke("tools/run_store.py", "recover",
                             env={"FN_CHECKPOINT_DIFFERENTIAL": "1"})
        self.assertIn("transactions=128", output)
        self.assertIn("checkpoint=ok generation=0 suffix-from=120 differential=equal",
                      output)
        with self.recovered() as (host, bridge, records):
            self.assertEqual(host.checkpoint_outcome, ("ok", 0, 120, True))
            self.assertEqual(bridge.article_count(), 128)
        output = self.invoke("tools/checkpoint.py", "status")
        self.assertIn("generations=0 checkpoint=ok generation=0", output)

    def test_no_marker_is_a_distinct_outcome(self):
        post_many(self.path, 2, "base")
        output = self.invoke("tools/run_store.py", "recover")
        self.assertIn("checkpoint=none", output)
        self.invoke("tools/checkpoint.py", "publish")
        # Published but unselected: still none, and the generation exists.
        output = self.invoke("tools/checkpoint.py", "status")
        self.assertIn("generations=0 checkpoint=none", output)

    def test_select_refuses_unpublished_generation(self):
        post_many(self.path, 1, "base")
        self.invoke("tools/checkpoint.py", "select", "--generation", 3,
                    expected=run_store.EXIT_REFUSED)

    # -- corruption is reported, never rolled back --------------------------

    def _corrupt_middle(self, path):
        data = bytearray(path.read_bytes())
        middle = len(data) // 2
        data[middle] ^= 0x5A
        path.write_bytes(bytes(data))

    def test_corrupt_selected_generation_is_reported_not_rolled_back(self):
        post_many(self.path, 3, "base")
        self.invoke("tools/checkpoint.py", "publish", "--select")
        post_many(self.path, 2, "more")
        self.invoke("tools/checkpoint.py", "publish", "--select")
        store = Store(self.path)
        self.assertEqual(checkpoint.generations(store), [0, 1])
        self._corrupt_middle(checkpoint.generation_path(store, 1))
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.path), "recover"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            timeout=600)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, run_store.EXIT_FAULT, output)
        self.assertIn("transactions=5", output)
        self.assertIn("checkpoint=corrupt", output)
        self.assertIn("generation 1", output)
        self.assertNotIn("checkpoint=ok", output)
        # The intact older generation is still there and still not selected.
        self.assertEqual(checkpoint.generations(store), [0, 1])
        with self.recovered(differential=False) as (host, bridge, records):
            self.assertEqual(host.checkpoint_outcome[0], "corrupt")
            self.assertEqual(bridge.article_count(), 5)
            self.assertEqual(checkpoint.selected_generation(host, bridge), 1)

    def test_corrupt_marker_is_reported(self):
        post_many(self.path, 2, "base")
        self.invoke("tools/checkpoint.py", "publish", "--select")
        store = Store(self.path)
        self._corrupt_middle(checkpoint.selection_path(store))
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.path), "recover"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            timeout=600)
        self.assertEqual(result.returncode, run_store.EXIT_FAULT)
        self.assertIn("checkpoint=corrupt", result.stdout.decode("utf-8", "replace"))

    # -- process death at every cut -----------------------------------------

    def _kill_group(self, child):
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=5)

    def _crash_after(self, point):
        control_read, control_write = os.pipe()
        child = subprocess.Popen(
            [sys.executable, "tests/checkpoint_crash_child.py", "--store", str(self.path),
             "--point", point, "--control-fd", str(control_read)],
            cwd=ROOT, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, pass_fds=(control_read,), start_new_session=True)
        os.close(control_read)
        deadline = time.monotonic() + 120
        line = b""
        try:
            while time.monotonic() < deadline:
                ready, _, _ = select.select([child.stdout], [], [], 0.1)
                if not ready:
                    if child.poll() is not None:
                        break
                    continue
                line = child.stdout.readline()
                if line:
                    break
            expected = "POINT {}\n".format(point).encode("ascii")
            if line != expected:
                self._kill_group(child)
                self.fail("child did not reach {}: line={!r} stderr={}".format(
                    point, line, child.stderr.read().decode("utf-8", "replace")))
        finally:
            self._kill_group(child)
            os.close(control_write)
            child.stdout.close()
            child.stderr.close()
        self.assertEqual(child.returncode, -signal.SIGKILL)

    def test_process_death_at_every_cut_recovers_old_authority_or_complete_generation(self):
        # Each case: (cut, generations that may exist, selections that may
        # be recovered).  Generation 0 is the old authority over 3 records;
        # the killed publication is generation 1 over 4 records.
        cases = (
            ("checkpoint:candidate-durable", ([0],), (0,)),
            ("checkpoint:candidate-linked", ([0], [0, 1]), (0,)),
            ("checkpoint:candidate-published", ([0, 1],), (0,)),
            ("checkpoint:selection-durable", ([0, 1],), (0,)),
            ("checkpoint:selection-replaced", ([0, 1],), (0, 1)),
            ("checkpoint:selection-published", ([0, 1],), (1,)),
        )
        for point, allowed_generations, allowed_selected in cases:
            with self.subTest(point=point):
                self.temp.cleanup()
                self.temp = tempfile.TemporaryDirectory(prefix="fn-checkpoint-crash-")
                self.root = Path(self.temp.name)
                self.path = self.root / "store"
                self.invoke("tools/run_store.py", "init")
                post_many(self.path, 3, "base")
                self.invoke("tools/checkpoint.py", "publish", "--select")
                post_many(self.path, 1, "more")
                self._crash_after(point)
                store = Store(self.path)
                self.assertIn(checkpoint.generations(store), allowed_generations)
                with self.recovered() as (host, bridge, records):
                    outcome = host.checkpoint_outcome
                    self.assertEqual(outcome[0], "ok", outcome)
                    self.assertIn(outcome[1], allowed_selected)
                    # Generation 0 covers 3 records, generation 1 covers 4.
                    self.assertEqual(outcome[2], 3 + outcome[1])
                    self.assertTrue(outcome[3])
                    self.assertEqual(bridge.article_count(), 4)
                    self.assertEqual(len(records), 4)
                # Staged names are cleaned or reported, never adopted.
                for name in os.listdir(store.staging):
                    self.assertTrue(name.startswith("."), name)


if __name__ == "__main__":
    unittest.main()
