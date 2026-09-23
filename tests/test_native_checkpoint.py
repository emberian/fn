"""Actual saved-image checkpoint publication, selection, and recovery."""

import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

from tools import run_store


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host-developer is required for raw Store fixtures")
class NativeCheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-checkpoint-")
        self.base = Path(self.temporary.name)
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"native checkpoint payload\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def tearDown(self):
        self.temporary.cleanup()

    def native(self, *args, expected=0, env=None):
        result = subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=30, check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"native {args} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def python_checkpoint(self, store, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/checkpoint.py", "--store", str(store),
             command, *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
            check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"python checkpoint {command} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def python_store(self, store, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             command, *map(str, args)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
            check=False, text=True)
        self.assertEqual(result.returncode, expected,
                         f"python store {command} returned {result.returncode}\n"
                         f"stdout={result.stdout}\nstderr={result.stderr}")
        return result

    def initialized(self, name="store", article=True):
        store = self.base / name
        self.native("store", store, "init", "fn.letters")
        if article:
            self.native("store", store, "post", "<checkpoint@example.invalid>",
                        self.payload, "-", "-", "fn.letters")
        return store

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/checkpoint developer image")
    def test_fenced_clone_rollover_after_selected_pack_reclaim(self):
        source = self.initialized("clone-source")
        self.native("consumer-bootstrap-fixture", source,
                    "history-id", "incarnation-old")
        self.native("checkpoint", "pack", source, "select")
        self.native("checkpoint", "pack-reclaim", source)

        # Reusing the copied incarnation and an occupied destination are
        # refused before any target is published.
        old_id_target = self.base / "same-id"
        self.native("checkpoint", "clone", source, old_id_target,
                    "incarnation-old", expected=run_store.EXIT_REFUSED)
        self.assertFalse(old_id_target.exists())
        occupied = self.base / "occupied"
        occupied.mkdir()
        (occupied / "keep").write_bytes(b"preserve")
        self.native("checkpoint", "clone", source, occupied,
                    "incarnation-new", expected=run_store.EXIT_REFUSED)
        self.assertEqual((occupied / "keep").read_bytes(), b"preserve")

        target = self.base / "clone-target"
        self.native("checkpoint", "clone", source, target,
                    "incarnation-new")
        self.assertFalse((target / "clone-pending.fnce").exists())
        self.assertEqual(
            (source / "packs" / "generation-0.fncp").read_bytes(),
            (target / "packs" / "generation-0.fncp").read_bytes())
        self.assertIn("articles=1",
                      self.native("store", target, "recover").stdout)
        # Prefix reclamation changed physical names, never dense history.
        packed = self.native("checkpoint", "pack", target)
        self.assertIn("records=3", packed.stdout)
        self.native("checkpoint", "clone", source, target,
                    "incarnation-another", expected=run_store.EXIT_REFUSED)

        for point in ("clone-published", "clone-rollover-durable"):
            with self.subTest(point=point):
                destination = self.base / point
                self.stopped_then_killed(
                    ("checkpoint", "clone", source, destination,
                     "new-" + point), point)
                self.assertTrue((destination / "clone-pending.fnce").is_file())
                refused = self.native("store", destination, "recover",
                                      expected=run_store.EXIT_REFUSED)
                self.assertIn("fenced pending durable incarnation", refused.stderr)
                self.native("checkpoint", "clone-resume", destination)
                self.assertFalse((destination / "clone-pending.fnce").exists())
                self.assertIn("articles=1",
                              self.native("store", destination, "recover").stdout)
                packed = self.native("checkpoint", "pack", destination)
                self.assertIn("records=3", packed.stdout)

    def test_native_and_python_frames_cross_open_byte_identically(self):
        source = self.initialized("source")
        native_store = self.base / "native"
        python_store = self.base / "python"
        shutil.copytree(source, native_store)
        shutil.copytree(source, python_store)

        published = self.native("checkpoint", "publish", native_store, "select")
        self.assertIn("published generation=0 records=1 selected=yes", published.stdout)
        py_status = self.python_checkpoint(native_store, "status")
        self.assertIn("checkpoint=ok generation=0 suffix-from=1 differential=equal",
                      py_status.stdout)
        py_recover = self.python_store(native_store, "recover")
        self.assertIn("transactions=1 articles=1", py_recover.stdout)

        self.python_checkpoint(python_store, "publish", "--select")
        native_status = self.native("checkpoint", "status", python_store)
        self.assertIn("generations=0 checkpoint=ok generation=0", native_status.stdout)
        self.assertEqual(
            (native_store / "checkpoints" / "generation-0.fncp").read_bytes(),
            (python_store / "checkpoints" / "generation-0.fncp").read_bytes())
        self.assertEqual(
            (native_store / "checkpoints" / "selected.fncp").read_bytes(),
            (python_store / "checkpoints" / "selected.fncp").read_bytes())

    def test_selected_corruption_is_reported_without_rollback_or_lost_replay(self):
        original = self.initialized("original")
        self.native("checkpoint", "publish", original, "select")
        generation = Path("checkpoints/generation-0.fncp")
        marker = Path("checkpoints/selected.fncp")
        cases = (
            ("marker-truncated", marker, lambda raw: raw[:-1]),
            ("generation-truncated", generation, lambda raw: raw[:-1]),
            ("generation-malformed", generation,
             lambda raw: b"BAD!" + raw[4:]),
        )
        for label, relative, damage in cases:
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                path = store / relative
                path.write_bytes(damage(path.read_bytes()))
                status = self.native("checkpoint", "status", store,
                                     expected=run_store.EXIT_FAULT)
                self.assertIn("checkpoint=corrupt", status.stdout)
                recovered = self.native("store", store, "recover",
                                        expected=run_store.EXIT_FAULT)
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertIn("checkpoint=corrupt", recovered.stdout)

        missing = self.base / "generation-missing"
        shutil.copytree(original, missing)
        (missing / generation).unlink()
        status = self.native("checkpoint", "status", missing,
                             expected=run_store.EXIT_FAULT)
        self.assertIn("selected generation 0 is missing", status.stdout)

    def test_corrupt_unselected_generation_is_invisible(self):
        store = self.initialized("unselected")
        self.native("checkpoint", "publish", store, "select")
        self.native("checkpoint", "publish", store)
        second = store / "checkpoints" / "generation-1.fncp"
        second.write_bytes(b"unselected garbage")
        status = self.native("checkpoint", "status", store)
        self.assertIn("generations=0 1 checkpoint=ok generation=0", status.stdout)

    def test_acl2_namespace_codec_rejects_alias_overflow_and_excess(self):
        original = self.initialized("namespace", article=False)
        self.native("checkpoint", "publish", original)
        generation = original / "checkpoints" / "generation-0.fncp"
        for label, alias in (("leading-zero", "generation-00.fncp"),
                             ("overflow", "generation-4294967296.fncp")):
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                shutil.copy2(generation, store / "checkpoints" / alias)
                result = self.native("checkpoint", "status", store,
                                     expected=run_store.EXIT_FAULT)
                self.assertIn("ACL2 rejected checkpoint namespace", result.stderr)

        excess = self.base / "namespace-excess"
        shutil.copytree(original, excess)
        directory = excess / "checkpoints"
        for index in range(4097):
            (directory / f"unexpected-{index}").touch()
        result = self.native("checkpoint", "status", excess,
                             expected=run_store.EXIT_FAULT)
        self.assertIn("checkpoint namespace exceeds ACL2 observation bound",
                      result.stderr)

    def test_differential_mismatch_is_always_corruption(self):
        store = self.initialized("mismatch")
        self.native("checkpoint", "publish", store, "select")
        env = dict(self.env)
        env["FN_CHECKPOINT_DIFFERENTIAL"] = "0"
        env["FN_CHECKPOINT_TEST_MISMATCH"] = "1"
        status = self.native("checkpoint", "status", store,
                             expected=run_store.EXIT_FAULT, env=env)
        self.assertIn("checkpoint=corrupt", status.stdout)
        self.assertIn("differs from full replay", status.stdout)
        recovered = self.native("store", store, "recover",
                                expected=run_store.EXIT_FAULT, env=env)
        self.assertIn("transactions=1 articles=1", recovered.stdout)
        self.assertIn("checkpoint=corrupt", recovered.stdout)

    def test_known_and_ambiguous_failures_keep_distinct_exit_codes(self):
        refused_store = self.initialized("candidate-refused", article=False)
        refused_env = dict(self.env)
        refused_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "file-barrier"
        refused = self.native("checkpoint", "publish", refused_store,
                              expected=run_store.EXIT_REFUSED, env=refused_env)
        self.assertIn("publication refused", refused.stderr)
        self.assertEqual(list((refused_store / "checkpoints").glob("generation-*")), [])

        uncertain_store = self.initialized("candidate-uncertain", article=False)
        uncertain_env = dict(self.env)
        uncertain_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        uncertain = self.native("checkpoint", "publish", uncertain_store,
                                expected=run_store.EXIT_UNCERTAIN, env=uncertain_env)
        self.assertIn("publication is uncertain", uncertain.stderr)
        self.assertTrue((uncertain_store / "checkpoints" / "generation-0.fncp").is_file())

        marker_store = self.initialized("marker", article=False)
        self.native("checkpoint", "publish", marker_store)
        marker_refused_env = dict(self.env)
        marker_refused_env["FN_CHECKPOINT_TEST_FAIL"] = "selection-file"
        self.native("checkpoint", "select", marker_store, "0",
                    expected=run_store.EXIT_REFUSED, env=marker_refused_env)
        self.assertFalse((marker_store / "checkpoints" / "selected.fncp").exists())

        marker_uncertain_env = dict(self.env)
        marker_uncertain_env["FN_CHECKPOINT_TEST_FAIL"] = "selection-directory"
        self.native("checkpoint", "select", marker_store, "0",
                    expected=run_store.EXIT_UNCERTAIN, env=marker_uncertain_env)
        reopened = self.native("checkpoint", "status", marker_store)
        self.assertIn("checkpoint=ok generation=0", reopened.stdout)

    def transaction_bytes(self, store):
        return {path.name: path.read_bytes()
                for path in sorted((store / "transactions").glob("*.txn"))}

    def stopped_then_killed(self, args, point, occurrence=1):
        env = dict(self.env)
        env["FN_CHECKPOINT_TEST_STOP"] = point
        env["FN_CHECKPOINT_TEST_STOP_AFTER"] = str(occurrence)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                if process.poll() is not None:
                    stdout, stderr = process.communicate()
                    self.fail(f"process exited before {point}: {stdout} {stderr}")
                state = subprocess.run(
                    ["ps", "-o", "state=", "-p", str(process.pid)],
                    stdout=subprocess.PIPE, text=True, check=False).stdout.strip()
                if state.startswith("T"):
                    break
                time.sleep(0.02)
            else:
                self.fail(f"process did not stop at {point}")
            os.kill(process.pid, signal.SIGKILL)
        finally:
            if process.poll() is None:
                process.kill()
            # Reap the process and close both pipes.  wait() alone leaves the
            # Popen-owned file objects open and obscures real warning output.
            process.communicate(timeout=5)

    def test_process_death_at_every_native_checkpoint_cut_reopens(self):
        candidate_expectations = {
            "candidate-file": "generations=- checkpoint=none",
            "candidate-link": "generations=0 checkpoint=none",
            "candidate-directory": "generations=0 checkpoint=none",
        }
        for point, expected in candidate_expectations.items():
            with self.subTest(point=point):
                store = self.initialized(point)
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "publish", store), point)
                status = self.native("checkpoint", "status", store)
                self.assertIn(expected, status.stdout)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertEqual(self.transaction_bytes(store), before)

    def test_process_death_at_every_selection_cut_preserves_event_bytes(self):
        selection_expectations = {
            "selection-file": "checkpoint=none",
            "selection-replace": "checkpoint=ok generation=0",
            "selection-directory": "checkpoint=ok generation=0",
        }
        for point, expected in selection_expectations.items():
            with self.subTest(point=point):
                store = self.initialized(point)
                self.native("checkpoint", "publish", store)
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "select", store, "0"), point)
                status = self.native("checkpoint", "status", store)
                self.assertIn(expected, status.stdout)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                self.assertEqual(self.transaction_bytes(store), before)

    def test_selected_lossless_pack_splices_before_generic_replay(self):
        store = self.initialized("pack")
        packed = self.native("checkpoint", "pack", store, "select")
        self.assertIn("packed generation=0 records=1 selected=yes", packed.stdout)
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=1 articles=1", recovered.stdout)

    def test_selected_pack_missing_or_corrupt_fails_closed(self):
        for mode in ("missing", "corrupt"):
            with self.subTest(mode=mode):
                store = self.initialized("pack-" + mode)
                self.native("checkpoint", "pack", store, "select")
                generation = store / "packs" / "generation-0.fncp"
                if mode == "missing":
                    generation.unlink()
                else:
                    raw = bytearray(generation.read_bytes())
                    raw[len(raw) // 2] ^= 1
                    generation.write_bytes(raw)
                refused = self.native("store", store, "recover",
                                      expected=run_store.EXIT_FAULT)
                self.assertNotIn("articles=", refused.stdout)

    def test_surviving_covered_transaction_conflict_fails_closed(self):
        store = self.initialized("pack-conflict")
        other = self.initialized("pack-conflict-other", article=False)
        self.native("store", other, "post", "<other@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        source = other / "transactions" / "00000000000000000000.txn"
        target = store / "transactions" / "00000000000000000000.txn"
        target.write_bytes(source.read_bytes())
        refused = self.native("store", store, "recover",
                              expected=run_store.EXIT_FAULT)
        self.assertNotIn("articles=", refused.stdout)

    def test_selected_pack_reclaims_physical_prefix_and_replays_suffix(self):
        store = self.initialized("pack-reclaim")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        reclaimed = self.native("checkpoint", "pack-reclaim", store)
        self.assertIn("reclaimed transaction-prefix=1", reclaimed.stdout)
        self.assertEqual([p.name for p in (store / "transactions").iterdir()],
                         ["00000000000000000001.txn"])
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=2 articles=2", recovered.stdout)

    def test_pack_prefix_reclaim_process_death_recovers_from_selected_pack(self):
        for point in ("pack-reclaim-unlink", "pack-reclaim-directory"):
            with self.subTest(point=point):
                store = self.initialized(point)
                self.native("checkpoint", "pack", store, "select")
                before = self.transaction_bytes(store)
                self.stopped_then_killed(("checkpoint", "pack-reclaim", store), point)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=1 articles=1", recovered.stdout)
                # Recovery observes the selected packed bytes; any transaction
                # file that survived the cut remains byte-identical.
                after = self.transaction_bytes(store)
                self.assertEqual(after, {name: before[name] for name in after})

    def test_partial_multi_file_prefix_reclaim_resumes_from_selected_pack(self):
        store = self.initialized("pack-partial")
        self.native("store", store, "post", "<prefix-two@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-three@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        before = self.transaction_bytes(store)
        suffix_name = "00000000000000000002.txn"
        self.stopped_then_killed(("checkpoint", "pack-reclaim", store),
                                 "pack-reclaim-unlink")
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=3 articles=3", recovered.stdout)
        self.native("checkpoint", "pack-reclaim", store)
        self.assertEqual(sorted((store / "transactions").glob("*.txn")),
                         [store / "transactions" / "00000000000000000002.txn"])
        self.assertEqual((store / "transactions" / suffix_name).read_bytes(),
                         before[suffix_name])

    def test_death_after_each_covered_unlink_preserves_exact_suffix_and_resumes(self):
        for occurrence in range(1, 5):
            with self.subTest(occurrence=occurrence):
                store = self.initialized(f"pack-unlink-{occurrence}")
                for number in range(1, 4):
                    self.native("store", store, "post",
                                f"<covered-{number}@example.invalid>",
                                self.payload, "-", "-", "fn.letters")
                self.native("checkpoint", "pack", store, "select")
                self.native("store", store, "post", "<retained@example.invalid>",
                            self.payload, "-", "-", "fn.letters")
                before = self.transaction_bytes(store)
                suffix_name = "00000000000000000004.txn"

                self.stopped_then_killed(
                    ("checkpoint", "pack-reclaim", store),
                    "pack-reclaim-unlink", occurrence=occurrence)
                recovered = self.native("store", store, "recover")
                self.assertIn("transactions=5 articles=5", recovered.stdout)
                self.assertEqual((store / "transactions" / suffix_name).read_bytes(),
                                 before[suffix_name])

                # Retry removes exactly the remaining covered prefix and does
                # not expire or rewrite the retained suffix event.
                self.native("checkpoint", "pack-reclaim", store)
                self.assertEqual(self.transaction_bytes(store),
                                 {suffix_name: before[suffix_name]})

    def test_missing_retained_suffix_gap_fails_closed_without_reclamation(self):
        store = self.initialized("pack-suffix-gap")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-one@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.native("store", store, "post", "<suffix-two@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        transactions = store / "transactions"
        (transactions / "00000000000000000001.txn").unlink()
        before = self.transaction_bytes(store)

        refused = self.native("store", store, "recover",
                              expected=run_store.EXIT_FAULT)
        self.assertNotIn("articles=", refused.stdout)
        self.assertEqual(self.transaction_bytes(store), before)
        reclaim = self.native("checkpoint", "pack-reclaim", store,
                              expected=run_store.EXIT_FAULT)
        self.assertNotEqual(reclaim.returncode, 0)
        self.assertEqual(self.transaction_bytes(store), before)

    def test_arbitrary_covered_deletion_image_recovers_and_resumes(self):
        store = self.initialized("pack-subset")
        for number in range(1, 4):
            self.native("store", store, "post",
                        f"<prefix-{number}@example.invalid>",
                        self.payload, "-", "-", "fn.letters")
        self.native("checkpoint", "pack", store, "select")
        self.native("store", store, "post", "<suffix-4@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        before = self.transaction_bytes(store)

        # A process-death image may contain any subset of already-issued
        # covered unlinks.  Keep covered 1 and 3, remove covered 0 and 2, and
        # retain the complete suffix at 4.
        for sequence in (0, 2):
            (store / "transactions" /
             f"{sequence:020d}.txn").unlink()
        recovered = self.native("store", store, "recover")
        self.assertIn("transactions=5 articles=5", recovered.stdout)
        for name, raw in self.transaction_bytes(store).items():
            self.assertEqual(raw, before[name])
        self.native("checkpoint", "pack-reclaim", store)
        suffix_name = "00000000000000000004.txn"
        self.assertEqual(self.transaction_bytes(store),
                         {suffix_name: before[suffix_name]})

if __name__ == "__main__":
    unittest.main()
