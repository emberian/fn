"""Malformed-image recovery matrix for the real ACL2-backed file adapter."""
import contextlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import Acl2Store, Store, StoreError, StoreFault, StoreIndeterminate, frame  # noqa: E402
from tools import frame_bridge  # noqa: E402


def flip_last_octet(path):
    """Corrupt an FNSM metadata frame's integrity trailer by one bit."""
    raw = bytearray(path.read_bytes())
    raw[-1] ^= 1
    path.write_bytes(bytes(raw))


class StoreCorruptionTests(unittest.TestCase):
    """Intentional bad disk images must be faults, never a usable prefix."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-store-corruption-")
        self.base = Path(self.temp.name)
        self.payload_number = 0

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, path, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(path), command,
             *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False)
        if result.returncode != expected:
            self.fail("{} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    def post(self, path, msgid, payload, fault=None, expected=0):
        payload_path = self.base / "payload-{}".format(self.payload_number)
        self.payload_number += 1
        payload_path.write_bytes(payload)
        arguments = ["--message-id", msgid, "--payload", payload_path,
                     "--group", "fn.letters", "--group", "fn.test"]
        if fault is not None:
            arguments.extend(["--inject-fault", fault])
        return self.invoke(path, "post", *arguments, expected=expected)

    def store_with_prior(self, name, count=2):
        path = self.base / name
        Store(path, writable=True).initialize()
        for number in range(count):
            self.assertEqual(self.post(path, "<prior-{}@example.invalid>".format(number),
                                       "prior-{}".format(number).encode("ascii")).returncode, 0)
        return path

    @contextlib.contextmanager
    def live(self, path):
        store, bridge, records = run_store.open_live_store(path, writable=True)
        try:
            yield store, bridge, records
        finally:
            bridge.close()
            store.close()

    @contextlib.contextmanager
    def reopened(self, path):
        store = Store(path, writable=False)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            records = store.recover(bridge)
            yield bridge, records
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def transaction(self, path, sequence):
        return path / "transactions" / "{:020d}.txn".format(sequence)

    def assert_unusable(self, path, diagnostic):
        """Both reader and writer entry points must refuse this corrupt image."""
        for command, arguments in (
                ("recover", ()),
                ("status", ()),
                ("inspect", ("--message-id", "<prior-0@example.invalid>")),
                ("post", ("--message-id", "<blocked@example.invalid>",
                          "--payload", self.payload_for_refusal(),
                          "--group", "fn.letters"))):
            with self.subTest(command=command):
                result = self.invoke(path, command, *arguments,
                                     expected=run_store.EXIT_FAULT)
                self.assertIn(diagnostic.encode("utf-8"), result.stderr)

    def payload_for_refusal(self):
        path = self.base / "blocked-payload"
        path.write_bytes(b"blocked")
        return path

    def assert_prior_bytes_unchanged(self, path, before):
        self.assertEqual(self.transaction(path, 0).read_bytes(), before)

    def test_frontier_malformed_namespace_matrix(self):
        cases = (
            ("truncated", lambda path: path.write_bytes(path.read_bytes()[:-1]),
             "invalid durable allocation frontier frame"),
            ("legacy-json", lambda path: path.write_bytes(b"{"),
             "legacy JSON allocator is retained in place"),
            ("trailer", flip_last_octet, "invalid durable allocation frontier frame"),
            ("kind", lambda path: path.write_bytes((path.parent / "config.json").read_bytes()),
             "invalid durable allocation frontier frame"),
            ("symlink", lambda path: (path.unlink(), os.symlink(path.parent / "config.json", path)),
             "refusing non-regular path"),
            ("directory", lambda path: (path.unlink(), path.mkdir()),
             "refusing non-regular path"),
            ("oversize", lambda path: path.write_bytes(b"x" * 4097),
             "store file exceeds bound"),
        )
        for label, corrupt, diagnostic in cases:
            with self.subTest(label=label):
                path = self.store_with_prior("frontier-" + label)
                prior = self.transaction(path, 0).read_bytes()
                corrupt(path / "allocation-frontier.json")
                self.assert_prior_bytes_unchanged(path, prior)
                self.assert_unusable(path, diagnostic)
                self.assert_prior_bytes_unchanged(path, prior)

    def test_config_and_history_inconsistency_matrix(self):
        cases = (
            ("config-trailer", "config", flip_last_octet, "invalid durable config frame"),
            ("config-kind", "config", lambda path: path.write_bytes(
                (path.parent / "allocation-frontier.json").read_bytes()),
             "invalid durable config frame"),
            ("frontier-behind-history", "frontier", lambda path: path.write_bytes(
                frame_bridge.session().metadata_frontier_frame(1)),
             "ACL2 replay rejected committed transaction history"),
        )
        for label, kind, corrupt, diagnostic in cases:
            with self.subTest(label=label):
                path = self.store_with_prior("inconsistent-" + label)
                prior = self.transaction(path, 0).read_bytes()
                corrupt(path / ("config.json" if kind == "config" else "allocation-frontier.json"))
                self.assert_prior_bytes_unchanged(path, prior)
                self.assert_unusable(path, diagnostic)

    def test_malformed_frame_matrix(self):
        def bad_length(path):
            raw = path.read_bytes()
            size = int.from_bytes(raw[len(run_store.MAGIC):len(run_store.MAGIC) + 4], "big")
            path.write_bytes(raw[:len(run_store.MAGIC)] + (size + 1).to_bytes(4, "big") +
                             raw[len(run_store.MAGIC) + 4:])

        def bad_digest(path):
            raw = bytearray(path.read_bytes())
            raw[-1] ^= 1
            path.write_bytes(raw)

        cases = (
            ("length", bad_length, "frame refused: truncated"),
            ("digest", bad_digest, "frame refused: integrity"),
            ("schema", lambda path: path.write_bytes(frame(b"unknown-schema")),
             "ACL2 returned a non-natural"),
        )
        for label, corrupt, diagnostic in cases:
            with self.subTest(label=label):
                path = self.store_with_prior("frame-" + label, count=1)
                corrupt(self.transaction(path, 0))
                self.assert_unusable(path, diagnostic)

    def test_filename_record_sequence_mismatch_refuses_prefix(self):
        path = self.store_with_prior("sequence-mismatch", count=1)
        first = self.transaction(path, 0)
        os.link(first, self.transaction(path, 1))
        self.assert_unusable(path, "record sequence does not match immutable filename")
        self.assertEqual(first.read_bytes(), self.transaction(path, 1).read_bytes())

    def test_final_name_collision_never_overwrites_and_faults_image(self):
        path = self.store_with_prior("collision", count=1)
        first = self.transaction(path, 0)
        collision = self.transaction(path, 1)
        original = first.read_bytes()
        with self.live(path) as (store, bridge, _records):
            # This is an intentional namespace corruption after normal open;
            # publication must not replace the already existing final name.
            os.link(first, collision)
            txid = bridge.next_txid()
            self.assertEqual(store.advance_frontier(bridge, txid), txid + 1)
            self.assertEqual(bridge.prepare(b"<collision-tail@example.invalid>", b"tail", [0, 1],
                                            b"archive:collision-tail", b"sha256:collision-tail",
                                            b"unsigned-legacy-v0", 2), "prepared")
            with self.assertRaises(StoreIndeterminate):
                store.publish(bridge, 1, bridge.pending_record())
            self.assertTrue(store.fenced)
            self.assertEqual(collision.read_bytes(), original)
            # A link collision is publication ambiguity.  The old bridge has
            # no durable-status completion to submit; fresh observed recovery
            # below diagnoses the corrupted final namespace.
        self.assertEqual(first.read_bytes(), original)
        self.assertEqual(collision.read_bytes(), original)
        self.assert_unusable(path, "record sequence does not match immutable filename")

    def test_multiple_prior_crossposts_and_uncertain_tail_replay_atomically(self):
        path = self.store_with_prior("uncertain-tail", count=2)
        tail = self.post(path, "<uncertain-tail@example.invalid>", b"tail",
                         fault="postpublish",
                         expected=run_store.EXIT_UNCERTAIN)
        self.assertIn(b"indeterminate", tail.stderr)
        with self.reopened(path) as (bridge, records):
            self.assertEqual(len(records), 3)
            self.assertEqual(bridge.article_count(), 3)
            self.assertEqual(bridge.pin_count(), 3)
            self.assertEqual(bridge.reserved(), 6)
            self.assertEqual(bridge.group_next(0), 4)
            self.assertEqual(bridge.group_next(1), 4)
            for number in range(2):
                self.assertEqual(bridge.lookup("<prior-{}@example.invalid>".format(number).encode("ascii")),
                                 "prior-{}".format(number).encode("ascii"))
            self.assertEqual(bridge.lookup(b"<uncertain-tail@example.invalid>"), b"tail")
            self.assertEqual(bridge.next_txid(), 3)

    def test_metadata_checked_then_frontier_changes_is_a_fenced_fault(self):
        path = self.store_with_prior("metadata-after-effect", count=1)
        store = Store(path, writable=True)
        real_check = run_store.check_regular
        changed = False

        def check_then_corrupt(target):
            nonlocal changed
            result = real_check(target)
            if Path(target) == store.frontier_path and not changed:
                changed = True
                store.frontier_path.write_bytes(b"{")
            return result

        with mock.patch("run_store.check_regular", side_effect=check_then_corrupt):
            with self.assertRaises(StoreFault):
                store.acquire()
        self.assertTrue(changed)
        self.assertIsNone(store.lock_fd)
        self.assert_unusable(path, "invalid durable allocation frontier")


if __name__ == "__main__":
    unittest.main()
