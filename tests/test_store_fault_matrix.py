"""Table-driven real-file fault matrix for the ACL2-backed store adapter.

Each case uses the real ACL2 bridge and a temporary directory.  The injected
host failure is limited to one filesystem boundary; the acceptance, replay, and
allocation semantics are never reimplemented here.
"""
import contextlib
import errno
import io
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import Acl2Store, Store, StoreError, StoreIndeterminate, unframe  # noqa: E402


class StoreFaultMatrixTests(unittest.TestCase):
    """Reachable adapter boundaries, with actual post-failure recovery."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-store-fault-matrix-")
        self.base = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def path_for(self, name):
        return self.base / name

    def post(self, path, msgid, payload, groups=("fn.letters", "fn.test")):
        payload_path = path.parent / ("payload-" + msgid[1:9])
        payload_path.write_bytes(payload)
        return run_store.command_post(SimpleNamespace(
            store=path, message_id=msgid, payload=payload_path,
            group=list(groups), charge=None, inject_fault=None))

    def initialized_with_prior(self, name):
        path = self.path_for(name)
        Store(path, writable=True).initialize()
        self.assertEqual(self.post(path, "<prior@example.invalid>", b"prior"), 0)
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
            yield store, bridge, records
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def prepare_crosspost(self, store, bridge, tag):
        txid = bridge.next_txid()
        self.assertEqual(store.advance_frontier(bridge, txid), txid + 1)
        self.assertEqual(
            bridge.prepare(("<{}@example.invalid>".format(tag)).encode("ascii"),
                           tag.encode("ascii"), [0, 1],
                           ("archive:" + tag).encode("ascii"),
                           ("sha256:" + tag).encode("ascii"),
                           b"unsigned-legacy-v0", 2),
            "prepared")
        return txid, bridge.pending_record()

    def assert_prior(self, bridge):
        self.assertEqual(bridge.article_count(), 1)
        self.assertEqual(bridge.pin_count(), 1)
        self.assertEqual(bridge.reserved(), 2)
        self.assertEqual(bridge.group_next(0), 2)
        self.assertEqual(bridge.group_next(1), 2)
        self.assertTrue(bridge.lookup_found(b"<prior@example.invalid>"))
        self.assertEqual(bridge.lookup(b"<prior@example.invalid>"), b"prior")

    def assert_recovered(self, path, articles, frontier, tail=None, tail_payload=None):
        with self.reopened(path) as (_store, bridge, records):
            self.assertEqual(bridge.article_count(), articles)
            self.assertEqual(bridge.pin_count(), articles)
            self.assertEqual(bridge.next_txid(), frontier)
            self.assertEqual(bridge.group_next(0), articles + 1)
            self.assertEqual(bridge.group_next(1), articles + 1)
            self.assertEqual(bridge.reserved(), articles * 2)
            self.assertEqual(bridge.lookup(b"<prior@example.invalid>"), b"prior")
            if tail is not None:
                self.assertEqual(bridge.lookup(("<{}@example.invalid>".format(tail)).encode("ascii")),
                                 (tail if tail_payload is None else tail_payload).encode("ascii"))
            return [bridge.record_txid(unframe(
                (path / "transactions" / "{:020d}.txn".format(sequence)).read_bytes(),
                bridge_max_record_bytes))
                    for sequence in range(len(records))]

    def test_prepublication_create_write_and_file_fsync_matrix(self):
        """Before/after staging effects remain known aborts; frontier is consumed."""
        cases = (
            ("create-before", "before", "open"),
            ("create-after", "after", "open"),
            ("write-before", "before", "write"),
            ("write-after", "after", "write"),
            ("fsync-before", "before", "fsync"),
            ("fsync-after", "after", "fsync"),
        )
        for label, timing, boundary in cases:
            with self.subTest(label=label):
                path = self.initialized_with_prior(label)
                with self.live(path) as (store, bridge, records):
                    self.assertEqual(len(records), 1)
                    reserved, record = self.prepare_crosspost(store, bridge, label)
                    self.assertEqual(reserved, 1)
                    real_open, real_write, real_fsync = os.open, run_store.write_all, run_store.fsync_file

                    def fail_open(target, flags, mode=0o777):
                        if Path(target).parent == store.staging:
                            if timing == "after":
                                fd = real_open(target, flags, mode)
                                os.close(fd)
                            raise OSError(errno.EIO, "matrix staging create")
                        return real_open(target, flags, mode)

                    def fail_write(fd, data):
                        if timing == "after":
                            real_write(fd, data)
                        raise OSError(errno.EIO, "matrix staging write")

                    def fail_fsync(fd):
                        if timing == "after":
                            real_fsync(fd)
                        raise OSError(errno.EIO, "matrix staging fsync")

                    patched = {
                        "open": mock.patch("run_store.os.open", side_effect=fail_open),
                        "write": mock.patch("run_store.write_all", side_effect=fail_write),
                        "fsync": mock.patch("run_store.fsync_file", side_effect=fail_fsync),
                    }[boundary]
                    with patched:
                        with self.assertRaises(StoreError):
                            store.publish(bridge, 1, record)
                    # No final-name attempt occurred.  The pending ACL2 step may
                    # take its known-abort path, but the allocator reservation is
                    # deliberately retained.
                    self.assertFalse(store.fenced)
                    self.assertEqual(bridge.known_abort(), "aborted")
                    self.assertEqual(bridge.next_txid(), 2)
                    self.assert_prior(bridge)
                self.assertEqual(self.assert_recovered(path, 1, 2), [0])
                # A later real crosspost receives txid 2, proving that neither
                # an aborted staging attempt nor its orphan reused txid 1.
                self.assertEqual(self.post(path, "<{}-later@example.invalid>".format(label),
                                           b"later"), 0)
                self.assertEqual(self.assert_recovered(path, 2, 3), [0, 2])

    def test_link_and_transaction_directory_barrier_matrix(self):
        """Publication uncertainty fences; after-effect final names replay atomically."""
        cases = (
            ("link-before", "link", "before", False),
            ("link-after", "link", "after", True),
            ("directory-before", "directory", "before", True),
            ("directory-after", "directory", "after", True),
        )
        for label, boundary, timing, visible in cases:
            with self.subTest(label=label):
                path = self.initialized_with_prior(label)
                with self.live(path) as (store, bridge, records):
                    _reserved, record = self.prepare_crosspost(store, bridge, label)
                    real_link, real_dir = os.link, run_store.fsync_dir

                    def fail_link(source, target):
                        if timing == "after":
                            real_link(source, target)
                        raise OSError(errno.EIO, "matrix link")

                    def fail_directory(target):
                        result = None
                        if timing == "after":
                            result = real_dir(target)
                        if Path(target) == store.transactions:
                            raise OSError(errno.EIO, "matrix transaction directory barrier")
                        return result if timing == "after" else real_dir(target)

                    patched = (mock.patch("run_store.os.link", side_effect=fail_link)
                               if boundary == "link" else
                               mock.patch("run_store.fsync_dir", side_effect=fail_directory))
                    with patched:
                        with self.assertRaises(StoreIndeterminate):
                            store.publish(bridge, 1, record)
                    self.assertTrue(store.fenced)
                    with self.assertRaises(StoreIndeterminate):
                        store.advance_frontier(bridge, store.frontier)
                    # Link and transaction-directory ambiguity are file-kernel
                    # uncertainty.  Do not inject a legacy completion status or
                    # reuse this bridge: the next authority is a fresh observed
                    # Store/Acl2Store recovery below.
                # Recovery is the sole authority after any attempted final-name
                # publication.  It sees either the prior prefix or the entire
                # two-group record; never one group, one pin, or partial bytes.
                txids = self.assert_recovered(path, 2 if visible else 1, 2,
                                               label if visible else None)
                self.assertEqual(txids, [0, 1] if visible else [0])

    def test_allocator_replace_and_directory_barrier_matrix(self):
        """A possibly visible allocator advance fences and is reread on recovery."""
        cases = (
            ("replace-before", "replace", "before", 1),
            ("replace-after", "replace", "after", 2),
            ("allocator-directory-before", "directory", "before", 2),
            ("allocator-directory-after", "directory", "after", 2),
        )
        for label, boundary, timing, recovered_frontier in cases:
            with self.subTest(label=label):
                path = self.initialized_with_prior(label)
                with self.live(path) as (store, bridge, _records):
                    real_replace, real_dir = os.replace, run_store.fsync_dir

                    def fail_replace(source, target):
                        if timing == "after":
                            real_replace(source, target)
                        raise OSError(errno.EIO, "matrix allocator replace")

                    def fail_directory(target):
                        result = None
                        if timing == "after":
                            result = real_dir(target)
                        if Path(target) == store.root:
                            raise OSError(errno.EIO, "matrix allocator directory barrier")
                        return result if timing == "after" else real_dir(target)

                    patched = (mock.patch("run_store.os.replace", side_effect=fail_replace)
                               if boundary == "replace" else
                               mock.patch("run_store.fsync_dir", side_effect=fail_directory))
                    with patched:
                        with self.assertRaises(StoreIndeterminate):
                            store.advance_frontier(bridge, bridge.next_txid())
                    self.assertTrue(store.fenced)
                    with self.assertRaises(StoreIndeterminate):
                        store.publish(bridge, 1, b"unreachable")
                    store.recover(bridge)
                    self.assertFalse(store.fenced)
                    self.assertEqual(store.frontier, recovered_frontier)
                    self.assertEqual(bridge.next_txid(), recovered_frontier)
                    self.assert_prior(bridge)
                self.assertEqual(self.assert_recovered(path, 1, recovered_frontier), [0])

    def test_allocator_staging_and_write_progress_matrix(self):
        """Pre-replacement allocator errors are known failures, including writes."""
        cases = (
            ("create", "before"),
            ("create", "after"),
            ("write-eio", "partial-error"),
            ("write-enospc", "partial-nospace"),
            ("write-zero", "zero"),
            ("file-fsync", "before"),
            ("file-fsync", "after"),
            ("file-close", "after"),
        )
        for boundary, timing in cases:
            with self.subTest(boundary=boundary, timing=timing):
                path = self.initialized_with_prior("allocator-{}-{}".format(boundary, timing))
                with self.live(path) as (store, bridge, _records):
                    real_open, real_write = os.open, os.write
                    real_fsync, real_close = run_store.fsync_file, os.close

                    def fail_open(target, flags, mode=0o777):
                        if Path(target).parent == store.staging:
                            if timing == "after":
                                fd = real_open(target, flags, mode)
                                real_close(fd)
                            raise OSError(errno.EIO, "matrix allocator staging create")
                        return real_open(target, flags, mode)

                    write_calls = 0

                    def fail_write(fd, data):
                        nonlocal write_calls
                        write_calls += 1
                        if timing == "zero":
                            return 0
                        if write_calls == 1:
                            return real_write(fd, data[:max(1, len(data) // 2)])
                        error = errno.ENOSPC if timing == "partial-nospace" else errno.EIO
                        raise OSError(error, "matrix allocator partial write")

                    def fail_fsync(fd):
                        if timing == "after":
                            real_fsync(fd)
                        raise OSError(errno.EIO, "matrix allocator staging fsync")

                    def fail_close(fd):
                        if boundary == "file-close":
                            real_close(fd)
                            raise OSError(errno.EIO, "matrix allocator staging close")
                        return real_close(fd)

                    patched = {
                        "create": mock.patch("run_store.os.open", side_effect=fail_open),
                        "write-eio": mock.patch("run_store.os.write", side_effect=fail_write),
                        "write-enospc": mock.patch("run_store.os.write", side_effect=fail_write),
                        "write-zero": mock.patch("run_store.os.write", side_effect=fail_write),
                        "file-fsync": mock.patch("run_store.fsync_file", side_effect=fail_fsync),
                        "file-close": mock.patch("run_store.os.close", side_effect=fail_close),
                    }[boundary]
                    with patched:
                        with self.assertRaises(StoreError):
                            store.advance_frontier(bridge, bridge.next_txid())
                    self.assertFalse(store.fenced)
                    self.assertEqual(store.frontier, 1)
                    self.assertEqual(bridge.next_txid(), 1)
                    self.assert_prior(bridge)
                    # Retrying the real allocator consumes txid 1 exactly once.
                    self.assertEqual(store.advance_frontier(bridge, 1), 2)
                    self.assertEqual(bridge.refuse_reservation(), "refused")
                    self.assertEqual(bridge.next_txid(), 2)
                self.assertEqual(self.assert_recovered(path, 1, 2), [0])

    def test_publication_write_progress_and_cleanup_matrix(self):
        """Staging write failures abort; post-barrier cleanup failures do not revoke."""
        cases = (
            ("write-eio", "partial-error", "error"),
            ("write-enospc", "partial-nospace", "error"),
            ("write-zero", "zero", "error"),
            ("file-close", "after", "error"),
            ("cleanup-unlink", "after", "durable"),
            ("cleanup-directory", "after", "durable"),
        )
        for boundary, timing, expected in cases:
            with self.subTest(boundary=boundary, timing=timing):
                path = self.initialized_with_prior("publication-{}-{}".format(boundary, timing))
                with self.live(path) as (store, bridge, _records):
                    _reserved, record = self.prepare_crosspost(store, bridge, boundary)
                    real_write, real_unlink = os.write, os.unlink
                    real_dir, real_close = run_store.fsync_dir, os.close
                    write_calls = 0

                    def fail_write(fd, data):
                        nonlocal write_calls
                        write_calls += 1
                        if timing == "zero":
                            return 0
                        if write_calls == 1:
                            return real_write(fd, data[:max(1, len(data) // 2)])
                        error = errno.ENOSPC if timing == "partial-nospace" else errno.EIO
                        raise OSError(error, "matrix publication partial write")

                    def fail_unlink(target):
                        if Path(target).parent == store.staging:
                            raise OSError(errno.EIO, "matrix cleanup unlink")
                        return real_unlink(target)

                    def fail_directory(target):
                        result = real_dir(target)
                        if Path(target) == store.staging:
                            raise OSError(errno.EIO, "matrix cleanup staging barrier")
                        return result

                    def fail_close(fd):
                        if boundary == "file-close":
                            real_close(fd)
                            raise OSError(errno.EIO, "matrix publication staging close")
                        return real_close(fd)

                    patched = {
                        "write-eio": mock.patch("run_store.os.write", side_effect=fail_write),
                        "write-enospc": mock.patch("run_store.os.write", side_effect=fail_write),
                        "write-zero": mock.patch("run_store.os.write", side_effect=fail_write),
                        "file-close": mock.patch("run_store.os.close", side_effect=fail_close),
                        "cleanup-unlink": mock.patch("run_store.os.unlink", side_effect=fail_unlink),
                        "cleanup-directory": mock.patch("run_store.fsync_dir", side_effect=fail_directory),
                    }[boundary]
                    with patched:
                        if expected == "error":
                            with self.assertRaises(StoreError):
                                store.publish(bridge, 1, record)
                            self.assertFalse(store.fenced)
                            self.assertEqual(bridge.known_abort(), "aborted")
                            self.assert_prior(bridge)
                        else:
                            self.assertEqual(store.publish(bridge, 1, record), "durable")
                            # The file kernel is completing: cleanup is
                            # best-effort, but the host remains fenced until
                            # the exact bridge finish consumes the candidate.
                            self.assertTrue(store.fenced)
                            self.assertEqual(store.finish(bridge), "durable")
                            self.assertEqual(bridge.article_count(), 2)
                            self.assertEqual(bridge.pin_count(), 2)
                if expected == "error":
                    self.assertEqual(self.assert_recovered(path, 1, 2), [0])
                else:
                    self.assertEqual(self.assert_recovered(path, 2, 2, boundary), [0, 1])

    def test_store_lock_close_after_success_matrix(self):
        """A teardown I/O fault keeps its own outcome, distinct from the work's.

        The transaction is durably committed and reported as committed.  The
        failing lock close is an I/O fault at teardown: it is classified as a
        fault, never as a refusal of the post and never as an uncertain
        acceptance, and the committed transaction survives unchanged.
        """
        for operation in ("writer", "reader"):
            with self.subTest(operation=operation):
                path = self.initialized_with_prior(operation + "-close")
                payload_path = path.parent / (operation + "-close-payload")
                payload_path.write_bytes(b"close")
                store, bridge, records = run_store.open_live_store(
                    path, writable=(operation == "writer"))
                lock_fd = store.lock_fd
                real_close = os.close

                def fail_lock_close(fd):
                    if fd == lock_fd:
                        real_close(fd)
                        raise OSError(errno.EIO, "matrix {} lock close".format(operation))
                    return real_close(fd)

                if operation == "writer":
                    args = SimpleNamespace(
                        store=path, message_id="<writer-close@example.invalid>",
                        payload=payload_path, group=["fn.letters", "fn.test"],
                        charge=None, inject_fault=None)
                    command, expected = run_store.command_post, "committed sequence=1"
                else:
                    args = SimpleNamespace(store=path)
                    command, expected = run_store.command_status, "transactions=1 articles=1"
                output = io.StringIO()
                with mock.patch("run_store.open_live_store", return_value=(store, bridge, records)), \
                     mock.patch("run_store.os.close", side_effect=fail_lock_close), \
                     contextlib.redirect_stdout(output):
                    with self.assertRaises(OSError) as raised:
                        command(args)
                self.assertIn(expected, output.getvalue())
                # The work reached its own outcome first, and the teardown
                # failure is reported as a fault distinct from refusal (1) and
                # from uncertain acceptance (3).
                self.assertEqual(run_store.exit_code_for(raised.exception),
                                 run_store.EXIT_FAULT)
                self.assertNotIsInstance(raised.exception, run_store.StoreError)
                # The descriptor was actually closed before the injected
                # exception; a fresh process can reopen the durable state.
                if operation == "writer":
                    self.assertEqual(self.assert_recovered(path, 2, 2, "writer-close", "close"),
                                     [0, 1])
                else:
                    self.assertEqual(self.assert_recovered(path, 1, 1), [0])

    def test_recovery_read_and_all_five_barrier_matrix(self):
        """Read and every recovery rebarrier failure close an already-live gate."""
        cases = (("read", "transaction", timing) for timing in ("before", "after"))
        cases = tuple(cases) + tuple(
            ("file-fsync", target, timing)
            for target in ("config", "frontier") for timing in ("before", "after")) + tuple(
            ("directory", target, timing)
            for target in ("transactions", "root", "parent") for timing in ("before", "after"))
        for boundary, target_name, timing in cases:
            with self.subTest(boundary=boundary, target=target_name, timing=timing):
                path = self.initialized_with_prior(
                    "recovery-{}-{}-{}".format(boundary, target_name, timing))
                with self.live(path) as (store, bridge, _records):
                    real_read = run_store.read_regular_bounded
                    real_regular = run_store.fsync_regular
                    real_dir = run_store.fsync_dir

                    def fail_read(target, maximum):
                        if Path(target).suffix == ".txn":
                            if timing == "after":
                                real_read(target, maximum)
                            raise OSError(errno.EIO, "matrix recovery read")
                        return real_read(target, maximum)

                    def fail_regular(target):
                        expected = {"config": store.config_path,
                                    "frontier": store.frontier_path}.get(target_name)
                        if expected is not None and Path(target) == expected:
                            if timing == "after":
                                real_regular(target)
                            raise OSError(errno.EIO, "matrix recovered file barrier")
                        return real_regular(target)

                    def fail_directory(target):
                        expected = {"transactions": store.transactions,
                                    "root": store.root,
                                    "parent": store.root.parent}[target_name]
                        if Path(target) == expected:
                            if timing == "after":
                                real_dir(target)
                            raise OSError(errno.EIO, "matrix recovered directory barrier")
                        return real_dir(target)

                    patched = (mock.patch("run_store.read_regular_bounded", side_effect=fail_read)
                               if boundary == "read" else
                               mock.patch("run_store.fsync_regular", side_effect=fail_regular)
                               if boundary == "file-fsync" else
                               mock.patch("run_store.fsync_dir", side_effect=fail_directory))
                    with patched:
                        if boundary == "read":
                            with self.assertRaises(OSError):
                                store.recover(bridge)
                        else:
                            with self.assertRaises(StoreIndeterminate):
                                store.recover(bridge)
                    self.assertTrue(store.fenced)
                    # command_post closes its owner in finally; a stale object
                    # is rejected before its old fence state is consulted.
                    with self.assertRaises(StoreError):
                        store.advance_frontier(bridge, store.frontier)
                    store.recover(bridge)
                    self.assertFalse(store.fenced)
                    self.assert_prior(bridge)
                self.assertEqual(self.assert_recovered(path, 1, 1), [0])

    def test_recovery_helper_close_matrix(self):
        """Actual post-effect closes propagate through each recovery helper class."""
        for boundary in ("read", "regular", "directory"):
            with self.subTest(boundary=boundary):
                path = self.initialized_with_prior("recovery-close-" + boundary)
                with self.live(path) as (store, bridge, _records):
                    real_open, real_close = os.open, os.close
                    target_fds = set()

                    def capture_open(target, *args, **kwargs):
                        fd = real_open(target, *args, **kwargs)
                        selected = ((boundary == "read" and Path(target).suffix == ".txn") or
                                    (boundary == "regular" and Path(target) == store.config_path) or
                                    (boundary == "directory" and Path(target) == store.transactions))
                        if selected:
                            target_fds.add(fd)
                        return fd

                    def fail_close(fd):
                        if fd in target_fds:
                            real_close(fd)
                            raise OSError(errno.EIO, "matrix recovery helper close")
                        return real_close(fd)

                    with mock.patch("run_store.os.open", side_effect=capture_open), \
                         mock.patch("run_store.os.close", side_effect=fail_close):
                        if boundary == "read":
                            with self.assertRaises(OSError):
                                store.recover(bridge)
                        else:
                            with self.assertRaises(StoreIndeterminate):
                                store.recover(bridge)
                    self.assertTrue(store.fenced)
                    with self.assertRaises(StoreIndeterminate):
                        store.advance_frontier(bridge, store.frontier)
                    store.recover(bridge)
                    self.assertFalse(store.fenced)
                    self.assert_prior(bridge)
                self.assertEqual(self.assert_recovered(path, 1, 1), [0])

    def test_completion_return_and_lost_reply_matrix(self):
        """Published crossposts remain recovery authority after completion uncertainty."""
        for outcome in ("rejected", "lost"):
            with self.subTest(outcome=outcome):
                path = self.initialized_with_prior("completion-" + outcome)
                payload_path = path.parent / "completion-payload"
                payload_path.write_bytes(outcome.encode("ascii"))
                store, bridge, records = run_store.open_live_store(path, writable=True)
                real_finish = bridge.finish

                def finish():
                    if outcome == "lost":
                        self.assertEqual(real_finish(), "durable")
                        raise StoreError("matrix lost completion reply")
                    return "fault"

                args = SimpleNamespace(store=path,
                                       message_id="<completion-{}@example.invalid>".format(outcome),
                                       payload=payload_path, group=["fn.letters", "fn.test"],
                                       charge=None, inject_fault=None)
                try:
                    with mock.patch("run_store.open_live_store", return_value=(store, bridge, records)), \
                         mock.patch.object(bridge, "finish", side_effect=finish):
                        with self.assertRaises(StoreIndeterminate):
                            run_store.command_post(args)
                    self.assertTrue(store.fenced)
                    # command_post closes its owner in finally; a stale object
                    # is rejected before its old fence state is consulted.
                    with self.assertRaises(StoreError):
                        store.advance_frontier(bridge, store.frontier)
                finally:
                    # command_post closed both resources; close is idempotent for
                    # the store and ACL2 bridge has no further logical role here.
                    store.close()
                    bridge.close()
                self.assertEqual(self.assert_recovered(path, 2, 2,
                                                        "completion-" + outcome, outcome), [0, 1])


# Keep this value explicit so record decoding in assertions remains tied to the
# checked experimental profile instead of duplicating acceptance semantics.
bridge_max_record_bytes = run_store.DEFAULT_CONFIG["max_record_bytes"]


if __name__ == "__main__":
    unittest.main()
