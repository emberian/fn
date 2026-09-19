"""Process-death checks at real immutable-store publication boundaries.

These tests kill a helper process after an actual syscall or ACL2 completion
returns.  They cover process death with the OS cache retained; they do not
claim anything about power loss, torn sectors, or a filesystem losing cached
metadata.
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
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import Acl2Store, Store, unframe  # noqa: E402


class StoreProcessCrashTests(unittest.TestCase):
    BASELINE_ID = b"<baseline@example.invalid>"
    BASELINE_PAYLOAD = b"committed before the child process dies"

    def _run(self, store, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store), command,
             *map(str, args)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            timeout=30,
        )
        if result.returncode != expected:
            self.fail("{} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode,
                result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    def _post(self, store, payload_path, message_id, payload, expected=0):
        payload_path.write_bytes(payload)
        return self._run(
            store, "post", "--message-id", message_id,
            "--payload", payload_path, "--group", "fn.letters",
            expected=expected,
        )

    def _kill_group(self, child):
        """Kill helper and inherited ACL2 children, then reap the helper."""
        # The helper may have exited while its ACL2 subprocess still owns the
        # group.  Always clean our dedicated group, not only a live leader.
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            # A process outside the expected group would be a helper cleanup
            # defect; still ensure this test does not leak a live subprocess.
            child.kill()
            child.wait(timeout=5)

    def _crash_after(self, store, payload_path, message_id, payload, point):
        payload_path.write_bytes(payload)
        control_read, control_write = os.pipe()
        command = [
            sys.executable, "tests/store_crash_child.py",
            "--store", str(store), "--message-id", message_id,
            "--payload", str(payload_path), "--point", point,
            "--control-fd", str(control_read),
        ]
        child = subprocess.Popen(
            command, cwd=ROOT, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            pass_fds=(control_read,), start_new_session=True,
        )
        os.close(control_read)
        deadline = time.monotonic() + 30
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
            expected_line = ("POINT {}\n".format(point)).encode("ascii")
            if line != expected_line:
                self._kill_group(child)
                stderr = child.stderr.read().decode("utf-8", "replace")
                self.fail("child did not reach {}: line={!r} stderr={}".format(
                    point, line, stderr))
        finally:
            # The child blocks on the control pipe, so killing after the point
            # line is observed is ordered after the wrapped real operation.
            self._kill_group(child)
            os.close(control_write)
            child.stdout.close()
            child.stderr.close()
        self.assertIsNotNone(child.returncode)
        self.assertEqual(child.returncode, -signal.SIGKILL)

    @contextlib.contextmanager
    def _recovered(self, store):
        host = Store(store, writable=True)
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

    def _record_txids(self, store, bridge):
        txids = []
        for unused_sequence, path in store.transaction_files():
            constants = run_store.frame_bridge.session().constants
            txids.append(bridge.record_txid(unframe(
                run_store.read_regular_bounded(
                    path, constants["overhead"] + constants["max_store"]))))
        return txids

    def test_process_death_at_publication_boundaries_releases_lock_and_reopens(self):
        cases = (
            ("frontier-replace", False),
            ("frontier-dir-barrier", False),
            ("staged-data-barrier", False),
            ("final-link", True),
            ("directory-barrier", True),
            ("core-durable", True),
        )
        for point, expected_new_record in cases:
            with self.subTest(point=point), tempfile.TemporaryDirectory(
                    prefix="fn-store-process-crash-") as temporary:
                root = Path(temporary)
                store = root / "store"
                payload_path = root / "payload"
                self._run(store, "init")
                self._post(store, payload_path, self.BASELINE_ID.decode("ascii"),
                           self.BASELINE_PAYLOAD)

                crashed_id = "<crashed-{}@example.invalid>".format(point)
                crashed_payload = ("payload at {} boundary".format(point)).encode("ascii")
                self._crash_after(store, payload_path, crashed_id, crashed_payload, point)

                # Reopen through the real ACL2 replay path.  Acquiring the
                # writer lock here also proves process death released it.
                with self._recovered(store) as (host, bridge, records):
                    self.assertEqual(bridge.lookup(self.BASELINE_ID), self.BASELINE_PAYLOAD)
                    self.assertTrue(bridge.lookup_found(self.BASELINE_ID))
                    self.assertEqual(bridge.pin_count(), 1 + int(expected_new_record))
                    self.assertEqual(bridge.article_count(), 1 + int(expected_new_record))
                    # Baseline reserves txid 0; the killed post reserves txid
                    # 1 before every listed publication boundary.
                    self.assertEqual(bridge.next_txid(), 2)
                    self.assertEqual(self._record_txids(host, bridge),
                                     [0, 1] if expected_new_record else [0])
                    self.assertFalse(host.fenced)
                    if expected_new_record:
                        self.assertEqual(bridge.lookup(crashed_id.encode("ascii")),
                                         crashed_payload)
                    else:
                        self.assertFalse(bridge.lookup_found(crashed_id.encode("ascii")))

                # A post after recovery must consume the next durable identity;
                # the process death cannot make the crashed reservation reusable.
                if expected_new_record:
                    # Lost success must be safely retryable with the same
                    # identity, without another durable allocation or pin.
                    retried = self._post(store, payload_path, crashed_id,
                                         crashed_payload)
                    self.assertEqual(retried.stdout, b"duplicate\n")
                    with self._recovered(store) as (host, bridge, records):
                        self.assertEqual(self._record_txids(host, bridge), [0, 1])
                        self.assertEqual(bridge.next_txid(), 2)
                        self.assertEqual(bridge.article_count(), 2)
                        self.assertEqual(bridge.pin_count(), 2)
                else:
                    follow_id = "<after-{}@example.invalid>".format(point)
                    follow_payload = b"post after recovery"
                    self._post(store, payload_path, follow_id, follow_payload)
                    with self._recovered(store) as (host, bridge, records):
                        self.assertEqual(bridge.lookup(follow_id.encode("ascii")),
                                         follow_payload)
                        self.assertEqual(self._record_txids(host, bridge), [0, 2])
                        self.assertEqual(bridge.next_txid(), 3)
                        self.assertEqual(bridge.article_count(), 2)
                        self.assertEqual(bridge.pin_count(), 2)


if __name__ == "__main__":
    unittest.main()
