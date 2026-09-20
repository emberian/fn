"""Real descriptor/lock cleanup failures at the store ownership boundary."""
import errno
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


class StoreLifecycleTests(unittest.TestCase):
    def test_mutation_requires_a_live_exclusive_owner(self):
        for mode in ("reader", "closed-writer"):
            for operation in ("allocate", "publish"):
                with self.subTest(mode=mode, operation=operation):
                    with tempfile.TemporaryDirectory(prefix="fn-owner-") as temporary:
                        path = Path(temporary) / "store"
                        run_store.Store(path, writable=True).initialize()
                        store = run_store.Store(path, writable=(mode != "reader"))
                        store.acquire()
                        if mode == "closed-writer":
                            store.close()
                        frontier = store.frontier_path.read_bytes()
                        try:
                            with self.assertRaises(run_store.StoreError):
                                if operation == "allocate":
                                    store.advance_frontier(None, 0)
                                else:
                                    store.publish(None, 0, b"not-admitted")
                            self.assertEqual(store.frontier_path.read_bytes(), frontier)
                            self.assertEqual(list(store.transactions.iterdir()), [])
                            self.assertEqual(list(store.staging.iterdir()), [])
                        finally:
                            store.close()

    def test_acquire_metadata_io_error_releases_writer_lock(self):
        with tempfile.TemporaryDirectory(prefix="fn-lock-error-") as temporary:
            path = Path(temporary) / "store"
            run_store.Store(path, writable=True).initialize()
            broken = run_store.Store(path, writable=True)
            following = run_store.Store(path, writable=True)
            real_lstat = os.lstat

            def fail_config_stat(target, *args, **kwargs):
                if Path(target) == broken.config_path:
                    raise OSError(errno.EIO, "injected metadata stat failure")
                return real_lstat(target, *args, **kwargs)

            try:
                with mock.patch("run_store.os.lstat", side_effect=fail_config_stat):
                    with self.assertRaises(OSError):
                        broken.acquire()
                self.assertIsNone(broken.lock_fd)
                following.acquire()
                self.assertIsNotNone(following.lock_fd)
            finally:
                broken.close()
                following.close()

    def test_after_effect_close_error_cannot_close_reused_descriptor(self):
        with tempfile.TemporaryDirectory(prefix="fn-close-error-") as temporary:
            path = Path(temporary) / "store"
            run_store.Store(path, writable=True).initialize()
            store = run_store.Store(path, writable=True)
            store.acquire()
            retired = store.lock_fd
            real_close = os.close
            replacement = None

            def close_then_fail(fd):
                nonlocal replacement
                real_close(fd)
                if fd == retired:
                    # POSIX allocates the lowest unused descriptor. Reusing
                    # the just-closed one makes an accidental retry observable.
                    replacement = os.open(Path(temporary) / "unrelated",
                                          os.O_CREAT | os.O_RDWR, 0o600)
                    raise OSError(errno.EIO, "injected after-effect close failure")

            try:
                with mock.patch("run_store.os.close", side_effect=close_then_fail):
                    with self.assertRaises(OSError):
                        store.close()
                self.assertEqual(replacement, retired)
                self.assertIsNone(store.lock_fd)
                store.close()
                os.fstat(replacement)
            finally:
                # A failing pre-fix assertion must not close the unrelated FD
                # through the stale Store field or leak it into later tests.
                store.lock_fd = None
                if replacement is not None:
                    real_close(replacement)


class StagingSweepTests(unittest.TestCase):
    """Finding 5 of planning/evidence/deploy-cce4b11-2026-09-20.md.

    An uncertain publication left one `.stage-' name behind and two
    recoveries reported it and collected none.  Recovery now sweeps, and
    which names it may unlink is decided by books/store-sweep.lisp.
    """

    def store_command(self, store, *argv, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store), *argv],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != expected:
            self.fail("store {} returned {}\nstdout={}\nstderr={}".format(
                argv, result.returncode, result.stdout, result.stderr))
        return result.stdout

    def test_an_uncertain_publication_leaves_no_staging_orphan_after_recovery(self):
        with tempfile.TemporaryDirectory(prefix="fn-sweep-") as temporary:
            store = Path(temporary) / "store"
            payload = Path(temporary) / "payload"
            payload.write_bytes(b"From: a <a@fn.example.invalid>\r\n"
                                b"Subject: first\r\n\r\nHello, news.\r\n")
            self.store_command(store, "init", "--group", "fn.letters")
            self.store_command(store, "post", "--message-id", "<a@fn.example.invalid>",
                               "--payload", str(payload), "--group", "fn.letters")
            # An indeterminate failure after the final publication attempt:
            # the staged name may or may not have been linked, so the host
            # reports uncertainty and leaves the staging file behind.
            self.store_command(store, "post", "--message-id", "<b@fn.example.invalid>",
                               "--payload", str(payload), "--group", "fn.letters",
                               "--inject-fault", "postpublish",
                               expected=run_store.EXIT_UNCERTAIN)
            staged = sorted(p.name for p in (store / "staging").iterdir())
            self.assertTrue([n for n in staged if n.startswith(".stage-")], staged)
            first = self.store_command(store, "recover")
            second = self.store_command(store, "recover")
            # The first recovery collects it; the second has nothing to do.
            self.assertIn(b"staging-orphans=0", second, second)
            self.assertIn(b"staging-orphans=0", first, first)
            self.assertEqual(
                [p.name for p in (store / "staging").iterdir()
                 if p.name.startswith(".stage-")], [])
            # Nothing the durable history names was touched.
            status = self.store_command(store, "status")
            self.assertIn(b"staging-orphans=0", status)


if __name__ == "__main__":
    unittest.main()
