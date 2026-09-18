"""Real descriptor/lock cleanup failures at the store ownership boundary."""
import errno
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class StoreLifecycleTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
