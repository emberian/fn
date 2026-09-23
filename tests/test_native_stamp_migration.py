"""A real pre-T2 Store reopened and extended by a T2 native image.

Set FN_PRE_T2_NATIVE_DEVELOPER_HOST and FN_T2_NATIVE_DEVELOPER_HOST to two
frozen executable developer images.  Store POST is developer-only.
The old image writes schema 0; the new image must preserve those bytes while
writing schema 1 for its next acceptance.  The temporary store is isolated.
"""

import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import frame_bridge  # noqa: E402

OLD = Path(os.environ.get("FN_PRE_T2_NATIVE_DEVELOPER_HOST",
                          "/nonexistent/fn-pre-t2-developer"))
NEW = Path(os.environ.get("FN_T2_NATIVE_DEVELOPER_HOST",
                          "/nonexistent/fn-t2-developer"))
DTN_EPOCH_UNIX_SECONDS = 946684800


@unittest.skipUnless(os.access(OLD, os.X_OK) and os.access(NEW, os.X_OK),
                     "frozen pre-T2 and T2 developer images are required")
class NativeStampMigrationTests(unittest.TestCase):
    def stamp_of_frame(self, raw):
        """Ask the ACL2 byte-store decoder for the exact persisted stamp."""
        bridge = frame_bridge.session()
        # INCLUDE-BOOK prints an event transcript, not one value for the
        # framing decoder.  The underlying bridge still checks ACL2 errors.
        bridge.store.call('(include-book "books/byte-store-scan")')
        literal = "(" + " ".join(str(octet) for octet in raw) + ")"
        form = "(fn-bs-record-of-octets '" + literal + ")"
        self.assertEqual(bridge.call("(fn-record-p " + form + ")"), True)
        return bridge.call("(fn-record-stamp " + form + ")")

    def command(self, image, store, verb, *arguments):
        env = dict(os.environ)
        env["FN_HOST"] = "native"
        env["FN_NATIVE_HOST"] = str(image)
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             verb, *map(str, arguments)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(result.returncode, 0,
                         f"{image.name} {verb}: {result.stderr.decode(errors='replace')}")
        return result.stdout

    def test_old_record_reopens_byte_exact_and_new_acceptance_uses_schema_one(self):
        self.addCleanup(frame_bridge.close)
        with tempfile.TemporaryDirectory(prefix="fn-stamp-migration-") as temporary:
            base = Path(temporary)
            store = base / "store"
            payload = base / "article"
            octets = b"From: a@example.invalid\r\nNewsgroups: fn.letters\r\n\r\nold\r\n"
            payload.write_bytes(octets)
            old_id = "<old-stamp@example.invalid>"
            new_id = "<new-stamp@example.invalid>"
            self.command(OLD, store, "init")
            self.command(OLD, store, "post", "--message-id", old_id,
                         "--payload", payload, "--group", "fn.letters")
            old_record = store / "transactions" / "00000000000000000000.txn"
            before = old_record.read_bytes()
            before_hash = hashlib.sha256(before).hexdigest()
            self.assertEqual(self.stamp_of_frame(before), frame_bridge.Keyword("legacy"))

            status = self.command(NEW, store, "status")
            self.assertIn(b"articles=1", status)
            self.assertEqual(self.command(NEW, store, "inspect", "--message-id", old_id),
                             octets)
            self.assertEqual(hashlib.sha256(old_record.read_bytes()).hexdigest(),
                             before_hash)

            payload.write_bytes(octets.replace(b"old", b"new"))
            before_post = int(time.time()) - DTN_EPOCH_UNIX_SECONDS
            self.command(NEW, store, "post", "--message-id", new_id,
                         "--payload", payload, "--group", "fn.letters")
            after_post = int(time.time()) - DTN_EPOCH_UNIX_SECONDS
            new_record = store / "transactions" / "00000000000000000001.txn"
            stamp = self.stamp_of_frame(new_record.read_bytes())
            self.assertIsInstance(stamp, int)
            self.assertNotIsInstance(stamp, bool)
            self.assertLessEqual(before_post, stamp)
            self.assertLessEqual(stamp, after_post)
            self.assertEqual(self.command(NEW, store, "inspect", "--message-id", new_id),
                             payload.read_bytes())
            self.assertEqual(self.command(NEW, store, "inspect", "--message-id", old_id),
                             octets)
            self.assertEqual(hashlib.sha256(old_record.read_bytes()).hexdigest(),
                             before_hash)


if __name__ == "__main__":
    unittest.main()
