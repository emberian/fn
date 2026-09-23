"""A real pre-T2 Store reopened and extended by a T2 native image.

Set FN_PRE_T2_NATIVE_HOST and FN_T2_NATIVE_HOST to two executable images.
The old image writes schema 0; the new image must preserve those bytes while
writing schema 1 for its next acceptance.  The temporary store is isolated.
"""

import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
OLD = Path(os.environ.get("FN_PRE_T2_NATIVE_HOST", "/nonexistent/fn-pre-t2"))
NEW = Path(os.environ.get("FN_T2_NATIVE_HOST", "/nonexistent/fn-t2"))


@unittest.skipUnless(OLD.is_file() and NEW.is_file(),
                     "FN_PRE_T2_NATIVE_HOST and FN_T2_NATIVE_HOST are required")
class NativeStampMigrationTests(unittest.TestCase):
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
            self.assertIn(b"\x44fn-r\x00", before)

            status = self.command(NEW, store, "status")
            self.assertIn(b"articles=1", status)
            self.assertEqual(self.command(NEW, store, "inspect", "--message-id", old_id),
                             octets)
            self.assertEqual(hashlib.sha256(old_record.read_bytes()).hexdigest(),
                             before_hash)

            payload.write_bytes(octets.replace(b"old", b"new"))
            self.command(NEW, store, "post", "--message-id", new_id,
                         "--payload", payload, "--group", "fn.letters")
            new_record = store / "transactions" / "00000000000000000001.txn"
            self.assertIn(b"\x44fn-r\x01", new_record.read_bytes())
            self.assertEqual(self.command(NEW, store, "inspect", "--message-id", old_id),
                             octets)
            self.assertEqual(hashlib.sha256(old_record.read_bytes()).hexdigest(),
                             before_hash)


if __name__ == "__main__":
    unittest.main()
