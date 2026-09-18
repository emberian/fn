"""Real-directory tests for the experimental ACL2-backed transaction store."""
import contextlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from run_store import Acl2Store, Store, StoreFault  # noqa: E402


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-store-test-")
        self.path = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "payload"
        self.invoke("init")

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, command, *args, expected=0):
        result = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(self.path),
                                 command, *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, check=False)
        if result.returncode != expected:
            self.fail("{} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    def post(self, msgid, data, groups=("fn.letters",), *extra, expected=0):
        self.payload.write_bytes(data)
        arguments = ["--message-id", msgid, "--payload", self.payload]
        for group in groups:
            arguments.extend(["--group", group])
        arguments.extend(extra)
        return self.invoke("post", *arguments, expected=expected)

    @contextlib.contextmanager
    def recovered_bridge(self):
        store = Store(self.path, writable=False)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            yield bridge
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_post_reopen_replays_and_preserves_literal_lisp_bytes(self):
        payload = b'Message-ID: <literal@example.invalid>\r\n\r\n#.(error "must not execute") \\ ()\r\n'
        self.post("<literal@example.invalid>", payload)
        status = self.invoke("status")
        self.assertIn(b"transactions=1 articles=1", status.stdout)
        inspected = self.invoke("inspect", "--message-id", "<literal@example.invalid>")
        self.assertEqual(inspected.stdout, payload)

    def test_two_group_post_replays_both_allocations_and_one_pin(self):
        self.post("<two@example.invalid>", b"two", ("fn.letters", "fn.test"))
        with self.recovered_bridge() as bridge:
            self.assertEqual(bridge.article_count(), 1)
            self.assertEqual(bridge.group_next(0), 2)
            self.assertEqual(bridge.group_next(1), 2)

    def test_duplicate_retry_and_conflicting_id_do_not_overwrite(self):
        original = b"first"
        self.post("<same@example.invalid>", original)
        duplicate = self.post("<same@example.invalid>", original)
        self.assertEqual(duplicate.stdout.strip(), b"duplicate")
        conflict = self.post("<same@example.invalid>", b"second", expected=2)
        self.assertIn(b"conflicting immutable Message-ID", conflict.stderr)
        inspected = self.invoke("inspect", "--message-id", "<same@example.invalid>")
        self.assertEqual(inspected.stdout, original)

    def test_corruption_truncation_and_gap_fault_instead_of_prefix_recovery(self):
        self.post("<zero@example.invalid>", b"zero")
        transaction = self.path / "transactions" / "00000000000000000000.txn"
        transaction.write_bytes(transaction.read_bytes()[:-1])
        result = self.invoke("recover", expected=2)
        self.assertIn(b"truncated", result.stderr)

        # A fresh store exercises a namespace gap independently of framing.
        other = Path(self.temp.name) / "gap"
        subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "init"],
                       cwd=ROOT, check=True, stdout=subprocess.PIPE)
        source = other / "transactions" / "00000000000000000000.txn"
        source.write_bytes(b"FNST\x01\x00\x00\x00\x00" + b"x" * 32)
        os.link(source, other / "transactions" / "00000000000000000001.txn")
        source.unlink()
        gap = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "recover"],
                             cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(gap.returncode, 2)
        self.assertIn(b"sequence gap", gap.stderr)

    def test_known_abort_before_publication_and_indeterminate_after_publication(self):
        aborted = self.post("<abort@example.invalid>", b"abort", ("fn.letters",),
                            "--inject-fault", "prepublish", expected=2)
        self.assertIn(b"known abort", aborted.stderr)
        self.invoke("recover")
        self.assertEqual(list((self.path / "transactions").iterdir()), [])

        uncertain = self.post("<uncertain@example.invalid>", b"uncertain", ("fn.letters",),
                              "--inject-fault", "postpublish", expected=2)
        self.assertIn(b"indeterminate", uncertain.stderr)
        # A complete but unacknowledged final file may survive; reopening does
        # exact decode, replay, and directory barriers before becoming usable.
        recovered = self.invoke("recover")
        self.assertIn(b"transactions=1 articles=1", recovered.stdout)

    def test_writer_lock_refuses_concurrent_mutator(self):
        holder = Store(self.path, writable=True)
        holder.acquire()
        try:
            self.payload.write_bytes(b"locked")
            refused = self.invoke("post", "--message-id", "<lock@example.invalid>",
                               "--payload", self.payload, "--group", "fn.letters", expected=2)
            self.assertIn(b"already locked", refused.stderr)
        finally:
            holder.close()


if __name__ == "__main__":
    unittest.main()
