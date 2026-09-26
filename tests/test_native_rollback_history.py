"""`store rollback-check --snapshot`, natively: history, not counters (PRF-141, SCN-076).

gpt-6's answers of 2026-09-26 §7: the verb used to compare each store's
(sequence . file length) list, so a snapshot whose first transaction holds a
different article of the same encoded length passed as "an earlier history"
and the report counted one lost transaction while the restore would also
replace the article.  ACL2 (books/native-operator.lisp
fn-native-operator-history-step / -verdict) now compares the exact committed
records the open reads, packs included, with both stores held under their
shared writer locks.

Cases: the counterexample (refused), a true earlier state (its count), an
identical copy (0), a compacted store (the pack's records are counted), a
snapshot longer than the store (refused), and a store held exclusively by a
writer (refused, never read unlocked).
"""
import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import unittest

from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
DEVELOPER = verbs.DEVELOPER
EXIT_OK, EXIT_REFUSED = 0, 1


class RollbackHistorySourceTests(unittest.TestCase):
    def test_the_host_hands_acl2_records_under_the_lock(self):
        from tests.campaign import native_cuts
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        history = native_cuts.host_function(io, "fnn-rollback-history")
        # The open's reader, the open's pack selection, the open's marker check.
        for call in ("fnn-durable-records", "*fnn-pack-lower-bound-callback*",
                     "*fnn-pack-recover-callback*", "fnn-check-history-marker"):
            self.assertIn(call, history)
        self.assertNotIn("stat-size", history)
        command = native_cuts.host_function(io, "fnn-command-rollback-snapshot")
        self.assertIn("fnn-acquire", command)
        self.assertIn("'fn-native-operator-host-history-step", command)
        self.assertIn("'fn-native-operator-host-history-verdict", command)


@unittest.skipUnless(verbs.executable(DEVELOPER), "the developer image is required")
class RollbackHistoryNativeTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-rollback-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.env = verbs.environment()
        for name in ("FN_NATIVE_POST_FAULT", "FN_NATIVE_RECOVERY_FAULT"):
            self.env.pop(name, None)

    def run_image(self, *words):
        return subprocess.run([str(DEVELOPER), "--fn", *map(str, words)], cwd=ROOT,
                              env=self.env, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=180, check=False)

    def store(self, name):
        path = self.root / name
        done = self.run_image("store", path, "init", "fn.test")
        self.assertEqual(done.returncode, EXIT_OK, done.stderr.decode())
        return path

    def post(self, store, message_id, body=b"exact payload bytes"):
        payload = self.root / (message_id.strip("<>").replace("@", "-") + ".eml")
        payload.write_bytes(
            b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
            b"Subject: rollback history\r\nDate: Sat, 26 Sep 2026 09:00:00 +0000\r\n"
            b"Message-ID: " + message_id.encode("ascii") + b"\r\n\r\n" + body + b"\r\n")
        done = self.run_image("store", store, "post", message_id, payload, "-", "-", "fn.test")
        self.assertEqual(done.returncode, EXIT_OK, done.stderr.decode())

    def config(self, store):
        path = self.root / (store.name + ".toml")
        path.write_text('[store]\npath = "{}"\n'.format(store), encoding="ascii")
        return path

    def check(self, store, snapshot, expected):
        done = self.run_image("operator", self.config(store), "store", "rollback-check",
                              "--snapshot", snapshot)
        text = done.stdout.decode() + done.stderr.decode()
        print("rollback-check {} --snapshot {}: exit={}\n{}".format(
            store.name, snapshot.name, done.returncode, text.strip()))
        self.assertEqual(done.returncode, expected, text)
        return done.stdout.decode()

    def descriptors(self, store):
        files = sorted((store / "transactions").iterdir())
        return [(f.name, f.stat().st_size) for f in files]

    def test_equal_counters_different_content_is_not_an_earlier_state(self):
        snapshot = self.store("snapshot")
        current = self.store("current")
        self.post(snapshot, "<article-a@example.invalid>")
        self.post(current, "<article-b@example.invalid>")
        self.post(current, "<article-c@example.invalid>")
        # The premise of the counterexample: sequence numbers and encoded
        # lengths agree for the snapshot's whole history.
        self.assertEqual(self.descriptors(snapshot), self.descriptors(current)[:1])
        self.assertNotEqual((snapshot / "transactions" / self.descriptors(snapshot)[0][0]).read_bytes(),
                            (current / "transactions" / self.descriptors(current)[0][0]).read_bytes())
        out = self.check(current, snapshot, EXIT_REFUSED)
        self.assertIn("rollback snapshot refused snapshot-not-a-prefix", out)
        self.assertIn("not an earlier state of this store's history", out)

    def test_an_earlier_state_counts_what_the_restore_loses(self):
        current = self.store("current")
        self.post(current, "<one@example.invalid>")
        snapshot = self.root / "snapshot"
        shutil.copytree(current, snapshot, symlinks=True)
        self.post(current, "<two@example.invalid>")
        self.post(current, "<three@example.invalid>")
        out = self.check(current, snapshot, EXIT_OK)
        self.assertIn("rollback snapshot loses transactions=2 snapshot-transactions=1 "
                      "store-transactions=3", out)
        self.assertIn("compared record by record", out)
        same = self.check(current, current, EXIT_OK)
        self.assertIn("loses transactions=0", same)
        # The other way round the snapshot is ahead: not an earlier state.
        self.check(snapshot, current, EXIT_REFUSED)

    def test_a_compacted_history_is_read_through_its_pack(self):
        current = self.store("current")
        for n in range(3):
            self.post(current, "<packed-{}@example.invalid>".format(n))
        snapshot = self.root / "snapshot"
        shutil.copytree(current, snapshot, symlinks=True)
        self.post(current, "<after@example.invalid>")
        compacted = self.run_image("operator", self.config(current), "store", "compact")
        print("compact: exit={} {}".format(compacted.returncode, compacted.stdout.decode().strip()))
        self.assertEqual(compacted.returncode, EXIT_OK, compacted.stderr.decode())
        self.assertLess(len(self.descriptors(current)), 4)
        out = self.check(current, snapshot, EXIT_OK)
        self.assertIn("loses transactions=1 snapshot-transactions=3 store-transactions=4", out)
        # A different history of the same shape, compacted, is still refused.
        other = self.store("other")
        for n in range(3):
            self.post(other, "<packed-{}@example.invalid>".format(n), body=b"exact payload BYTES")
        self.check(current, other, EXIT_REFUSED)

    def test_a_held_store_is_refused_not_read_unlocked(self):
        current = self.store("current")
        self.post(current, "<held@example.invalid>")
        snapshot = self.root / "snapshot"
        shutil.copytree(current, snapshot, symlinks=True)
        lock = os.open(str(current / "writer.lock"), os.O_RDWR)
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            done = self.run_image("operator", self.config(current), "store", "rollback-check",
                                  "--snapshot", snapshot)
            self.assertEqual(done.returncode, EXIT_REFUSED, done.stderr.decode())
            self.assertIn(b"already locked", done.stdout + done.stderr)
        finally:
            os.close(lock)


if __name__ == "__main__":
    unittest.main()
