"""S7a/SCN-217: read-only validation of an already captured snapshot.

Fixtures copy a STOPPED store and explicitly supply the producer completion
observation SNAPSHOT.  They do not exercise or warrant a running snapshot
producer, atomic file capture, freshness, or key/config capture ownership.
"""
import shutil
import unittest

from tests import test_native_state_checkpoint as scp
from tests import test_native_store_lineage as lineage
from tests.native_harness import EXIT_OK, Node, native_image
from tools.outcome_codes import EXIT

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
# This file is an explicit completion-observation fixture, not an observed
# output of the unfinished running snapshot producer.  Marker fields are
# provenance; the blessing checks presence and the store's own open.
COMPLETION_OBSERVATION = b"fn snapshot 1\nactive-segment=0 frontier=0 files=0\n"


class SnapshotBlessTests(scp.StateCheckpointFixture):
    image = DEVELOPER
    fork = lineage.StoreLineageTests.fork
    current = lineage.StoreLineageTests.current
    become = lineage.StoreLineageTests.become
    restore = lineage.StoreLineageTests.restore
    diverged_copies = lineage.StoreLineageTests.diverged_copies

    def open_line(self):
        # Exact lineage/open observations require explicit offline replay.
        status = self.op("status", "--replay")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        lines = [line for line in status.stdout.decode().splitlines()
                 if line.startswith("open=")]
        self.assertEqual(len(lines), 1, status.stdout.decode())
        return lines[0]

    def bless(self, target):
        return self.op("store", "bless-snapshot", str(target))

    def test_stopped_copy_blesses_reopens_and_names_missing_and_malformed_inputs(self):
        self.node.init(profile="development")
        ids = ["<snapshot-{}@example.invalid>".format(n) for n in range(3)]
        self.post(ids)
        copied = Node(self, self.image, name="copy")
        shutil.copytree(self.store, copied.store_path, symlinks=True)
        marker = copied.store_path / "SNAPSHOT"
        absent = self.bless(copied.store_path)
        self.assertEqual(absent.returncode, EXIT.REFUSED, absent.stdout + absent.stderr)
        self.assertIn(b"reason=snapshot-incomplete", absent.stdout)
        marker.write_bytes(COMPLETION_OBSERVATION)
        blessed = self.bless(copied.store_path)
        self.assertEqual(blessed.returncode, EXIT_OK, blessed.stdout + blessed.stderr)
        self.assertIn(b"transactions=3:", blessed.stdout)
        # A real subsequent open/served retrieval verifies the copied store
        # can run with its copied keys.  The producer is still a stopped copy.
        copied.start()
        try:
            with copied.session() as session:
                for message_id in ids:
                    reply = session.article(message_id)
                    self.assertIsNotNone(reply, message_id)
                    self.assertIn(message_id.encode(), reply)
        finally:
            copied.stop()
        key = copied.store_path / "keys" / "node-secret.key"
        saved_key = key.read_bytes()
        key.unlink()
        missing_key = self.bless(copied.store_path)
        self.assertEqual(missing_key.returncode, EXIT.REFUSED,
                         missing_key.stdout + missing_key.stderr)
        self.assertIn(b"reason=no-node-secret", missing_key.stdout)
        key.write_bytes(b"not a node secret")
        key.chmod(0o600)
        bad_key = self.bless(copied.store_path)
        self.assertEqual(bad_key.returncode, EXIT.REFUSED, bad_key.stdout + bad_key.stderr)
        self.assertIn(b"node secret", bad_key.stderr)
        key.write_bytes(saved_key)
        config = copied.store_path / "config.json"
        config.write_bytes(b"not a store profile")
        malformed = self.bless(copied.store_path)
        self.assertEqual(malformed.returncode, EXIT.REFUSED,
                         malformed.stdout + malformed.stderr)
        self.assertIn(b"reason=open-refused", malformed.stdout)
        # No marker means no open, even when the copied profile is malformed.
        marker.unlink()
        incomplete = self.bless(copied.store_path)
        self.assertEqual(incomplete.returncode, EXIT.REFUSED,
                         incomplete.stdout + incomplete.stderr)
        self.assertIn(b"reason=snapshot-incomplete", incomplete.stdout)
        self.assertNotIn(b"open-refused", incomplete.stdout)

    def test_foreign_lineage_is_refused_and_complete_old_lineage_is_explicitly_allowed(self):
        theirs, mine = self.diverged_copies()
        marker = self.store / "SNAPSHOT"
        marker.write_bytes(COMPLETION_OBSERVATION)
        own = self.bless(self.store)
        self.assertEqual(own.returncode, EXIT_OK, own.stdout + own.stderr)
        self.assertIn(b"transactions=3:", own.stdout)
        self.path().write_bytes(theirs)
        foreign = self.bless(self.store)
        self.assertEqual(foreign.returncode, EXIT.REFUSED, foreign.stdout + foreign.stderr)
        self.assertIn(b"reason=open-refused: open refused reason=foreign-lineage", foreign.stdout)
        self.path().write_bytes(mine)
        # The same complete older copy is valid; blessing cannot infer freshness.
        restored = self.bless(self.store)
        self.assertEqual(restored.returncode, EXIT_OK, restored.stdout + restored.stderr)


if __name__ == "__main__":
    unittest.main()
