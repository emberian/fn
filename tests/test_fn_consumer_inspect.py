"""Actual SQLite inspection is read-only and never crosses the native boundary."""
import json
from pathlib import Path
import sqlite3
import unittest
from tests import test_fn_consumer_journal as journal


class Inspection(unittest.TestCase):
    setUp = journal.JournalAgainstAStandIn.setUp
    queue = journal.JournalAgainstAStandIn.queue
    run_consumer = journal.JournalAgainstAStandIn.run_consumer
    seen = journal.JournalAgainstAStandIn.seen

    def test_snapshot_preserves_inflight_and_exports_exact_public_artifacts(self):
        self.queue(0)
        self.assertEqual(self.run_consumer("report", "r1", "opaque", cut="after-post").returncode, 97)
        self.assertEqual(self.run_consumer("status").returncode, 0)
        inspected = self.run_consumer("inspect", "r1", "--bytes")
        self.assertEqual(inspected.returncode, 0, inspected.stderr)
        value = json.loads(inspected.stdout)
        self.assertEqual(value["attempts"]["rows"][0]["state"], "in-flight")
        artifact = value["submissions"]["rows"][0]
        with sqlite3.connect(json.loads(self.config.read_text())["db"]) as db:
            self.assertEqual(db.execute("SELECT state FROM attempts").fetchone()[0], "in-flight")
            self.assertEqual(bytes.fromhex(artifact["source"]["hex"]), db.execute("SELECT source FROM submissions").fetchone()[0])
        self.assertEqual(len(self.seen()), 1)
        target = self.root / "public.json"
        self.assertEqual(self.run_consumer("export", str(target)).returncode, 0)
        exported = json.loads(target.read_text())
        self.assertEqual(exported["tables"]["submissions"]["rows"][0], artifact)
        self.assertEqual(self.run_consumer("export", str(target)).returncode, 1)
        self.assertFalse(any(name in target.read_text() for name in ("ed_secret", "ml_private")))

    def test_live_reader_does_not_take_consumer_lock_or_mutate_attempts(self):
        self.assertEqual(self.run_consumer("report", "r1", "opaque").returncode, 0)
        client = journal.fn_consumer.Consumer(self.config)
        self.addCleanup(client.close)
        before = client.db.total_changes
        status = self.run_consumer("status")
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn("no fn calls", json.loads(status.stdout)["snapshot"])
        self.assertEqual(client.db.total_changes, before)
        self.assertEqual(len(self.seen()), 1)

    def test_query_pagination_and_metadata_only_are_explicit(self):
        for oid in ("r1", "r2", "r3"):
            self.assertEqual(self.run_consumer("report", oid, "opaque").returncode, 0)
        page = json.loads(self.run_consumer("query", "submissions", "--limit", "2").stdout)
        self.assertEqual(len(page["rows"]), 2)
        self.assertEqual(page["next_after"], 2)
        self.assertNotIn("hex", page["rows"][0]["source"])
        following = json.loads(self.run_consumer("query", "submissions", "--after", "2", "--limit", "2").stdout)
        self.assertEqual([row["operation_id"] for row in following["rows"]], ["r3"])
        self.assertIsNone(following["next_after"])
        self.assertEqual(self.run_consumer("query", "submissions", "--limit", "0").returncode, 1)
        self.assertEqual(self.run_consumer("inspect", "unknown").returncode, 1)

    def test_missing_database_is_not_created_by_inspection(self):
        config = json.loads(self.config.read_text())
        self.assertEqual(self.run_consumer("status").returncode, 4)
        self.assertFalse(Path(config["db"]).exists())
        self.assertFalse(Path(config["work"]).exists())

if __name__ == "__main__":
    unittest.main()
