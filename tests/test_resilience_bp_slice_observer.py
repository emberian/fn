"""Synthetic collector tests, not native execution evidence."""
import tempfile
import unittest
from pathlib import Path
from tools.resilience.adapters.bp_slice_observer import EVENTS, SliceObserver
from tools.resilience.journal import Journal


class SliceObserverTests(unittest.TestCase):
    def test_lossless_bytes_and_explicit_pending_verdict(self):
        observer = SliceObserver()
        for event in EVENTS:
            observer(event, source="a" * 40, octets=b"\x00\xff\r\n")
        with tempfile.TemporaryDirectory() as tmp:
            journal = Journal.read(observer.finish(Path(tmp) / "journal.jsonl"))
        self.assertEqual(journal.records[0]["octets"],
                         {"octets_hex": "00ff0d0a"})
        self.assertEqual(journal.records[-1]["semantic_verdict"], "pending")
        self.assertEqual(journal.of_kind("client"), [])

    def test_missing_or_reordered_event_refuses(self):
        observer = SliceObserver()
        with self.assertRaises(ValueError):
            observer(EVENTS[1])
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                observer.finish(Path(tmp) / "journal.jsonl")

    def test_no_unqualified_image_coordinate(self):
        with self.assertRaises(ValueError):
            SliceObserver()("fixture", source="historical-image")

    def test_no_observation_after_seal(self):
        observer = SliceObserver()
        for event in EVENTS:
            observer(event, source="a" * 40)
        with tempfile.TemporaryDirectory() as tmp:
            observer.finish(Path(tmp) / "journal.jsonl")
        with self.assertRaises(ValueError):
            observer("fixture", source="a" * 40)
