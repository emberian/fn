"""An ambiguous feed append fences the real owner's public feed methods."""
import io
from pathlib import Path
import sys
import unittest
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from run_owner import Owner, EXIT_UNCERTAIN, StoreIndeterminate


class FeedFenceTests(unittest.TestCase):
    def owner(self):
        owner = Owner.__new__(Owner)
        owner.feed_uncertain = False
        owner.stopping = False
        owner.exit_code = 0
        owner.bridge = mock.Mock()
        owner.bridge.feed_frames.return_value = [b"frame"]
        owner.bridge.feed_record_peers.return_value = ["inn"]
        journal = mock.Mock()
        owner.feeds = {"inn": SimpleNamespace(journal=journal, session=None,
                                              peer="inn", close=mock.Mock())}
        owner.clock = mock.Mock()
        owner.selector = mock.Mock()
        return owner, journal

    def test_ambiguous_append_stops_all_feed_mutations_and_preserves_exit_three(self):
        owner, journal = self.owner()
        journal.append.side_effect = OSError("ambiguous append barrier")
        with mock.patch("sys.stderr", new_callable=io.StringIO) as log:
            with self.assertRaises(StoreIndeterminate):
                owner.feed_flush()
            self.assertTrue(owner.stopping)
            self.assertTrue(owner.feed_uncertain)
            self.assertEqual(owner.exit_code, EXIT_UNCERTAIN)
            owner.bridge.reset_mock()
            work = mock.Mock()
            owner.guard("control", work)
            work.assert_not_called()
            owner.serve(object(), 0)
            with self.assertRaises(StoreIndeterminate):
                owner.control(object())
            owner.feed_drop(owner.feeds["inn"])
            owner.feed_read("inn")
            owner.feed_poll()
            owner.feed_write(owner.feeds["inn"], b"IHAVE <a@fn>\r\n")
            self.assertFalse(owner.feed_dial(owner.feeds["inn"]))
            with self.assertRaises(StoreIndeterminate):
                owner.feed_flush()
            owner.take_fault("feed-poll", RuntimeError("outer boundary"))
        self.assertNotIn("FAULT", log.getvalue())
        self.assertIn("FEED-UNCERTAIN", log.getvalue())
        owner.bridge.assert_not_called()
        self.assertEqual(owner.bridge.mock_calls, [])
        journal.append.assert_called_once()
        self.assertEqual(owner.exit_code, EXIT_UNCERTAIN)

    def test_missing_journal_or_mismatched_peer_list_never_silently_loses_obligation(self):
        for peers in ([], ["absent"]):
            owner, journal = self.owner()
            owner.bridge.feed_record_peers.return_value = peers
            with mock.patch("sys.stderr", new_callable=io.StringIO):
                with self.assertRaises(StoreIndeterminate):
                    owner.feed_flush()
            journal.append.assert_not_called()
            self.assertTrue(owner.stopping)
            self.assertEqual(owner.exit_code, EXIT_UNCERTAIN)

    def test_second_peer_is_not_advanced_after_lost_connection_append_failure(self):
        owner, journal = self.owner()
        feed = owner.feeds["inn"]
        feed.session = mock.Mock()
        other = SimpleNamespace(peer="other", session=None)
        owner.feeds["other"] = other
        owner.bridge.feed_tick.side_effect = OSError("socket lost")
        journal.append.side_effect = OSError("loss record barrier")
        with mock.patch("sys.stderr", new_callable=io.StringIO):
            owner.feed_poll()
        owner.bridge.feed_has_queued.assert_not_called()
        self.assertTrue(owner.feed_uncertain)


if __name__ == "__main__":
    unittest.main()
