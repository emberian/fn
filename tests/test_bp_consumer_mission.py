"""A signed BP application campaign cannot pass as unsigned/manual transport."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent / "bp-dtn7"
sys.path.insert(0, str(HERE))
from consumer_exchange import ConsumerExchangeFailure, MissionConsumerExchange
from run_mission_four_node import mission_complete


class MissionVerdictTests(unittest.TestCase):
    def setUp(self):
        self.steps = [{"held": True} for _ in range(7)]

    def test_old_all_green_unsigned_fallback_is_not_signed_success(self):
        historical = {"report_signed": False, "reply_signed": False}
        # The former final predicate could pass with both fallbacks: every
        # transport step held, despite the explicitly signed request.
        self.assertTrue(len(self.steps) == 7 and all(row["held"] for row in self.steps))
        self.assertFalse(mission_complete("mission", "signed", historical, self.steps))
        self.assertTrue(mission_complete("mission", "unsigned", historical, self.steps))

    def test_manual_signed_poll_ack_does_not_establish_application_exchange(self):
        historical = {"report_signed": True, "reply_signed": True}
        self.assertFalse(mission_complete("mission", "signed", historical, self.steps))
        historical["application_exchange_complete"] = True
        self.assertTrue(mission_complete("mission", "signed", historical, self.steps))
        historical["application_failure"] = "consumer refused credential"
        self.assertFalse(mission_complete("mission", "signed", historical, self.steps))

    def test_ambiguous_peer_is_only_an_admission_case(self):
        self.assertTrue(mission_complete("ambiguous-peer", "signed",
                                        {"report_signed": True}, self.steps[:2]))
        self.assertFalse(mission_complete("mission", "signed",
                                         {"report_signed": True}, self.steps[:2]))

    def test_author_refusal_is_logged_and_stops_with_original_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            application = MissionConsumerExchange.__new__(MissionConsumerExchange)
            application.root = root
            application.configs = {"a": root / "consumer.json"}
            lab = SimpleNamespace(env={}, logs={}, path=lambda name: root / name)
            application.mission = SimpleNamespace(lab=lab)
            refused = subprocess.CompletedProcess([], 1, json.dumps({"outbox": []}).encode(),
                                                  b"consumer stopped: revoked author\n")
            with patch("consumer_exchange.subprocess.run", return_value=refused) as run:
                with self.assertRaisesRegex(ConsumerExchangeFailure, "revoked author"):
                    application.invoke("a", "author-refused", "report", "r1", "payload")
                self.assertEqual(run.call_count, 1)
                self.assertIn("tools/fn_consumer.py", run.call_args.args[0][1])
            self.assertIn(b"revoked author", lab.logs["author-refused"].read_bytes())


if __name__ == "__main__":
    unittest.main()
