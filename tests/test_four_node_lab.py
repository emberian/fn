"""The four-node delay-tolerant lab, under the mock BPA.

One run of `tests/bp-dtn7/run_four_node_lab.py` is the test: it schedules the
contacts, carries the bytes and reads the journals, while every acceptance,
receipt and number stays in ACL2.  The real-BPA run is optional and is skipped
unless `DTN7_REPO` names a checkout.
"""

import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

LAB_PATH = ROOT / "tests/bp-dtn7/run_four_node_lab.py"
LAB_BUDGET_SECONDS = 300.0

# The lab lives in a directory whose name is not an identifier, so it is loaded
# by path rather than imported.
_spec = importlib.util.spec_from_file_location("fn_four_node_lab", LAB_PATH)
lab = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = lab
_spec.loader.exec_module(lab)

REQUIRED_ASSERTIONS = (
    "window_1_delivers_both_letters",
    "relay_a_accepts_both_letters",
    "relay_a_archival_receipts_survive_kill",
    "relay_a_journal_is_usable_after_recovery",
    "relay_a_onward_obligation_recoverable_after_kill",
    "relay_a_archival_receipts_unchanged_by_recovery",
    "media_hop_accepts_both_letters",
    "carried_media_is_not_modified_by_import",
    "media_reimport_is_duplicate_not_a_second_acceptance",
    "lost_receipt_regenerates_byte_identically",
    "reimport_adds_no_receipt_record",
    "attempt_expires_while_no_contact_is_open",
    "expired_attempt_leaves_the_work_outstanding",
    "retry_uses_a_distinct_transport_identity",
    "window_2_delivers_a_reordered_pair_and_a_duplicate",
    "the_pair_reaches_the_destination_in_the_reverse_of_its_submission_order",
    "destination_accepts_each_letter_once_and_calls_the_rest_duplicates",
    "destination_holds_exactly_one_acceptance_per_article",
    "destination_holds_exactly_one_archive_pin_per_article",
    "every_node_holds_the_exact_article_bytes",
    "each_node_advanced_only_by_its_own_acceptances",
    "the_same_letter_carries_a_different_local_number_at_home_and_destination",
)


# There is no blessed failure here any more.  Until 2026-09-21 this file
# carried one -- a refusal text that turned a failing run into a SKIP -- for a
# defect that had been cured the same night, and the skip then hid a second,
# unrelated break (`receive_bpa_request` gained a required `bundle` argument
# and the lab was never updated) behind a green suite.  A gate that can skip
# is a gate that reports nothing on the day it matters, so every failure of
# this lab is a failure of these tests.


class FourNodeLabTests(unittest.TestCase):
    """One mock-BPA run; the assertions live in the lab and are checked here."""

    report = None
    run_root = None
    temporary = None

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-four-node-")
        cls.run_root = Path(cls.temporary.name) / "run"
        cls.run_root.mkdir()
        try:
            cls.report = lab.run_lab(cls.run_root)
        except BaseException as error:  # a failed lab still leaves its record
            evidence = cls.run_root / "evidence.json"
            cls.report = (json.loads(evidence.read_text()) if evidence.exists()
                          else {"status": "failed", "error": repr(error)})

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_the_lab_passes_under_the_mock_bpa(self):
        self.assertEqual(self.report.get("status"), "passed", self.report.get("error"))
        self.assertEqual(self.report.get("transport"), "mock_bpa")
        self.assertTrue(self.report.get("sources_unchanged"))

    def test_the_mock_bpa_run_fits_the_five_minute_budget(self):
        self.assertLess(self.report.get("seconds", LAB_BUDGET_SECONDS), LAB_BUDGET_SECONDS)

    def test_every_named_assertion_was_checked_and_held(self):
        checked = self.report.get("assertions", {})
        for name in REQUIRED_ASSERTIONS:
            self.assertIn(name, checked)
            self.assertTrue(checked[name], name)

    def test_the_destination_holds_one_acceptance_and_one_pin_per_article(self):
        destination = self.report.get("node_states", {}).get("destination", {})
        self.assertEqual(destination["articles"], 2)
        self.assertEqual(destination["pins"], 2)
        self.assertEqual(destination["records"], 2)
        self.assertTrue(all(destination["exact_articles"].values()))

    def test_each_node_carries_its_own_numbering_frontier(self):
        frontiers = self.report.get("local_number_frontiers", {})
        states = self.report.get("node_states", {})
        self.assertTrue(frontiers)
        for name, frontier in frontiers.items():
            self.assertEqual(frontier, states[name]["articles"] + 1)

    def test_a_process_death_cut_was_actually_reached(self):
        cuts = [event for event in self.report.get("events", [])
                if event["event"] == "relay-a-killed-mid-forward"]
        self.assertEqual(len(cuts), 1)
        self.assertEqual(cuts[0]["signal"], "SIGKILL")
        self.assertIn(cuts[0]["resolution"],
                      ("durable-intent-recovered-committed",
                       "intent-absent-obligation-reestablished"))

    def test_the_forwarding_undertaking_is_recorded_as_a_proposal_only(self):
        kinds = self.report.get("relay_kinds", {"archived": {}, "forwarding": {}})
        self.assertEqual(kinds["archived"]["status"], "asserted")
        self.assertEqual(kinds["forwarding"]["status"], "proposal")
        self.assertNotIn("passed", kinds["forwarding"]["status"])

    def test_the_record_states_what_it_does_not_show(self):
        self.assertTrue(self.report.get("limitations"))
        self.assertTrue(any("not BPv7" in line for line in self.report.get("limitations", [])))


@unittest.skipUnless(os.environ.get("DTN7_REPO"),
                     "optional: set DTN7_REPO to a pinned dtn7-rs checkout")
class FourNodeLabPinnedBpaTests(unittest.TestCase):
    """The pinned-BPA run of the same lab is optional and not yet wired."""

    def test_the_pinned_bpa_run_is_declared_rather_than_silently_skipped(self):
        with tempfile.TemporaryDirectory(prefix="fn-four-node-pinned-") as temporary:
            run = Path(temporary) / "run"
            run.mkdir()
            with self.assertRaises(NotImplementedError):
                lab.run_lab(run, dtn7_repo=Path(os.environ["DTN7_REPO"]))


if __name__ == "__main__":
    unittest.main()
