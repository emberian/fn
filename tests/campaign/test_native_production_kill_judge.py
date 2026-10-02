"""The production-kill campaign's judge, over hand-written records (no image).

Sweep 2026-10-03 S058: the campaign measured transactions/ and the
allocation frontier, which a record-log store does not have, so every
died-absent row failed and a resubmission that appended a second record was
never seen.  It now counts the log's committed records (`fn log scan-store`)
and an unobserved store fails.  S129: an unexpected reply (a 5xx, or no reply
while the connection stayed open) was merged into "uncertain" and passed.
Each test below is one input the judge must refuse, or the matching good
input it must accept.  The native run itself is `python3 -m
tests.campaign.native_production_kill run` on a box.
"""
from __future__ import annotations

from pathlib import Path
import tempfile
import types
import unittest

from tests.campaign import native_production_kill as pk


def obs(code, status, identical=True, resubmit=None, after=None):
    out = {"post": {"code": code, "rc": code},
           "reread": {"status": status, "identical": identical, "sha256": None}}
    if resubmit is not None:
        out["resubmit"] = resubmit
        out["reread_after_resubmit"] = after or {"identical": True}
    return out


class VerdictTests(unittest.TestCase):
    def test_died_absent_needs_exactly_one_new_record(self):
        good = obs(pk.UNCERTAIN, "430", None, {"code": pk.ACCEPTED, "new_records": 1})
        self.assertEqual(pk.verdict(good, "small"), "died-absent")
        for new in (0, 2, None):
            bad = obs(pk.UNCERTAIN, "430", None, {"code": pk.ACCEPTED, "new_records": new})
            self.assertEqual(pk.verdict(bad, "small"), "died-absent-resubmit-failed", new)

    def test_a_resubmission_that_appended_a_record_is_seen(self):
        good = obs(pk.UNCERTAIN, "220", True, {"code": pk.REFUSED, "new_records": 0})
        self.assertEqual(pk.verdict(good, "small"), "died-present-identical")
        dup = obs(pk.UNCERTAIN, "220", True, {"code": pk.REFUSED, "new_records": 1})
        self.assertEqual(pk.verdict(dup, "small"), "died-present-resubmit-accepted")
        blind = obs(pk.UNCERTAIN, "220", True, {"code": pk.REFUSED, "new_records": None})
        self.assertEqual(pk.verdict(blind, "small"), "died-present-resubmit-accepted")

    def test_an_unexpected_reply_is_its_own_failing_verdict(self):
        self.assertEqual(pk.verdict(obs(pk.UNEXPECTED, "220", True), "small"),
                         "unexpected-reply")
        self.assertEqual(pk.verdict(obs(pk.UNEXPECTED, "430", None), "small"),
                         "unexpected-reply")

    def test_a_malformed_served_xref_fails_even_a_240(self):
        bad = obs(pk.ACCEPTED, "220", True)
        bad["reread"]["xref_malformed"] = True
        self.assertEqual(pk.verdict(bad, "small"), "malformed-xref")

    def test_the_client_classifies_a_hang_and_a_5xx_as_unexpected(self):
        self.assertEqual(pk.classify(None), pk.UNEXPECTED)
        self.assertEqual(pk.classify(b"503 program fault\r\n"), pk.UNEXPECTED)
        self.assertEqual(pk.classify(b""), pk.UNCERTAIN)
        self.assertEqual(pk.classify(b"441 uncertain\r\n"), pk.UNCERTAIN)


class StoreStateTests(unittest.TestCase):
    def test_a_store_without_a_journal_is_an_observation_error(self):
        with tempfile.TemporaryDirectory() as directory:
            store = Path(directory) / "store"
            (store / "transactions").mkdir(parents=True)  # the retired layout
            node = types.SimpleNamespace(store=store, image=Path("/nonexistent"),
                                         dir=Path(directory), env=lambda: {})
            state = pk.store_state(node)
            self.assertIn("no journal/", state["error"])
            self.assertNotIn("records", state)
            later = pk.store_state(node, state)
            self.assertIsNone(later["new_records"])
            self.assertEqual(pk.store_phase(state, later), "unobserved")

    def test_history_lost_compares_count_and_chain(self):
        """store_state's own comparison, the scan replaced by fixed answers."""
        from unittest import mock
        from tests.native_log_observation import CommittedHistory
        with tempfile.TemporaryDirectory() as directory:
            store = Path(directory) / "store"
            (store / "journal").mkdir(parents=True)
            node = types.SimpleNamespace(store=store, image=Path("/nonexistent"),
                                         dir=Path(directory), env=lambda: {})
            with mock.patch.object(pk, "committed_history",
                                   return_value=CommittedHistory(5, "aa")):
                pre = pk.store_state(node)
            for records, last, new, lost in ((5, "aa", 0, False), (6, "bb", 1, False),
                                             (4, "cc", -1, True), (5, "dd", 0, True)):
                with mock.patch.object(pk, "committed_history",
                                       return_value=CommittedHistory(records, last)):
                    state = pk.store_state(node, pre)
                self.assertEqual((state["new_records"], state["history_lost"]), (new, lost),
                                 (records, last))
            with mock.patch.object(pk, "committed_history",
                                   side_effect=AssertionError("log scan-store failed (4)")):
                state = pk.store_state(node, pre)
            self.assertIn("scan-store failed", state["error"])
            self.assertIsNone(state["new_records"])


class JudgeTests(unittest.TestCase):
    """judge() over a minimal record: an unobserved death fails it."""

    def record(self, death):
        msgid = "<pk-1-0000@production-kill.invalid>"
        settled = obs(pk.ACCEPTED, "220", True)
        settled["msgid"] = msgid
        return {
            "seed": 1, "stores": [{"final": {"map": {"map": {"1": msgid}}, "article": {},
                                              "inspect": {}}}],
            "calibration": [], "medians_ms": {}, "pids": [],
            "ledger": {msgid: {"size_class": "small", "events": []}},
            "iterations": [{
                "index": 0, "store": 0,
                "item": {"kind": "single", "band": "late", "sizes": ["small"], "delay_ms": 1.0},
                "restart": {"ready": True}, "kill": {"after_t0_ms": 1.0},
                "posts": [{"reply": "240 ok", "rc": 0}], "victims": [msgid],
                "settled": [settled], "stream_settled": [],
                "inspect_before_restart": {msgid: {"rc": 0, "sha256": None}},
                "pre": {"records": 3, "last": "aa", "staging": []},
                "death": death,
                "after_inspect": {**death, "new_records": 0, "history_lost": False},
                "map_before": {"map": {}}, "map_after": {"map": {"1": msgid}}}]}

    def judge(self, record) -> int:
        import contextlib
        import io
        import json
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "run.json"
            path.write_text(json.dumps(record))
            with contextlib.redirect_stdout(io.StringIO()) as out:
                code = pk.judge([str(path)])
        self.output = out.getvalue()
        return code

    def test_a_kept_history_passes_and_a_lost_or_unobserved_one_fails(self):
        kept = {"records": 4, "last": "bb", "staging": [], "new_records": 1,
                "history_lost": False}
        self.assertEqual(self.judge(self.record(kept)), 0, self.output)
        lost = {"records": 2, "last": "cc", "staging": [], "new_records": -1,
                "history_lost": True}
        self.assertEqual(self.judge(self.record(lost)), 1)
        self.assertIn("committed history lost at death", self.output)
        unobserved = {"staging": [], "new_records": None, "error": "no journal/"}
        self.assertEqual(self.judge(self.record(unobserved)), 1)
        self.assertIn("the store was not observed", self.output)


if __name__ == "__main__":
    unittest.main()
