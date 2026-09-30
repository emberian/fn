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
        self.assertEqual(len(journal.of_kind("client")), len(EVENTS) - 2)

    def test_missing_or_reordered_event_refuses(self):
        observer = SliceObserver()
        with self.assertRaises(ValueError):
            observer("fixture")
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


class SliceSemanticTests(unittest.TestCase):
    """Synthetic oracle teeth; these do not execute the native fixture."""

    def journal(self):
        observer = SliceObserver()
        records = [
            ("post-observed", dict(message_id=b"<target>", submitted_octets=b"submitted", prompt=b"340 send\r\n", reply=b"240 accepted\r\n")),
            ("post-observed", dict(message_id=b"<unrelated>", submitted_octets=b"other", prompt=b"340 send\r\n", reply=b"240 accepted\r\n")),
            ("fixture", dict(source="a" * 40, msgid=b"<target>", accepted_octets=b"stored", status=b"status pinned=yes\n", exit_code=0)),
            ("decision-cut-readback", dict(octets=b"stored")),
            ("application-replay", dict(exit_code=0)),
            ("outbox-process-death", dict(exit_code=-9)),
            ("receipt-contact-uncertain", dict(exit_code=0, stdout=b"BP transport work=job1 status=attempted\n")),
            ("checkpoint-stage-cut", dict(exit_code=-9)),
            ("receipt-contact-resumed", dict(exit_code=0, stdout=b"BP transport work=job1 status=forwarded\n", attempted_work=[b"job1"], forwarded_work=[b"job1"])),
            ("receipt-obligation-settlement", dict(matching=b"pinned=no\n", unrelated=b"pinned=yes\n")),
            ("checkpoint-complete-readback", dict(exit_code=0, octets=b"stored")),
            ("retirement-frozen-report", dict(exit_code=0, report=b"obligation id=forward-unrelated kind=forward\n", stdout=b"obligation id=forward-unrelated kind=forward\n")),
        ]
        for event, fields in records:
            observer(event, **fields)
        observer.journal.environment("image-artifact-coordinate", images=[
            dict(source="a" * 40, manifest_sha256="b" * 64, launcher="synthetic-nntp", manifest="synthetic-set/MANIFEST.json"),
            dict(source="a" * 40, manifest_sha256="b" * 64, launcher="synthetic-bp", manifest="synthetic-set/MANIFEST.json")])
        observer.journal.environment("fixture-observations-complete", semantic_verdict="pending")
        return observer.journal

    def check(self, journal):
        from tools.resilience.checker import check_bp_slice_observations
        return check_bp_slice_observations(journal, expected_source="a" * 40)

    def test_exact_relationships_pass_with_explicit_pending_composition(self):
        verdict = self.check(self.journal())
        self.assertEqual(verdict.kind, "consistent")
        self.assertTrue(verdict.verify())
        self.assertIn("bp-slice-whole-composition", verdict.pending_rules)

    def test_relationship_corruptions_are_named_violations(self):
        from tools.resilience.adapters.bp_slice_observer import encode
        cases = [("decision-cut-readback", "octets", b"changed", "accepted-bytes-preserved"),
                 ("receipt-obligation-settlement", "unrelated", b"pinned=no\n", "matching-obligation-only"),
                 ("retirement-frozen-report", "report", b"empty\n", "retirement-debt-preserved"),
                 ("post-observed", "reply", b"441 refused\r\n", "post-accepted")]
        for event, field, value, cause in cases:
            with self.subTest(cause=cause):
                journal = self.journal()
                next(r for r in journal.records if r.get("event") == event)[field] = encode(value)
                verdict = self.check(journal)
                self.assertEqual((verdict.kind, verdict.cause), ("violation", cause))

    def test_receipt_derived_fields_cannot_fabricate_healing(self):
        journal = self.journal()
        resumed = next(r for r in journal.records if r.get("event") == "receipt-contact-resumed")
        resumed["stdout"] = {"octets_hex": b"BP transport work=other status=forwarded\n".hex()}
        self.assertEqual(self.check(journal).kind, "harness-failure")
        resumed["forwarded_work"] = [{"octets_hex": b"other".hex()}]
        self.assertEqual(self.check(journal).cause, "receipt-reoffered")

    def test_missing_binding_and_ambiguous_status_fail_closed(self):
        journal = self.journal()
        journal.records[0].pop("reply")
        self.assertEqual(self.check(journal).kind, "harness-failure")
        journal = self.journal()
        journal.records[2]["status"] = {"octets_hex": b"pinned=yes pinned=no".hex()}
        self.assertEqual(self.check(journal).kind, "harness-failure")

    def test_internal_diagnostic_cannot_substitute_for_client_promise(self):
        journal = self.journal()
        journal.records[0]["kind"] = "internal"
        self.assertEqual(self.check(journal).cause,
                         "missing-or-reordered-slice-observation")

    def test_artifact_coordinate_cannot_be_omitted(self):
        journal = self.journal()
        journal.records = [r for r in journal.records
                           if r.get("event") != "image-artifact-coordinate"]
        self.assertEqual(self.check(journal).cause, "image-artifact-coordinate-missing")

    def test_source_mismatch_and_missing_completion_refuse(self):
        journal = self.journal()
        journal.records[2]["source"] = "b" * 40
        self.assertEqual(self.check(journal).cause, "fixture-source-mismatch")
        journal = self.journal()
        journal.records.pop()
        self.assertEqual(self.check(journal).cause, "fixture-not-complete")


class SliceImagePreflightTests(unittest.TestCase):
    def test_source_mismatch_refuses_before_fixture_setup(self):
        from unittest import mock
        from tools.resilience.adapters.bp_slice_observer import run_fixture
        with mock.patch("tests.native_image_provenance._published_source", return_value="b" * 40), \
                mock.patch("tests.test_bp_node_native.NativeBpNodeTests") as fixture:
            with self.assertRaisesRegex(ValueError, "differs from expected source"):
                run_fixture("unused.jsonl", "a" * 40)
            fixture.assert_not_called()
