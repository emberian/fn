"""Synthetic contract teeth and recorder orchestration; no native verdict."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from tools.outcome_codes import EXIT
from tools.resilience import payload_boundary as boundary
from tools.resilience.checker import check
from tools.resilience.journal import Journal
from tools.resilience.adapters.native_cuts import Run, HarnessFailure, _reply_outcome

SOURCE = "a" * 40


def fixture():
    scenario = boundary.scenario(SOURCE)
    journal = Journal(scenario.id)
    journal.environment("payload-boundary-image", source=SOURCE, manifest_sha256="b" * 64)
    journal.environment("persisted-payload-profile", returncode=int(EXIT.OK),
        stdout_hex=b"profile max-article-octets=32768 max-groups-per-article=65535\n".hex(), stderr_hex="")
    for i, op in enumerate(scenario.posts()):
        row = op.args["boundary_payload"]
        journal.environment("boundary-payload-prepared", operation=op.id,
            **row, sha256=hashlib.sha256(b"x" * row["octets"]).hexdigest(), prepared_octets=row["octets"])
        above = row["relation"] == "above"
        fields = dict(operation=op.id, returncode=int(EXIT.REFUSED if above else EXIT.OK),
            stdout_hex=b"".hex() if above else f"committed sequence={i+1} charge=1\n".encode().hex(),
            stderr_hex=b"store: payload exceeds the modelled bound\n".hex() if above else "")
        journal.environment("post-process-result", **fields)
        journal.client("reply", outcome="refused" if above else "accepted", **fields)
    journal.client("recover", operation="recover", outcome="completed", phase="healing")
    for op in scenario.posts():
        journal.client("read", operation="read-" + op.id, article=op.id,
                       result="absent" if op.args["boundary_payload"]["relation"] == "above" else "match")
    return scenario, journal


class BoundaryOutcomeTests(unittest.TestCase):
    def test_complete_source_keyed_history_has_named_refusal_witness(self):
        scenario, journal = fixture()
        verdict = check(scenario, journal)
        self.assertEqual(verdict.kind, "consistent")
        self.assertIn("payload-bound-refused", verdict.witnesses_observed)
        self.assertIn("payload-boundary-native-qualification", verdict.pending_rules)

    def test_uncertain_exit_is_not_refusal_even_with_refusal_text(self):
        scenario, journal = fixture()
        row = next(r for r in journal.of_kind("client") if r.get("operation") == "payload-above")
        row.update(returncode=int(EXIT.UNCERTAIN), outcome="uncertain")
        process = next(r for r in journal.of_kind("environment") if r.get("event") == "post-process-result" and r.get("operation") == "payload-above")
        process["returncode"] = int(EXIT.UNCERTAIN)
        verdict = check(scenario, journal)
        self.assertEqual(verdict.kind, "inconclusive")
        self.assertIn("outcome-uncertain", verdict.cause)
        row["outcome"] = "refused"
        self.assertEqual(check(scenario, journal).kind, "harness-failure")

    def test_above_A_wrong_named_refusal_and_acceptance_are_violations(self):
        for accepted in (False, True):
            scenario, journal = fixture()
            row = next(r for r in journal.of_kind("client") if r.get("operation") == "payload-above")
            if accepted:
                row.update(returncode=int(EXIT.OK), outcome="accepted", stdout_hex=b"committed sequence=3 charge=1\n".hex())
            else:
                row["stderr_hex"] = b"store: group count exceeds codec bound\n".hex()
            process = next(r for r in journal.of_kind("environment") if r.get("event") == "post-process-result" and r.get("operation") == "payload-above")
            process.update({k: row[k] for k in ("returncode", "stdout_hex", "stderr_hex")})
            self.assertEqual(check(scenario, journal).kind, "violation")

    def test_within_A_refusal_not_a_productive_pass(self):
        scenario, journal = fixture()
        row = next(r for r in journal.of_kind("client") if r.get("operation") == "payload-at")
        row.update(returncode=int(EXIT.REFUSED), outcome="refused", stdout_hex="", stderr_hex=b"store: budget refused\n".hex())
        process = next(r for r in journal.of_kind("environment") if r.get("event") == "post-process-result" and r.get("operation") == "payload-at")
        process.update({k: row[k] for k in ("returncode", "stdout_hex", "stderr_hex")})
        self.assertEqual(check(scenario, journal).kind, "violation")

    def test_missing_profile_preparation_or_reply_cannot_pass(self):
        for event in ("persisted-payload-profile", "boundary-payload-prepared", "reply"):
            scenario, journal = fixture()
            journal.records.remove(next(r for r in journal.records if r.get("event") == event))
            self.assertEqual(check(scenario, journal).kind, "harness-failure")

    def test_profile_mismatch_and_repeated_profile_are_not_ignored(self):
        scenario, journal = fixture()
        row = next(r for r in journal.records if r.get("event") == "persisted-payload-profile")
        row["stdout_hex"] = b"profile max-article-octets=1048576\n".hex()
        self.assertEqual(check(scenario, journal).kind, "harness-failure")
        scenario, journal = fixture()
        journal.records.append(copy.deepcopy(next(r for r in journal.records if r.get("event") == "persisted-payload-profile")))
        self.assertEqual(check(scenario, journal).kind, "harness-failure")

    def test_current_acl2_exit_map_and_exact_success_marker(self):
        for code, outcome in ((EXIT.REFUSED, "refused"), (EXIT.UNCERTAIN, "uncertain"), (-9, "lost")):
            self.assertEqual(_reply_outcome(SimpleNamespace(returncode=code, stdout=b"", stderr=b"")), outcome)
        for code in (EXIT.FAULT, EXIT.USAGE, EXIT.INTERRUPTED, EXIT.NOT_CONNECTED, 75, True, None):
            with self.assertRaises(HarnessFailure):
                _reply_outcome(SimpleNamespace(returncode=code, stdout=b"", stderr=b""))
        with self.assertRaises(HarnessFailure):
            _reply_outcome(SimpleNamespace(returncode=EXIT.OK, stdout=b"not duplicate\n", stderr=b""))

    def test_fault_transcript_retained_without_client_refusal(self):
        runner = object.__new__(Run)
        runner.j = Journal("unit")
        op = boundary.scenario(SOURCE).posts()[0]
        result = SimpleNamespace(returncode=int(EXIT.FAULT), stdout=b"", stderr=b"raw\xff")
        with self.assertRaises(HarnessFailure):
            runner.record_post_reply(op, result, "store-post")
        self.assertEqual(runner.j.records[0]["stderr_hex"], result.stderr.hex())
        self.assertEqual(runner.j.of_kind("client"), [])

    def test_refused_store_open_is_not_article_absence(self):
        runner = object.__new__(Run)
        runner.j = Journal("unit")
        runner.payloads = {}
        op = boundary.scenario(SOURCE).operation("read-payload-above")
        with patch.object(runner, "invoke", return_value=SimpleNamespace(returncode=int(EXIT.REFUSED),
                stdout=b"", stderr=b"store: genesis damaged\n")):
            with self.assertRaisesRegex(HarnessFailure, "not-an-absence"):
                runner.store_read(op)
        self.assertEqual(runner.j.of_kind("client"), [])

    def test_source_mismatch_refuses_before_config_or_payload_mutation(self):
        scenario = boundary.scenario(SOURCE)
        with tempfile.TemporaryDirectory() as tmp:
            image = Path(tmp) / "launcher"
            image.write_text("unexecuted fixture launcher")
            work = Path(tmp) / "work"
            work.mkdir()
            with patch("tests.native_image_provenance._published_source", return_value="c"*40):
                with self.assertRaisesRegex(ValueError, "before Store mutation"):
                    Run(scenario, image, work)
            self.assertEqual(list(work.iterdir()), [])

    def test_metadata_changes_cannot_relabel_profile_reference(self):
        for key, value in (("expected_profile_a", 1048576), ("reference_source", "c" * 40),
                           ("reference_book_sha256", "c" * 64)):
            scenario, journal = fixture()
            scenario.initial["payload_boundary"][key] = value
            self.assertEqual(check(scenario, journal).kind, "harness-failure")

    def test_image_manifest_change_cannot_seal_native_verdict(self):
        scenario = boundary.scenario(SOURCE)
        journal = Journal(scenario.id)
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "MANIFEST.json"
            manifest.write_text("original")
            journal.environment("payload-boundary-image", source=SOURCE, manifest=str(manifest),
                manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest())
            manifest.write_text("changed")
            with patch("tests.native_image_provenance._published_source", return_value=SOURCE):
                with self.assertRaisesRegex(HarnessFailure, "changed-during"):
                    boundary.image_unchanged(scenario, Path(tmp) / "unexecuted-image", journal)

    def test_run_post_observes_profile_before_first_post_and_passes_profile_flags(self):
        scenario = boundary.scenario(SOURCE)
        runner = object.__new__(Run)
        runner.s, runner.j, runner.hook = scenario, Journal(scenario.id), True
        responses = [SimpleNamespace(returncode=int(EXIT.OK), stdout=b"initialized", stderr=b""),
                     SimpleNamespace(returncode=int(EXIT.OK), stdout=b"profile max-article-octets=1048576\n", stderr=b"")]
        with patch.object(runner, "invoke", side_effect=responses) as invoke, \
                patch.object(runner, "store_post") as post:
            with self.assertRaisesRegex(HarnessFailure, "profile-mismatch"):
                runner.run_post()
            self.assertEqual(invoke.call_args_list[0].args, ("init", "--profile", "development", "fn.letters"))
            post.assert_not_called()
            self.assertTrue(any(r.get("event") == "persisted-payload-profile" for r in runner.j.records))

    def test_raw_process_result_mismatch_cannot_back_a_client_promise(self):
        scenario, journal = fixture()
        row = next(r for r in journal.of_kind("environment") if r.get("event") == "post-process-result")
        row["returncode"] = int(EXIT.FAULT)
        self.assertEqual(check(scenario, journal).kind, "harness-failure")

    def test_changed_prepared_bytes_cannot_execute_as_original_case(self):
        scenario, journal = fixture()
        op = scenario.posts()[0]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "payload"
            path.write_bytes(b"y" * op.args["boundary_payload"]["octets"])
            runner = object.__new__(Run)
            runner.j, runner.payloads = journal, {op.id: path}
            with patch.object(runner, "invoke") as invoke:
                with self.assertRaisesRegex(HarnessFailure, "payload-changed"):
                    runner.store_post(op)
                invoke.assert_not_called()
