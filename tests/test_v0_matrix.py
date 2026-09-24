"""tools/v0_matrix.py's shape, its vocabulary, and one real dry-run row.

Narrow by design. The matrix's value is a run against two nodes on a box, and
nothing here stands in for that. What is tested is the machinery a run cannot
be trusted without:

* the inventory is well formed and every id it cites is in the registries;
* the five verdicts mean what the document says, and the three ways an exit
  code or a status line becomes one of them do not overlap;
* `validate` refuses a hand-edited verdict -- the ledger rule, "counts come
  from tools, not typing", applied to a verdict word;
* one row produced by really running a command through the dry-run host, so
  the emit/document/validate path is exercised end to end and not only over a
  synthetic dictionary.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import v0_matrix  # noqa: E402
from deploy_gate import Step  # noqa: E402
from v0_matrix import (ACCEPTED, NOT_BUILT, NOT_EXERCISED, OUTCOMES,  # noqa: E402
                       PLAN, PLANNED_IDS, PLAN_BY_KEY, REFUSED, UNCERTAIN,
                       VERDICTS)


def registry(path, key):
    return {entry["id"] for entry in json.loads((ROOT / path).read_text())[key]}


class InventoryTests(unittest.TestCase):
    """PLAN is the one place the feature list lives; it has to be sound."""

    def test_every_row_id_is_unique(self):
        self.assertEqual(len(PLANNED_IDS), len(set(PLANNED_IDS)))

    def test_every_spec_belongs_to_a_declared_feature(self):
        known = {fid for fid, _ in v0_matrix.FEATURES}
        for spec in PLAN:
            self.assertIn(spec.feature, known, spec.key)

    def test_every_declared_feature_has_at_least_one_row(self):
        used = {spec.feature for spec in PLAN}
        for fid, _ in v0_matrix.FEATURES:
            self.assertIn(fid, used, fid)

    def test_every_requirement_id_is_in_the_registry(self):
        known = registry("planning/requirements.json", "requirements")
        for spec in PLAN:
            self.assertTrue(spec.requirements, spec.key)
            for ident in spec.requirements:
                self.assertIn(ident, known, "{}: {}".format(spec.key, ident))

    def test_every_scenario_id_is_in_the_catalog(self):
        known = registry("tests/scenarios/catalog.json", "scenarios")
        for spec in PLAN:
            self.assertTrue(spec.scenarios, spec.key)
            for ident in spec.scenarios:
                self.assertIn(ident, known, "{}: {}".format(spec.key, ident))

    def test_an_expectation_is_an_outcome_or_nothing(self):
        for spec in PLAN:
            self.assertIn(spec.expected, (None,) + OUTCOMES, spec.key)

    def test_a_probe_row_says_why_it_has_no_expectation(self):
        for spec in PLAN:
            if spec.expected is None:
                self.assertTrue(spec.limit, "{}: a row with no expectation has to say "
                                            "what it records instead".format(spec.key))

    def test_the_listing_runs_and_names_every_row(self):
        text = v0_matrix.render_plan()
        for spec in PLAN:
            self.assertIn(spec.key, text)


class VocabularyTests(unittest.TestCase):
    """Five verdicts, and the three mappings that produce them."""

    def test_the_vocabulary_is_the_three_outcomes_and_two_non_outcomes(self):
        self.assertEqual(VERDICTS,
                         (ACCEPTED, REFUSED, UNCERTAIN, NOT_EXERCISED, NOT_BUILT))
        self.assertEqual(OUTCOMES, (ACCEPTED, REFUSED, UNCERTAIN))

    def test_a_reply_becomes_exactly_one_outcome(self):
        for status, want in (("200 ready", ACCEPTED), ("340 send it", ACCEPTED),
                             ("111 date", ACCEPTED), ("430 no such article", REFUSED),
                             ("435 not wanted", REFUSED), ("439 rejected", REFUSED),
                             ("500 command not recognized", REFUSED),
                             ("400 service discontinued", UNCERTAIN),
                             ("403 internal fault", UNCERTAIN),
                             ("503 feature not supported", UNCERTAIN),
                             ("ConnectionResetError: [Errno 104]", UNCERTAIN),
                             ("", UNCERTAIN)):
            self.assertEqual(v0_matrix.reply_verdict(status), want, status)

    def test_a_missing_verb_is_recognised_apart_from_a_refusal(self):
        for status in ("500 command not recognized", "501 syntax error"):
            self.assertTrue(v0_matrix.unsupported(status), status)
        for status in ("435 not wanted", "430 no such article", "239 taken",
                       "502 transit is not permitted on this connection"):
            self.assertFalse(v0_matrix.unsupported(status), status)

    def test_a_permission_answer_is_not_a_missing_verb(self):
        # Measured on persvati: an fn node answers `IHAVE` with
        # "502 transit is not permitted on this connection".  The verb is
        # there and the node decided about the caller.
        for status in ("502 transit is not permitted on this connection",
                       "440 posting not permitted", "480 authentication required",
                       "483 secure connection required"):
            self.assertTrue(v0_matrix.not_permitted(status), status)
            self.assertFalse(v0_matrix.available(status), status)
        for status in ("411 no such group", "423 no article with that number",
                       "430 no article with that message-id", "340 send it",
                       "215 list follows"):
            self.assertFalse(v0_matrix.not_permitted(status), status)
            self.assertTrue(v0_matrix.available(status), status)

    def test_the_three_exit_codes_stay_distinct(self):
        self.assertEqual(v0_matrix.exit_verdict(0), ACCEPTED)
        self.assertEqual(v0_matrix.exit_verdict(1), REFUSED)
        self.assertEqual(v0_matrix.exit_verdict(3), UNCERTAIN)
        self.assertEqual(v0_matrix.exit_verdict(None), NOT_EXERCISED)
        # A code outside the vocabulary is not quietly folded into a refusal,
        # and it is not an uncertain outcome either: a fault (4), a usage
        # error (5) or a timeout (124) is a command that did not decide.  The
        # row is not-exercised, its blocker names the code, and `document`
        # counts it as `faulted` so the run cannot exit 0 over it.
        for code in (2, 4, 5, 124):
            self.assertEqual(v0_matrix.exit_verdict(code), NOT_EXERCISED, code)
            self.assertIn("exited {}".format(code), v0_matrix.exit_blocker(code))
        self.assertIn("host fault", v0_matrix.exit_blocker(4))
        self.assertIn("usage error", v0_matrix.exit_blocker(5))

    def test_a_host_fault_is_counted_and_is_not_an_outcome(self):
        with tempfile.TemporaryDirectory() as home:
            gate = v0_matrix.V0Matrix(v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40,
                                      "abc1234", "dev")
            faulted = Step("node A outcome accepted", "fn post", 4,
                           "fault operator post [Errno 2] no such file", 0.0)
            row = gate.from_step("V0-OUT-ACCEPTED", faulted, node="a")
            self.assertEqual(row.verdict, NOT_EXERCISED)
            self.assertIn("exited 4", row.blocker)
            gate.backfill()
            doc = gate.document("2026-09-22T00:00:00Z", 1.0)
            self.assertEqual(doc["summary"]["faulted"], 1)
            self.assertEqual(doc["summary"][UNCERTAIN], 0)
            self.assertEqual(doc["summary"]["disagreed"], 0)
            self.assertEqual(v0_matrix.validate(doc), [])

    def test_the_statement_vocabulary_is_read_as_its_own(self):
        # `fn statement verify`: 0 verified, 3 unverified, 4 absent, 2 no verdict.
        # 3 is NOT D13's uncertain here, and the matrix does not translate it.
        self.assertEqual(v0_matrix.V0Matrix.statement_verdict(0), ACCEPTED)
        self.assertEqual(v0_matrix.V0Matrix.statement_verdict(3), REFUSED)
        self.assertEqual(v0_matrix.V0Matrix.statement_verdict(4), REFUSED)
        self.assertEqual(v0_matrix.V0Matrix.statement_verdict(2), UNCERTAIN)


class CapabilityPinProtocolTests(unittest.TestCase):
    """The capability audit has to speak each transfer protocol correctly."""

    def test_takethis_writes_its_block_before_reading_the_final_status(self):
        # A transfer server does not answer TAKETHIS until it has the article
        # block.  This small Conn double records call order while letting every
        # other probe reach the same driver branch it uses on a live node.
        fake_driver = r'''
import json, os

def note(kind, value=""):
    with open(os.environ["PIN_LOG"], "a", encoding="utf-8") as out:
        out.write(json.dumps([kind, value]) + "\n")

class Sock:
    def sendall(self, payload):
        note("sendall", payload.decode("ascii"))
    def close(self):
        note("close")

class Conn:
    def __init__(self, port, timeout=30):
        self.sock = Sock()
        self.greeting = "200 ready"
    def cmd(self, text, multiline=False):
        note("cmd", text)
        if text.startswith("AUTHINFO USER"):
            return "381 password required", []
        if text.startswith("AUTHINFO PASS"):
            return "281 authentication accepted", []
        if text == "CAPABILITIES":
            return "101 capability list follows", ["READER", "POST", "IHAVE",
                                                     "STREAMING", "OVER", "HDR", "LIST"]
        if text == "POST":
            return "340 send article", []
        if text.startswith("IHAVE"):
            return "335 send article", []
        if text == "MODE STREAM":
            return "203 streaming permitted", []
        if text == "STARTTLS":
            return "580 TLS unavailable", []
        if text.startswith("CHECK"):
            return "238 send it", []
        if text.startswith("TAKETHIS"):
            raise AssertionError("TAKETHIS must be block-first")
        if text.startswith("NEWNEWS"):
            return "500 command not recognized", []
        if text.startswith("GROUP") or text.startswith("LISTGROUP"):
            return "211 group selected", []
        if text.startswith(("OVER", "HDR", "XOVER", "XHDR", "XPAT")):
            return "412 no newsgroup selected", []
        if text == "MODE READER":
            return "200 reader", []
        if text == "LIST ACTIVE":
            return "215 list follows", []
        return "500 command not recognized", []
    def send(self, text):
        note("send", text)
    def line(self):
        note("line")
        return "439 rejected"
    def close(self):
        self.sock.close()
'''
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            (directory / "drive.py").write_text(fake_driver)
            (directory / "matrix.py").write_text(v0_matrix.MATRIX_DRIVER)
            log = directory / "pins.log"
            environment = dict(os.environ, PIN_LOG=str(log))
            done = subprocess.run(
                [sys.executable, "matrix.py", "pins", "--port", "1",
                 "--group", "fn.letters", "--user", "matrix",
                 "--secret", "matrix-secret-8f21"],
                cwd=directory, env=environment, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
            self.assertEqual(done.returncode, 0, done.stderr + done.stdout)
            calls = [json.loads(line) for line in log.read_text().splitlines()]
        take = calls.index(["send", "TAKETHIS <pin.take@matrix.example.invalid>"])
        self.assertEqual(calls[take + 1], ["sendall", ".\r\n"])
        self.assertEqual(calls[take + 2], ["line", ""])


def make_gate(home):
    host = v0_matrix.LocalHost(Path(home))
    gate = v0_matrix.V0Matrix(host, ROOT, "a" * 40, "abc1234", "dev")
    gate._evidence_name = "planning/evidence/v0-matrix-test.md"
    return gate


class NativeEnvironmentTests(unittest.TestCase):
    def test_pinned_openssl_reaches_probe_and_public_operator(self):
        with tempfile.TemporaryDirectory() as home:
            gate = v0_matrix.V0Matrix(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/tmp/fn-host",
                native_openssl_prefix="/tank/fn/OpenSSL 3.5.8")
            command = gate.native_command("/tmp/fn.toml", "run")
            self.assertIn("FN_OPENSSL_PREFIX='/tank/fn/OpenSSL 3.5.8'", command)
            self.assertIn("FN_NATIVE_HOST=/tmp/fn-host", command)

            seen = []
            def record(title, script, **_kwargs):
                seen.append(script)
                return Step(title, script, 0,
                            "\n".join("{} sha".format(name) for name in (
                                "NATIVE-LAUNCHER-DIGEST", "NATIVE-IMAGE-DIGEST",
                                "NATIVE-RUNTIME-DIGEST", "NATIVE-CORE-DIGEST")), 0.0)
            gate.sh = record
            gate.probe_native_subject()
            self.assertEqual(len(seen), 1)
            self.assertIn("FN_OPENSSL_PREFIX='/tank/fn/OpenSSL 3.5.8' "
                          "FN_NATIVE_HOST=\"$image\"", seen[0])



class EmitTests(unittest.TestCase):
    """The only way a row is created, and what it refuses to create."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.gate = make_gate(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_a_verdict_outside_the_vocabulary_is_refused(self):
        with self.assertRaises(v0_matrix.GateError):
            self.gate.emit("V0-NODE-LOOPBACK", "pass", "cmd", "obs")

    def test_a_row_that_did_not_run_must_name_its_blocker(self):
        with self.assertRaises(v0_matrix.GateError):
            self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs")
        self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs",
                       blocker="no BP node is wired behind the layer", owner="w9/dtn-2")
        self.assertIn("V0-BP-NODE", self.gate.emitted)

    def test_a_row_is_emitted_once(self):
        self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs", blocker="x")
        with self.assertRaises(v0_matrix.GateError):
            self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs", blocker="x")

    def test_agrees_is_null_for_a_row_that_is_not_an_outcome(self):
        row = self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs", blocker="x")
        self.assertIsNone(row.agrees)

    def test_a_refusal_row_that_draws_its_refusal_agrees(self):
        row = self.gate.emit("V0-OUT-REFUSED", REFUSED, "fn lookup", "rc=1", node="a")
        self.assertEqual(PLAN_BY_KEY["V0-OUT-REFUSED"].expected, REFUSED)
        self.assertTrue(row.agrees)

    def test_exact_wildcard_config_usage_is_distinct_from_request_refusal(self):
        spec = PLAN_BY_KEY["V0-NODE-LOOPBACK"]
        row = self.gate.emit("V0-NODE-LOOPBACK", NOT_EXERCISED,
                             'host = "0.0.0.0"; fn operator run',
                             "rc=5 " + spec.expected_usage, exit_code=5)
        record = row.json("abc1234")
        self.assertIsNone(row.agrees)
        self.assertTrue(v0_matrix.expected_usage_matches(record))
        self.assertEqual(v0_matrix.derive([record])["summary"]["faulted"], 0)
        record["observed"] = "rc=5 usage operator request (OTHER INVALID)"
        self.assertFalse(v0_matrix.expected_usage_matches(record))
        self.assertEqual(v0_matrix.derive([record])["summary"]["faulted"], 1)
        record["exit_code"] = 4
        self.assertEqual(v0_matrix.derive([record])["summary"]["faulted"], 1)

    def test_an_outcome_row_names_the_client_that_saw_it(self):
        row = self.gate.emit("V0-OUT-REFUSED", REFUSED, "fn lookup", "rc=1", node="a")
        self.assertEqual(row.client, v0_matrix.CLIENT_DRIVER)
        self.assertFalse(row.independent)

    def test_a_foreign_client_is_marked_independent(self):
        row = self.gate.emit("V0-CLIENT-NNTPLIB", ACCEPTED, "python3.12 ...", "ok",
                             node="a", client="stdlib nntplib on python3.12")
        self.assertTrue(row.independent)

    def test_a_row_that_did_not_run_has_no_client(self):
        row = self.gate.emit("V0-BP-NODE", NOT_BUILT, "cmd", "obs", blocker="x")
        self.assertIsNone(row.client)
        self.assertIsNone(row.independent)

    def test_backfill_leaves_no_planned_row_silent(self):
        self.gate.backfill()
        self.assertEqual(len(self.gate.rows), len(PLANNED_IDS))
        for row in self.gate.rows:
            self.assertEqual(row.verdict, NOT_EXERCISED)
            self.assertTrue(row.blocker)


class DryRunRowTests(unittest.TestCase):
    """One row from a command really run through the dry-run host."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.gate = make_gate(cls.temp.name)
        # This stands in for a refused lookup; it exercises report plumbing.
        step = cls.gate.sh("dry-run refusal", "echo 'article absent' ; exit 1",
                           expect=None)
        cls.row = cls.gate.from_step("V0-OUT-REFUSED", step, node="a",
                                     limit="a dry-run stand-in, not bin/fn")
        cls.gate.backfill()
        cls.doc = cls.gate.document("2026-09-20T00:00:00Z", 1.0)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_the_row_is_a_refusal_and_agrees(self):
        self.assertEqual(self.row.verdict, REFUSED)
        self.assertTrue(self.row.agrees)
        self.assertEqual(self.row.exit_code, 1)
        self.assertIn("article absent", self.row.observed)

    def test_the_row_names_its_invocation_its_revision_and_its_log(self):
        payload = self.row.json("abc1234")
        self.assertTrue(payload["invocation"])
        self.assertEqual(payload["revision"], "abc1234")
        self.assertTrue(payload["log"])
        self.assertTrue(payload["limit"])

    def test_the_document_validates(self):
        self.assertEqual(v0_matrix.validate(self.doc), [])

    def test_the_document_indexes_by_requirement_and_scenario(self):
        self.assertIn("V0-OUT-REFUSED-A", self.doc["by_requirement"]["FLR-002"])
        self.assertIn("V0-OUT-REFUSED-A", self.doc["by_scenario"]["SCN-021"])

    def test_the_summary_is_over_the_rows(self):
        self.assertEqual(self.doc["summary"]["total"], len(PLANNED_IDS))
        self.assertEqual(self.doc["summary"][REFUSED], 1)
        self.assertEqual(self.doc["summary"][NOT_EXERCISED], len(PLANNED_IDS) - 1)


class ValidateRefusesTypingTests(unittest.TestCase):
    """A verdict a human wrote into the file does not survive `make check`."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        gate = make_gate(temp.name)
        gate.backfill()
        self.doc = gate.document("2026-09-20T00:00:00Z", 1.0)

    def test_the_generated_document_is_accepted(self):
        self.assertEqual(v0_matrix.validate(self.doc), [])

    def test_a_hand_edited_verdict_breaks_the_digest(self):
        doc = json.loads(json.dumps(self.doc))
        doc["rows"][0]["verdict"] = ACCEPTED
        doc["rows"][0]["agrees"] = True
        doc["rows"][0]["blocker"] = None
        doc["summary"][NOT_EXERCISED] -= 1
        doc["summary"][ACCEPTED] += 1
        problems = v0_matrix.validate(doc)
        self.assertTrue(any("rows_digest" in p for p in problems), problems)

    def test_a_forged_digest_still_fails_on_the_summary(self):
        doc = json.loads(json.dumps(self.doc))
        doc["rows"][0]["verdict"] = ACCEPTED
        doc["rows"][0]["agrees"] = True
        doc["rows"][0]["blocker"] = None
        doc["rows_digest"] = v0_matrix.hashlib.sha256(json.dumps(
            doc["rows"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        problems = v0_matrix.validate(doc)
        self.assertTrue(any("summary" in p for p in problems), problems)

    def test_a_client_rewritten_by_hand_is_refused(self):
        doc = json.loads(json.dumps(self.doc))
        doc["rows"][0]["client"] = "a newsreader that never ran"
        problems = v0_matrix.validate(doc)
        self.assertTrue(problems)

    def test_a_missing_planned_row_is_refused(self):
        doc = json.loads(json.dumps(self.doc))
        doc["rows"] = doc["rows"][1:]
        problems = v0_matrix.validate(doc)
        self.assertTrue(any("missing from the file" in p for p in problems), problems)

    def test_a_row_that_is_not_in_the_plan_is_refused(self):
        doc = json.loads(json.dumps(self.doc))
        doc["rows"][0]["id"] = "V0-INVENTED-001"
        problems = v0_matrix.validate(doc)
        self.assertTrue(any("not in the tool's PLAN" in p for p in problems), problems)

    def test_a_document_written_by_something_else_is_refused(self):
        doc = json.loads(json.dumps(self.doc))
        doc["generated_by"] = "a person with an editor"
        problems = v0_matrix.validate(doc)
        self.assertTrue(any("generated_by" in p for p in problems), problems)

    def test_a_row_planned_after_the_run_is_added_as_a_non_outcome(self):
        """A row planned later gains a not-exercised row, never a verdict.

        `--plan-rows` is how a lane that adds a probe to PLAN keeps
        `planning/v0-matrix.json` complete without claiming a measurement it
        did not take. Everything it writes is re-derived by `derive`, so the
        digest, the summary and the indexes are the tool's and not typed.
        """
        doc = json.loads(json.dumps(self.doc))
        dropped = doc["rows"][0]["id"]
        doc["rows"] = doc["rows"][1:]
        added = v0_matrix.add_planned_rows(doc)
        self.assertEqual(added, [dropped])
        self.assertEqual(v0_matrix.validate(doc), [])
        row = [r for r in doc["rows"] if r["id"] == dropped][0]
        self.assertEqual(row["verdict"], NOT_EXERCISED)
        self.assertIsNone(row["agrees"])
        self.assertIn("planned after the recorded run", row["blocker"])

    def test_plan_rows_over_a_complete_file_changes_nothing(self):
        doc = json.loads(json.dumps(self.doc))
        self.assertEqual(v0_matrix.add_planned_rows(doc), [])
        self.assertEqual(doc, self.doc)


class CommittedMatrixTests(unittest.TestCase):
    """The file in the tree is the one the tool wrote."""

    def test_the_committed_matrix_validates(self):
        path = ROOT / v0_matrix.MATRIX_JSON
        if not path.is_file():
            self.skipTest("{} has not been generated yet".format(v0_matrix.MATRIX_JSON))
        self.assertEqual(v0_matrix.check_file(path), [])


class ReportPublicationTests(unittest.TestCase):
    """Concurrent/historical runs must not silently regress selected evidence."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        gate = make_gate(temp.name)
        gate.backfill()
        self.doc = gate.document("2026-09-21T06:00:00Z", 1.0)
        self.target = self.repo / v0_matrix.MATRIX_JSON

    def test_parallel_runs_receive_distinct_history_directories(self):
        with ThreadPoolExecutor(max_workers=8) as workers:
            dirs = list(workers.map(
                lambda _: v0_matrix.new_run_directory(self.repo, "abc1234"), range(20)))
        self.assertEqual(len(set(dirs)), len(dirs))
        self.assertTrue(all(path.is_dir() for path in dirs))
        self.assertFalse(self.target.exists())

    def test_current_measurement_is_published_as_valid_json(self):
        with patch.object(v0_matrix, "resolve", return_value=("a" * 40, "aaaaaaa")):
            v0_matrix.publish_current(self.repo, self.doc)
        self.assertEqual(json.loads(self.target.read_text()), self.doc)
        self.assertEqual(v0_matrix.check_file(self.target), [])

    def test_custom_report_paths_cannot_overwrite_another_run(self):
        path = self.repo / "report.json"
        v0_matrix.write_report_once(path, "first run\n")
        with self.assertRaises(FileExistsError):
            v0_matrix.write_report_once(path, "second run\n")
        self.assertEqual(path.read_text(), "first run\n")
        self.assertEqual(list(self.repo.glob(".matrix-report-*")), [])

    def test_an_old_source_cannot_replace_the_selected_report(self):
        self.target.parent.mkdir(parents=True)
        self.target.write_text(json.dumps(self.doc))
        before = self.target.read_bytes()
        with patch.object(v0_matrix, "resolve", return_value=("b" * 40, "bbbbbbb")):
            with self.assertRaisesRegex(v0_matrix.GateError, "not this checkout's HEAD"):
                v0_matrix.publish_current(self.repo, self.doc)
        self.assertEqual(self.target.read_bytes(), before)

    def test_parallel_publishers_leave_the_newer_run_selected(self):
        newer = dict(self.doc, generated_at="2026-09-21T06:01:00Z")

        def publish(doc):
            try:
                v0_matrix.publish_current(self.repo, doc)
            except v0_matrix.GateError as error:
                self.assertIn("newer matrix", str(error))

        with patch.object(v0_matrix, "resolve", return_value=("a" * 40, "aaaaaaa")):
            with ThreadPoolExecutor(max_workers=2) as workers:
                list(workers.map(publish, [newer, self.doc]))
        self.assertEqual(json.loads(self.target.read_text()), newer)

    def test_overlay_dry_run_and_invalid_rows_cannot_publish(self):
        with patch.object(v0_matrix, "resolve", return_value=("a" * 40, "aaaaaaa")):
            for kwargs in ({"overlay": True}, {"simulated": True}):
                with self.assertRaises(v0_matrix.GateError):
                    v0_matrix.publish_current(self.repo, self.doc, **kwargs)
            broken = dict(self.doc, rows_digest="edited")
            with self.assertRaisesRegex(v0_matrix.GateError, "inconsistent"):
                v0_matrix.publish_current(self.repo, broken)
        self.assertFalse(self.target.exists())

    def test_a_run_the_driver_stopped_early_cannot_publish(self):
        # 6c0626c5: a gate error left every row not exercised, and the run
        # was still written to planning/v0-matrix.json.
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        gate = make_gate(temp.name)
        gate.backfill(stopped=v0_matrix.GateError("deploy identity is already active"))
        stopped = gate.document("2026-09-21T06:00:00Z", 1.0)
        self.assertEqual(v0_matrix.validate(stopped), [])
        self.assertTrue(v0_matrix.stopped_early(stopped))
        self.assertEqual(v0_matrix.stopped_early(self.doc), [])
        with patch.object(v0_matrix, "resolve", return_value=("a" * 40, "aaaaaaa")):
            with self.assertRaisesRegex(v0_matrix.GateError, "stopped early"):
                v0_matrix.publish_current(self.repo, stopped)
            with self.assertRaisesRegex(v0_matrix.GateError, "stopped early"):
                v0_matrix.publish_current(self.repo, self.doc, stopped=True)
        self.assertFalse(self.target.exists())


if __name__ == "__main__":
    unittest.main()
