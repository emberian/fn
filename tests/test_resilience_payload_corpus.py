import hashlib
from pathlib import Path
import tempfile
import unittest
from tools.resilience import payload_corpus
from tools.resilience.adapters.native_cuts import Run, scenario_for
from tests.campaign.native_cuts import POST_LOG_CUTS

SOURCE = "a" * 40


class BoundaryPayloadTests(unittest.TestCase):
    def test_zero_and_arbitrary_width_boundaries_keep_source_coordinates(self):
        rows = payload_corpus.cases([
            dict(name="zero", octets=0, source=SOURCE, unit="complete-payload-octets"),
            dict(name="wide", octets=10**100, source=SOURCE, unit="complete-payload-octets")])
        self.assertEqual([r["octets"] for r in rows], [0, 1, 10**100-1, 10**100, 10**100+1])
        self.assertTrue(all(r["source"] == SOURCE for r in rows))

    def test_actual_native_cut_preparation_keeps_exact_input_and_journal(self):
        scenario = scenario_for(POST_LOG_CUTS[0])
        post = scenario.posts()[1]
        row = dict(boundary="supplied-fixture", source=SOURCE, octets=8193, boundary_octets=8193, relation="at")
        post.args["boundary_payload"] = row
        scenario.initial["payload_preparation_budget"] = 8193
        with tempfile.TemporaryDirectory() as tmp:
            runner = Run(scenario, Path(tmp) / "unexecuted-image", Path(tmp))
            data = runner.payloads[post.id].read_bytes()
            self.assertEqual(data, b"x" * 8193)
            record = next(r for r in runner.j.records if r.get("event") == "boundary-payload-prepared")
            self.assertEqual(record["sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual(record["admission"], "unobserved")

    def test_budget_refuses_before_config_or_payload_write(self):
        scenario = scenario_for(POST_LOG_CUTS[0])
        scenario.posts()[1].args["boundary_payload"] = dict(boundary="huge", source=SOURCE,
            octets=10**100, boundary_octets=10**100-1, relation="above")
        scenario.initial["payload_preparation_budget"] = 8192
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "no payload truncated"):
                Run(scenario, Path(tmp) / "unexecuted-image", Path(tmp))
            self.assertEqual(list(Path(tmp).iterdir()), [])

    def test_literal_served_envelope_is_counted_and_never_truncated(self):
        row = dict(boundary="small", source=SOURCE, octets=12, boundary_octets=12, relation="at")
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "payload"
            result = payload_corpus.write(path, row, b"header\r\n", b"\r\n")
            self.assertEqual(path.read_bytes(), b"header\r\nxx\r\n")
            self.assertEqual(result["prepared_octets"], 12)
            with self.assertRaisesRegex(ValueError, "smaller"):
                payload_corpus.write(Path(tmp) / "too-small", dict(row, octets=1), b"header")
            self.assertFalse((Path(tmp) / "too-small").exists())

    def test_bool_missing_source_and_missing_budget_refuse(self):
        with self.assertRaises(ValueError):
            payload_corpus.cases([dict(name="bad", octets=True, source=SOURCE, unit="complete-payload-octets")])
        with self.assertRaises(ValueError):
            payload_corpus.cases([dict(name="bad", octets=1, source="dev", unit="complete-payload-octets")])
        scenario = scenario_for(POST_LOG_CUTS[0])
        scenario.posts()[1].args["boundary_payload"] = dict(boundary="small", source=SOURCE, octets=1, boundary_octets=1, relation="at")
        with self.assertRaisesRegex(ValueError, "explicit experimental"):
            payload_corpus.preflight(scenario.posts(), None)

    def test_unsupported_boundary_relation_cannot_be_retained_as_fact(self):
        scenario = scenario_for(POST_LOG_CUTS[0])
        scenario.posts()[1].args["boundary_payload"] = dict(boundary="wrong", source=SOURCE,
            octets=5, boundary_octets=5, relation="above")
        with self.assertRaisesRegex(ValueError, "relation disagrees"):
            payload_corpus.preflight(scenario.posts(), 10)
