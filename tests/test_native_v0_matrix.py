"""Native execution-backend contract for tools/v0_matrix.py.

These tests do not stand in for a two-node native run. They pin the harness
boundary so that such a run cannot silently select a Python server, lose its
image/source labels, or label an unmeasured native feed as accepted.
"""
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import v0_matrix  # noqa: E402
from deploy_gate import Step  # noqa: E402


def native_gate(home):
    return v0_matrix.V0Matrix(
        v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
        backend=v0_matrix.NATIVE_BACKEND,
        native_image="/opt/fn/fn-host",
        native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"},
        native_group="fn.letters",
    )


class NativeCommandTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.gate = native_gate(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def test_native_server_has_one_packaged_candidate_and_no_python_peer(self):
        candidates = self.gate.server_candidates(self.gate.a)
        self.assertEqual(candidates, [(
            v0_matrix.NATIVE_BACKEND,
            "env FN_NATIVE_HOST=/opt/fn/fn-host packaging/fn-native operator "
            "/srv/fn/a.toml run",
        )])
        command = candidates[0][1]
        self.assertNotIn("bin/fn", command)
        self.assertNotIn("run_owner.py", command)
        self.assertNotIn("run_reader.py", command)
        self.assertNotIn("--fn owner", command)

    def test_operator_offline_action_uses_the_same_public_subject(self):
        self.assertEqual(
            self.gate.native_operator(self.gate.b, "status"),
            "env FN_NATIVE_HOST=/opt/fn/fn-host packaging/fn-native operator "
            "/srv/fn/b.toml status",
        )

    def test_schema_two_labels_backend_source_and_image_on_every_row(self):
        self.gate.image_identity = (
            "/opt/fn/fn-host sha256=" + "1" * 64
            + "; source correspondence unestablished")
        self.gate.backfill()
        doc = self.gate.document("2026-09-21T00:00:00Z", 1.0)
        self.assertEqual(doc["schema_version"], 2)
        self.assertEqual(doc["execution"]["backend"], v0_matrix.NATIVE_BACKEND)
        self.assertEqual(doc["execution"]["source"], "abc1234")
        self.assertIn("sha256=", doc["execution"]["image"])
        for row in doc["rows"]:
            self.assertEqual(row["backend"], doc["execution"]["backend"])
            self.assertEqual(row["source"], doc["execution"]["source"])
            self.assertEqual(row["image"], doc["execution"]["image"])
        self.assertEqual(v0_matrix.validate(doc), [])

    def test_historical_schema_one_matrix_remains_valid(self):
        legacy = json.loads((ROOT / "planning/v0-matrix.json").read_text())
        self.assertEqual(legacy["schema_version"], 1)
        self.assertEqual(v0_matrix.validate(legacy), [])


class HarnessOnlyNativeGate(v0_matrix.V0Matrix):
    """No process: exercise native slice accounting and dispatch only."""

    def preflight(self):
        return None

    def ship(self):
        return None

    def push_file(self, *args, **kwargs):
        return None

    def probe_native_subject(self):
        self.image_identity = "/opt/fn/fn-host sha256=" + "2" * 64

    def witness_output(self):
        return "\n".join((
                "NATIVE-PEERING-EXPECTED-RUNTIME " + "a" * 64,
                "NATIVE-PEERING-EXPECTED-CORE " + "b" * 64,
                'NATIVE-PEERING-WITNESS {"kind":"transit-and-feed","transit":'
                '{"ab":{"offer":"335","transfer":"235","duplicate":"435","identical":true},'
                '"ba":{"offer":"335","transfer":"235","duplicate":"435","identical":true}},'
                '"feed":{"ab":{"identical":true},"ba":{"identical":true}},'
                '"identity":{"a":{"status":"observed","runtime_sha256":"' + "a" * 64 + '",'
                '"core_sha256":"' + "b" * 64 + '"},"b":{"status":"observed",'
                '"runtime_sha256":"' + "a" * 64 + '","core_sha256":"' + "b" * 64 + '"}}}',
                'NATIVE-PEERING-WITNESS {"kind":"requeue-restart","journal":true,'
                '"source_killed":true,"source_restarted":true,"target_identical":true,'
                '"identity":{"restart-a":{"status":"observed",'
                '"runtime_sha256":"' + "a" * 64 + '","core_sha256":"' + "b" * 64 + '"},'
                '"restart-b":{"status":"observed","runtime_sha256":"' + "a" * 64 + '",'
                '"core_sha256":"' + "b" * 64 + '"}}}',
            ))

    def sh(self, name, script, timeout=600, note="", expect=0):
        output = ""
        if name == "native public peering/restart witness":
            output = self.witness_output()
        step = Step(name, script, 0, output, 0.0, note, expect)
        self.steps.append(step)
        return step

    def native_config_status(self, node):
        self.emit("V0-NODE-STATUS", v0_matrix.ACCEPTED,
                  self.native_operator(node, "status"), "accepted operator status",
                  node=node.name, exit_code=0, client=v0_matrix.CLIENT_CLI)
        return True

    def start_node(self, node, tag="main"):
        node.port = 11000 + (0 if node.name == "a" else 1)
        node.pid = "1"
        node.kind = v0_matrix.NATIVE_BACKEND
        node.post_enabled = True
        self.emit("V0-NODE-START", v0_matrix.ACCEPTED,
                  self.native_operator(node, "run"),
                  "native-operator reached LISTENING {}".format(node.port),
                  node=node.name)
        return True

    def alive(self, node, tag="main"):
        return bool(node.pid)

    def post_cycle(self, node):
        self.blocked(self.POST_KEYS, "socket driver stubbed in harness unit test",
                     nodes=(node.name,), invocation="matrix.py postcycle")

    def read_surface(self, node):
        self.blocked(self.READ_KEYS, "socket driver stubbed in harness unit test",
                     nodes=(node.name,), invocation="matrix.py surface")

    def stop_node(self, node, tag="main"):
        node.pid = ""

    def transit_direction(self, source, target, way):
        """No socket driver here: leave the transit rows to the witness."""
        return None

    def capability_pins(self, node):
        self.blocked(("V0-PIN-DISPATCHED", "V0-PIN-ADVERTISED"),
                     "socket driver stubbed in harness unit test",
                     nodes=(node.name,), invocation="matrix.py pins")

    def post_concurrent(self):
        self.blocked(("V0-POST-CONCURRENT",), "socket driver stubbed in harness unit test",
                     invocation="matrix.py concurrent")

    def group_served(self, node):
        self.blocked(("V0-GROUP-SERVED",), "socket driver stubbed in harness unit test",
                     nodes=(node.name,), invocation="feed.py presence")


class NativeSliceAccountingTests(unittest.TestCase):
    def structured_gate(self, home):
        return HarnessOnlyNativeGate(
            v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
            backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
            native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})

    @staticmethod
    def replace_witness(gate, alter, *, omit_expected=None):
        lines = gate.witness_output().splitlines()
        result = []
        for line in lines:
            if omit_expected and line.startswith(omit_expected):
                continue
            if line.startswith("NATIVE-PEERING-WITNESS "):
                witness = json.loads(line.split(" ", 1)[1])
                alter(witness)
                line = "NATIVE-PEERING-WITNESS " + json.dumps(witness, sort_keys=True)
            result.append(line)
        gate.witness_output = lambda: "\n".join(result)

    @staticmethod
    def native_peering_rows(gate):
        keys = gate.TRANSIT_KEYS + gate.FEED_KEYS
        return [row for row in gate.rows
                if any(row.id == key or row.id.startswith(key + "-") for key in keys)]

    def missing_witness_gate(self, home):
        class MissingWitness(HarnessOnlyNativeGate):
            def sh(self, name, script, timeout=600, note="", expect=0):
                if name == "native public peering/restart witness":
                    step = Step(name, script, 0, "ordinary unittest output only", 0.0,
                                note, expect)
                    self.steps.append(step)
                    return step
                return super().sh(name, script, timeout, note, expect)
        return MissingWitness(v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40,
                              "abc1234", "dev", backend=v0_matrix.NATIVE_BACKEND,
                              native_image="/opt/fn/fn-host",
                              native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})

    def test_success_exit_without_structured_witness_is_not_evidence(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.missing_witness_gate(home)
            gate.execute_native_acceptance()
            rows = [row for row in gate.rows if row.id.startswith("V0-FEED-")]
            self.assertTrue(all(row.verdict == v0_matrix.NOT_EXERCISED for row in rows))

    def test_missing_transit_owner_identity_blocks_all_native_peering_rows(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            self.replace_witness(gate, lambda witness: witness.get("identity", {}).pop("b", None))
            gate.execute_native_acceptance()
            rows = self.native_peering_rows(gate)
            self.assertTrue(all(row.verdict == v0_matrix.NOT_EXERCISED for row in rows))
            self.assertTrue(all("each required live owner" in row.blocker for row in rows))

    def test_missing_expected_runtime_hash_blocks_all_native_peering_rows(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            self.replace_witness(gate, lambda witness: None,
                                 omit_expected="NATIVE-PEERING-EXPECTED-RUNTIME")
            gate.execute_native_acceptance()
            rows = self.native_peering_rows(gate)
            self.assertTrue(all(row.verdict == v0_matrix.NOT_EXERCISED for row in rows))
            self.assertTrue(all("nonempty SHA-256" in row.blocker for row in rows))

    def test_missing_image_source_does_not_suppress_a_measured_witness(self):
        with tempfile.TemporaryDirectory() as home:
            gate = HarnessOnlyNativeGate(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND,
                native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            feed = [row for row in gate.rows if row.id.startswith("V0-FEED-")]
            self.assertEqual(len(feed), len(gate.FEED_KEYS))
            self.assertEqual({row.id: row.verdict for row in feed}, {
                "V0-FEED-QUEUE": v0_matrix.ACCEPTED,
                "V0-FEED-OFFER": v0_matrix.ACCEPTED,
                "V0-FEED-ONCE": v0_matrix.NOT_EXERCISED,
                "V0-FEED-JOURNAL": v0_matrix.ACCEPTED,
            })
            starts = [row for row in gate.rows if row.id.startswith("V0-NODE-START-")]
            self.assertEqual({row.node for row in starts}, {"a", "b"})
            self.assertTrue(all("packaging/fn-native operator" in row.invocation
                                for row in starts))

    def test_the_matrix_own_transit_measurement_is_not_overwritten_by_the_witness(self):
        class MeasuredTransit(HarnessOnlyNativeGate):
            def transit_direction(self, source, target, way):
                self.from_reply("V0-TRANSIT-OFFER", "502 transit not permitted",
                                "feed.py relay", direction=way)
        with tempfile.TemporaryDirectory() as home:
            gate = MeasuredTransit(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            # The matrix's own A/B observation stands; the witness's 335 does not replace it.
            self.assertEqual(rows["V0-TRANSIT-OFFER-AB"].verdict, v0_matrix.REFUSED)
            self.assertIn("relay", rows["V0-TRANSIT-OFFER-AB"].invocation)
            # Rows the matrix did not reach are still the witness's to fill.
            self.assertEqual(rows["V0-TRANSIT-TRANSFER-AB"].verdict, v0_matrix.ACCEPTED)
            self.assertEqual(rows["V0-FEED-JOURNAL"].verdict, v0_matrix.ACCEPTED)

    def test_offline_native_administration_rows_come_from_the_operator_verbs(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            for rid in ("V0-GROUP-CREATE-A", "V0-GROUP-RETIRE-B", "V0-PEER-ADD-A",
                        "V0-CAP-SET-B", "V0-OUT-ACCEPTED-A", "V0-NODE-STOP-B",
                        "V0-OUT-RECOVER-A", "V0-PEER-REMOVE", "V0-CFG-LIVE-REFUSE"):
                self.assertIn("packaging/fn-native operator", rows[rid].invocation, rid)
                self.assertNotIn("bin/fn", rows[rid].invocation, rid)
            self.assertEqual(rows["V0-OUT-UNCERTAIN-A"].verdict, v0_matrix.NOT_BUILT)
            self.assertEqual(rows["V0-PEER-LIST-A"].verdict, v0_matrix.NOT_BUILT)
            self.assertEqual(rows["V0-TRANSIT-IDENTITY-A"].verdict, v0_matrix.NOT_BUILT)
            self.assertEqual(rows["V0-CFG-LIVE"].verdict, v0_matrix.NOT_BUILT)

    def test_successful_shared_witness_maps_only_the_cases_it_exercises(self):
        with tempfile.TemporaryDirectory() as home:
            gate = HarnessOnlyNativeGate(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND,
                native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"},
                native_image_source="source-manifest")
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            self.assertEqual(rows["V0-TRANSIT-TRANSFER-AB"].verdict,
                             v0_matrix.ACCEPTED)
            self.assertEqual(rows["V0-TRANSIT-TRANSFER-BA"].verdict,
                             v0_matrix.ACCEPTED)
            self.assertEqual(rows["V0-FEED-JOURNAL"].verdict,
                             v0_matrix.ACCEPTED)
            self.assertEqual(rows["V0-TRANSIT-TAKETHIS-AB"].verdict,
                             v0_matrix.NOT_EXERCISED)


if __name__ == "__main__":
    unittest.main()
