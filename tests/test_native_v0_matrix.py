"""Native execution-backend contract for tools/v0_matrix.py.

These tests do not stand in for a two-node native run. They pin the harness
boundary so that such a run cannot silently select a Python server, lose its
image/source labels, or label an unmeasured native feed as accepted.
"""
import json
import os
from pathlib import Path
import re
import subprocess
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

    # Canned host output, by step name.  A native row that is a real
    # measurement needs the observation its phase reads -- a driver payload,
    # a LISTENING line, a configured path -- and a fixture that returns an
    # empty string for all of them tests only the not-exercised branch.
    AUTH_PAYLOAD = json.dumps({
        "CAPABILITIES BEFORE": "101 capabilities",
        "advertised_before": ["READER", "POST", "AUTHINFO"],
        "AUTHINFO ADVERTISED": True,
        "POST BEFORE": "480 authentication required",
        "AUTHINFO USER": "381 password required",
        "AUTHINFO PASS": "281 authentication accepted",
        "CAPABILITIES AFTER": "101 capabilities",
        "advertised_after": ["READER", "POST"],
        "AUTHINFO WITHDRAWN": True,
        "POST AFTER": "340 send it",
        "POST AFTER COMMIT": "240 article received",
        "AUTHINFO WRONG": "481 authentication failed",
        "ok": True,
    })
    UNGATED_AUTH_PAYLOAD = json.dumps({
        "CAPABILITIES BEFORE": "101 capabilities",
        "advertised_before": ["READER", "POST", "AUTHINFO"],
        "AUTHINFO ADVERTISED": True,
        "POST BEFORE": "340 send it",
        "AUTHINFO USER": "381 password required",
        "AUTHINFO PASS": "281 authentication accepted",
        "advertised_after": ["READER", "POST"],
        "AUTHINFO WITHDRAWN": True,
        "POST AFTER": "340 send it",
        "POST AFTER COMMIT": "240 article received",
        "AUTHINFO WRONG": "481 authentication failed",
        "ok": True,
    })

    def canned(self, name):
        if name == "native public peering/restart witness":
            return self.witness_output()
        if name == "native AUTHINFO secret":
            return "SECRET-READY"
        if name.startswith("start server"):
            return "LISTENING 11292"
        if name.endswith("principal list"):
            return "matrix principal=" + "c" * 64 + " posting=true"
        if name.endswith("configured store"):
            return "/srv/fn/a-store"
        if "auth-required AUTHINFO gate" in name:
            return self.AUTH_PAYLOAD
        if "AUTHINFO session" in name:
            return self.UNGATED_AUTH_PAYLOAD
        if "serves fn.matrix.live" in name:
            return json.dumps({"groups": {"fn.matrix.live": "211 1 1 1 fn.matrix.live"},
                               "ok": True})
        if name == "nntplib interpreter":
            return "USE python3.12"
        if name.startswith("independent nntplib client"):
            return json.dumps({"client": "stdlib nntplib", "python": "3.12.7",
                               "commands": ["CAPABILITIES", "GROUP", "ARTICLE"],
                               "group": {"count": 1}, "article_lines": 9,
                               "absent": "430 no such article", "ok": True})
        return ""

    # The exit code a real image gives, where it is not 0 and the row's
    # honesty depends on it: the wildcard listener is refused at
    # configuration ADMISSION and reported as a usage error, and an offline
    # administrative command against a store a live owner holds is refused.
    CANNED_RC = {"loopback refusal: run": v0_matrix.EXIT_USAGE,
                 "offline group create while the owner holds the store": 1}

    def sh(self, name, script, timeout=600, note="", expect=0):
        step = Step(name, script, self.CANNED_RC.get(name, 0), self.canned(name),
                    0.0, note, expect)
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
            self.assertEqual(rows["V0-CFG-LIVE"].verdict, v0_matrix.ACCEPTED)
            # The node's own path identity is a real operator step now, before
            # the peer records and before either owner starts.
            identity = rows["V0-TRANSIT-IDENTITY-A"]
            self.assertIn("policy set path-identity a.gate.example.invalid",
                          identity.invocation)
            self.assertNotEqual(identity.verdict, v0_matrix.NOT_BUILT)
            order = [row.id for row in gate.rows]
            self.assertLess(order.index("V0-TRANSIT-IDENTITY-A"),
                            order.index("V0-PEER-ADD-A"))
            self.assertLess(order.index("V0-PEER-ADD-A"),
                            order.index("V0-NODE-START-A"))

    def test_native_authinfo_rows_are_measured_and_name_their_two_subjects(self):
        """F-AUTH: the credential half on the served node, the policy half on
        a scratch owner that requires authentication.  The supplied
        configuration is never rewritten and no secret is in an invocation."""
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            self.assertEqual(rows["V0-AUTH-NEW"].verdict, v0_matrix.NOT_BUILT)
            self.assertIn("principal new", rows["V0-AUTH-NEW"].blocker)
            for node in ("A", "B"):
                enrol = rows["V0-AUTH-PASSWORD-" + node]
                self.assertEqual(enrol.verdict, v0_matrix.ACCEPTED)
                self.assertIn("principal set-password matrix", enrol.invocation)
                self.assertIn("auth.secret.pair", enrol.invocation)
                self.assertEqual(rows["V0-AUTH-LIST-" + node].verdict,
                                 v0_matrix.ACCEPTED)
                self.assertIn("principal list", rows["V0-AUTH-LIST-" + node].invocation)
                # The five session rows come from the SERVED node's listener.
                self.assertEqual(rows["V0-AUTH-ADVERTISED-" + node].verdict,
                                 v0_matrix.ACCEPTED)
                self.assertEqual(rows["V0-AUTH-LOGIN-" + node].verdict,
                                 v0_matrix.ACCEPTED)
                self.assertEqual(rows["V0-AUTH-WITHDRAWN-" + node].verdict,
                                 v0_matrix.ACCEPTED)
                self.assertEqual(rows["V0-AUTH-POST-" + node].verdict,
                                 v0_matrix.ACCEPTED)
                self.assertEqual(rows["V0-AUTH-WRONG-" + node].verdict,
                                 v0_matrix.REFUSED)
                self.assertIn("--secret-file",
                              rows["V0-AUTH-LOGIN-" + node].invocation)
                # The gated row is the policy row, and it says whose policy.
                gated = rows["V0-AUTH-GATED-" + node]
                self.assertEqual(gated.verdict, v0_matrix.REFUSED)
                self.assertIn("480", gated.observed)
                self.assertIn("[auth] required = true", gated.limit)
                self.assertIn("scratch store beside node", gated.limit)
            for row in gate.rows:
                self.assertIsNone(re.search(r"--secret (?!'')\S", row.invocation),
                                  row.id)
            # Every credential step ran before either owner started, because
            # the native owner loads the registry once, before its listener.
            order = [row.id for row in gate.rows]
            self.assertLess(order.index("V0-AUTH-PASSWORD-A"),
                            order.index("V0-NODE-START-A"))
            self.assertLess(order.index("V0-AUTH-GATED-A"),
                            order.index("V0-NODE-START-A"))

    def test_no_recorded_command_of_the_native_slice_carries_the_secret(self):
        """The secret is generated on the execution host and read from a file:
        `report.md` renders every command in full, so a secret in a command
        word or in an installed file's base64 would be in the evidence."""
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            secret = [step for step in gate.steps
                      if step.name == "native AUTHINFO secret"]
            self.assertEqual(len(secret), 1)
            self.assertIn("/dev/urandom", secret[0].command)
            self.assertNotIn("install auth.secret",
                             [step.name for step in gate.steps])

    def test_live_group_administration_is_the_verb_plus_a_socket_probe(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            live = rows["V0-CFG-LIVE"]
            self.assertEqual(live.verdict, v0_matrix.ACCEPTED)
            self.assertIn("group create fn.matrix.live", live.invocation)
            self.assertIn("presence", live.invocation)
            self.assertIn("211", live.observed)
            self.assertEqual(live.client, v0_matrix.CLIENT_DRIVER)
            # The refusal half is on the OFFLINE executor: a second
            # configuration over the same store whose control path is unbound.
            refuse = rows["V0-CFG-LIVE-REFUSE"]
            self.assertEqual(refuse.verdict, v0_matrix.REFUSED)
            self.assertIn("/offline/fn.toml", refuse.invocation)
            self.assertIn("offline executor", refuse.limit)
            self.assertIn("never-bound.sock", "\n".join(
                step.command for step in gate.steps))
            self.assertNotIn("/srv/fn/a.toml", refuse.invocation)

    def test_a_declared_group_the_service_does_not_serve_is_not_accepted(self):
        class SilentReconfiguration(HarnessOnlyNativeGate):
            def canned(self, name):
                if "serves fn.matrix.live" in name:
                    return json.dumps({"groups": {"fn.matrix.live": "411 no such group"},
                                       "ok": False})
                return super().canned(name)
        with tempfile.TemporaryDirectory() as home:
            gate = SilentReconfiguration(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            row = {r.id: r for r in gate.rows}["V0-CFG-LIVE"]
            # The verb exited 0; the running service is what decides the row.
            self.assertEqual(row.verdict, v0_matrix.REFUSED)
            self.assertIn("411", row.observed)

    def test_wildcard_listener_is_measured_and_its_usage_code_is_named(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            row = {r.id: r for r in gate.rows}["V0-NODE-LOOPBACK"]
            # 5 is not one of the three outcomes, so the row is not-exercised
            # with the code named -- never a refusal read off a usage error.
            self.assertEqual(row.verdict, v0_matrix.NOT_EXERCISED)
            self.assertEqual(row.exit_code, v0_matrix.EXIT_USAGE)
            self.assertIn("exited 5", row.blocker)
            self.assertIn('host = "0.0.0.0"', row.invocation)
            self.assertIn("packaging/fn-native operator", row.invocation)
            self.assertIn("run", row.invocation)
            self.assertIn("configuration admission", row.limit)
            self.assertIn("non-loopback IPv4", row.limit)

    def test_the_independent_client_runs_on_the_native_backend(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            for node in ("A", "B"):
                row = rows["V0-CLIENT-NNTPLIB-" + node]
                self.assertEqual(row.verdict, v0_matrix.ACCEPTED)
                self.assertIn("independent.py", row.invocation)
                self.assertIn("python3.12", row.invocation)
                self.assertIn("--group fn.letters", row.invocation)
                # The only row in the matrix fn did not observe itself.
                self.assertTrue(row.independent)
            self.assertEqual(rows["V0-CLIENT-SLRN"].verdict, v0_matrix.NOT_EXERCISED)

    def test_no_interpreter_with_nntplib_blocks_the_client_rows_honestly(self):
        class NoNntplib(HarnessOnlyNativeGate):
            def canned(self, name):
                if name == "nntplib interpreter":
                    return "NONE"
                return super().canned(name)
        with tempfile.TemporaryDirectory() as home:
            gate = NoNntplib(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = [row for row in gate.rows if row.id.startswith("V0-CLIENT-NNTPLIB")]
            self.assertEqual(len(rows), 2)
            for row in rows:
                self.assertEqual(row.verdict, v0_matrix.NOT_EXERCISED)
                self.assertIn("stdlib nntplib", row.blocker)

    def test_an_image_without_the_principal_verb_reads_as_not_exercised(self):
        """A usage error is not an outcome: the credential rows carry the
        code and the session rows name the enrolment that did not happen."""
        class NoPrincipalVerb(HarnessOnlyNativeGate):
            def sh(self, name, script, timeout=600, note="", expect=0):
                step = super().sh(name, script, timeout, note, expect)
                if "principal" in script:
                    step = Step(name, script, v0_matrix.EXIT_USAGE,
                                "usage: fn operator CONFIG "
                                "{help|run|post|status|recover|group|capacity|peer}",
                                0.0, note, expect)
                    self.steps[-1] = step
                return step
        with tempfile.TemporaryDirectory() as home:
            gate = NoPrincipalVerb(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            for rid in ("V0-AUTH-PASSWORD-A", "V0-AUTH-LIST-A", "V0-AUTH-LOGIN-A",
                        "V0-AUTH-ADVERTISED-B", "V0-AUTH-GATED-B"):
                self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED, rid)
                self.assertTrue(rows[rid].blocker, rid)
            self.assertIn("exited 5", rows["V0-AUTH-PASSWORD-A"].blocker)
            self.assertIn("set-password", rows["V0-AUTH-LOGIN-A"].blocker)

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


class AuthDriverTests(unittest.TestCase):
    """The shipped `auth` phase itself, driven against a fake Conn.

    The two things the native slice depends on and that no gate-level stub
    can show: the secret arrives as a FILE and never as an argument, and the
    unauthenticated POST probe does not leave the server inside a transfer.
    """

    FAKE_DRIVER = r'''
import json, os

def note(kind, value=""):
    with open(os.environ["AUTH_LOG"], "a", encoding="utf-8") as out:
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
        if text == "CAPABILITIES":
            return "101 capability list follows", ["READER", "POST", "AUTHINFO USER"]
        if text.startswith("AUTHINFO USER"):
            return "381 password required", []
        if text.startswith("AUTHINFO PASS"):
            return ("281 authentication accepted"
                    if text == "AUTHINFO PASS 0f0f0f0f0f0f0f0f" else
                    "481 authentication failed"), []
        if text == "POST":
            return "340 send article", []
        return "500 command not recognized", []
    def send(self, text):
        note("send", text)
    def line(self):
        note("line")
        return "441 posting failed"
    def close(self):
        self.sock.close()
'''

    def run_auth(self, directory, extra):
        (directory / "drive.py").write_text(self.FAKE_DRIVER)
        (directory / "matrix.py").write_text(v0_matrix.MATRIX_DRIVER)
        log = directory / "auth.log"
        done = subprocess.run(
            [sys.executable, "matrix.py", "auth", "--port", "1",
             "--group", "fn.letters", "--user", "matrix",
             "--msgid", "<auth@example.invalid>"] + extra,
            cwd=directory, env=dict(os.environ, AUTH_LOG=str(log)), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        return done, calls

    def test_the_secret_is_read_from_a_file_and_used_as_the_password(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            secret = directory / "auth.secret"
            secret.write_text("0f0f0f0f0f0f0f0f\n")
            done, calls = self.run_auth(directory, ["--secret-file", str(secret)])
            self.assertEqual(done.returncode, 0, done.stderr + done.stdout)
            result = json.loads(done.stdout.strip().splitlines()[-1])
            self.assertEqual(result["AUTHINFO PASS"], "281 authentication accepted")
            # The wrong-password probe must be a DIFFERENT password, or the
            # 481 row would be measuring the same secret as the 281 row.
            self.assertEqual(result["AUTHINFO WRONG"], "481 authentication failed")
            self.assertIn(["cmd", "AUTHINFO PASS 0f0f0f0f0f0f0f0f"], calls)
            self.assertIn(["cmd", "AUTHINFO PASS not-0f0f0f0f0f0f0f0f"], calls)

    def test_a_permitted_unauthenticated_post_is_closed_not_abandoned(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            secret = directory / "auth.secret"
            secret.write_text("0f0f0f0f0f0f0f0f\n")
            done, calls = self.run_auth(directory, ["--secret-file", str(secret)])
            result = json.loads(done.stdout.strip().splitlines()[-1])
            self.assertEqual(result["POST BEFORE"], "340 send article")
            # Not a bare `close` after the 340: the empty block terminates
            # the transfer the 340 opened, and the reply is recorded.
            first = calls.index(["cmd", "POST"])
            self.assertEqual(calls[first + 1], ["sendall", ".\r\n"])
            self.assertEqual(calls[first + 2], ["line", ""])
            self.assertEqual(result["POST BEFORE CLOSE"], "441 posting failed")


if __name__ == "__main__":
    unittest.main()
