"""Native execution-backend contract for tools/v0_matrix.py.

These tests do not stand in for a two-node native run. They pin the harness
boundary so that such a run cannot silently select a Python server, lose its
image/source labels, or label an unmeasured native feed as accepted.
"""
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import types
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
        # The 3f68944 dashboard, kept byte-identical when the first native
        # run replaced it as planning/v0-matrix.json.
        legacy = json.loads((ROOT / "planning/evidence/"
                             "v0-matrix-3f68944-2026-09-21.json").read_text())
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
        if name in ("node A init scratch configuration",
                    "node B init scratch configuration"):
            node = self.a if "node A" in name else self.b
            return "MATRIX-CONFIG-STORE {}/init/store".format(node.dir)
        if name in ("node A operator init", "node B operator init"):
            node = self.a if "node A" in name else self.b
            return "initialized {}/init/store".format(node.dir)
        if name == "native public peering/restart witness":
            return self.witness_output()
        if name == "native AUTHINFO secret":
            return "SECRET-READY"
        if name.startswith("start server"):
            return "LISTENING 11292"
        if name.endswith("principal list"):
            return "matrix principal=" + "c" * 64 + " posting=true"
        if name.endswith("lists its peers"):
            # Both records, so either node's phase finds the other's identity;
            # the phase matches the <path-identity>, not the node letter.
            return ("a path-identity=a.gate.example.invalid address=127.0.0.1 "
                    "port=11000 security=clear inbound=fn.* outbound=- "
                    "auth=source-address:127.0.0.1\n"
                    "b path-identity=b.gate.example.invalid address=127.0.0.1 "
                    "port=11001 security=clear inbound=fn.* outbound=- "
                    "auth=source-address:127.0.0.1")
        if name.endswith("recover the init scratch store"):
            return ("recovered transactions=1 articles=1 staging-orphans=0 "
                    "anchor=none checkpoint=none")
        if name.endswith("recover after the second init"):
            return ("recovered transactions=1 articles=1 staging-orphans=0 "
                    "anchor=none checkpoint=none")
        if name.endswith("configured store"):
            return "/srv/fn/a-store"
        if name.endswith("profile agent refusal"):
            return "usage operator run (UNSUPPORTED-PROFILE agent)"
        if name == "loopback refusal: run":
            return "usage operator request (CONFIGURATION INVALID)"
        if name.endswith("profile service log"):
            return ("accepted reader connection=0 time=2026-09-22T20:00:00Z\n"
                    "accepted post path=control message-id=<profile-a@example.invalid> "
                    "time=2026-09-22T20:00:01Z")
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
                 "offline group create while the owner holds the store": 1,
                 # A second `init` over a store that exists is refused, and
                 # the reinit-safety row is about what that refusal left.
                 "node A second operator init": 1,
                 # `[posting] agent` is refused at run admission, by name.
                 "node A profile agent refusal": v0_matrix.EXIT_USAGE,
                 "node B second operator init": 1}

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
        # FEED-ONCE belongs to the separate protected queue/restart witness.
        keys = gate.TRANSIT_KEYS + tuple(
            key for key in gate.FEED_KEYS if key != "V0-FEED-ONCE")
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
            # Without a developer image the cut that loses an outcome is
            # unreachable, and the row says which image it wanted.
            self.assertEqual(rows["V0-OUT-UNCERTAIN-A"].verdict, v0_matrix.NOT_BUILT)
            self.assertIn("--native-developer-image",
                          rows["V0-OUT-UNCERTAIN-A"].blocker)
            self.assertEqual(rows["V0-PEER-LIST-A"].verdict, v0_matrix.ACCEPTED)
            self.assertIn("peer list", rows["V0-PEER-LIST-A"].invocation)
            # The node is stood up, submitted to, recovered and refused a
            # second init, all through the public operator.
            self.assertEqual(rows["V0-NODE-INIT-A"].verdict, v0_matrix.ACCEPTED)
            self.assertIn("operator", rows["V0-NODE-INIT-A"].invocation)
            self.assertIn("init fn.letters", rows["V0-NODE-INIT-A"].invocation)
            self.assertEqual(rows["V0-NODE-REINIT-A"].verdict, v0_matrix.REFUSED)
            self.assertEqual(rows["V0-NODE-REINIT-SAFE-A"].verdict, v0_matrix.ACCEPTED)
            self.assertIn("articles=1", rows["V0-NODE-REINIT-SAFE-A"].observed)
            self.assertEqual(rows["V0-NODE-CONFIG-A"].verdict, v0_matrix.ACCEPTED)
            self.assertIn("/init/store", rows["V0-NODE-CONFIG-A"].observed)
            self.assertEqual(v0_matrix.PLAN_BY_KEY["V0-NODE-CONFIG"].requirements,
                             ("HST-003",))
            # The recovery row belongs to the phase with the better subject.
            order = [row.id for row in gate.rows]
            self.assertLess(order.index("V0-OUT-RECOVER-A"),
                            order.index("V0-NODE-STOP-A"))
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

    def test_native_config_row_needs_the_exact_store_path(self):
        class WrongStore(HarnessOnlyNativeGate):
            def canned(self, name):
                if name == "node A operator init":
                    return "initialized /some/other/store"
                return super().canned(name)

        with tempfile.TemporaryDirectory() as home:
            gate = WrongStore(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234",
                "dev", backend=v0_matrix.NATIVE_BACKEND,
                native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            self.assertEqual(rows["V0-NODE-CONFIG-A"].verdict,
                             v0_matrix.NOT_EXERCISED)
            self.assertIn("exact configured store path",
                          rows["V0-NODE-CONFIG-A"].blocker)
            self.assertEqual(rows["V0-NODE-CONFIG-B"].verdict, v0_matrix.ACCEPTED)

    def test_a_developer_image_makes_the_uncertain_outcome_a_measurement(self):
        """The one row the developer image is for, and the only thing it is for."""
        class DeveloperGate(HarnessOnlyNativeGate):
            CANNED_RC = dict(
                HarnessOnlyNativeGate.CANNED_RC,
                **{"node A submission to the init scratch owner":
                   v0_matrix.EXIT_UNCERTAIN,
                   "node B submission to the init scratch owner":
                   v0_matrix.EXIT_UNCERTAIN})

        with tempfile.TemporaryDirectory() as home:
            gate = DeveloperGate(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_developer_image="/opt/fn/fn-host-developer",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"},
                native_group="fn.letters")
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            row = rows["V0-OUT-UNCERTAIN-A"]
            self.assertEqual(row.verdict, v0_matrix.UNCERTAIN)
            self.assertEqual(row.exit_code, v0_matrix.EXIT_UNCERTAIN)
            self.assertIn("fn-native-control-status-exit-code", row.limit)
            # The owner carries the cut and the developer image; the client
            # that reports the outcome is the production one.
            owner = next(step for step in gate.steps
                         if step.name.startswith("start server")
                         and "init owner" in step.name
                         and "node A" in step.name)
            self.assertIn("FN_NATIVE_CONTROL_FAULT=postpublish", owner.command)
            self.assertIn("/opt/fn/fn-host-developer", owner.command)
            client = next(step for step in gate.steps
                          if step.name == "node A submission to the init scratch owner")
            self.assertIn("FN_NATIVE_HOST=/opt/fn/fn-host ", client.command)
            self.assertNotIn("fn-host-developer", client.command)
            self.assertNotIn("FN_NATIVE_CONTROL_FAULT", client.command)
            # The protected sent-cut witness also uses a developer source;
            # ordinary served clients and peer tests use production.
            for step in gate.steps:
                if "init owner" in step.name or step.name == "native protected peering witness":
                    continue
                self.assertNotIn("fn-host-developer", step.command, step.name)

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

    def test_an_owner_the_live_verb_killed_leaves_the_refusal_half_unexercised(self):
        # The dabebb84 run: the live verb exited 3 because the owner faulted
        # and exited, and the offline command then found the writer lock free
        # and was accepted.  With no live owner the refusal half is not a
        # statement about a held store, so the offline command is not run.
        class OwnerKilledByTheVerb(HarnessOnlyNativeGate):
            CANNED_RC = dict(HarnessOnlyNativeGate.CANNED_RC)
            CANNED_RC["live reconfiguration: declare fn.matrix.live on node A"] = 3

            def alive(self, node, tag="main"):
                if node.name == "a" and self.step_named(
                        "live reconfiguration: declare fn.matrix.live on node A"):
                    self.dead[node.name] = "fault operator run"
                    return False
                return bool(node.pid)
        with tempfile.TemporaryDirectory() as home:
            gate = OwnerKilledByTheVerb(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = {r.id: r for r in gate.rows}
            self.assertEqual(rows["V0-CFG-LIVE"].verdict, v0_matrix.UNCERTAIN)
            self.assertIn("DIED", rows["V0-CFG-LIVE"].observed)
            refuse = rows["V0-CFG-LIVE-REFUSE"]
            self.assertEqual(refuse.verdict, v0_matrix.NOT_EXERCISED)
            self.assertIn("owner died", refuse.blocker)
            self.assertNotIn("offline group create while the owner holds the store",
                             [step.name for step in gate.steps])

    def test_wildcard_listener_is_measured_and_its_usage_code_is_named(self):
        with tempfile.TemporaryDirectory() as home:
            gate = self.structured_gate(home)
            gate.execute_native_acceptance()
            row = {r.id: r for r in gate.rows}["V0-NODE-LOOPBACK"]
            # 5 is not one of the three outcomes, so the row is not-exercised
            # with the code named -- never a refusal read off a usage error.
            self.assertEqual(row.verdict, v0_matrix.NOT_EXERCISED)
            self.assertEqual(row.exit_code, v0_matrix.EXIT_USAGE)
            self.assertEqual(row.observed,
                             "rc=5 usage operator request (CONFIGURATION INVALID)")
            self.assertTrue(v0_matrix.expected_usage_matches(row.json("abc1234")))
            self.assertIn("exited 5", row.blocker)
            self.assertIn('host = "0.0.0.0"', row.invocation)
            self.assertIn("packaging/fn-native operator", row.invocation)
            self.assertIn("run", row.invocation)
            self.assertIn("configuration admission", row.limit)
            self.assertIn("non-loopback IPv4", row.limit)

    def profile_row(self, gate):
        gate.execute_native_acceptance()
        rows = [r for r in gate.rows if r.id == "V0-NODE-PROFILE"]
        self.assertEqual(len(rows), 1)
        return rows[0]

    def test_the_profile_row_measures_the_log_file_and_the_named_refusal(self):
        with tempfile.TemporaryDirectory() as home:
            row = self.profile_row(self.structured_gate(home))
            self.assertEqual(row.verdict, v0_matrix.ACCEPTED)
            # Both configurations are in the invocation: the reader must see
            # the `[log]` table and the refused `[posting] agent`.
            self.assertIn("[log]", row.invocation)
            self.assertIn("agent = ", row.invocation)
            self.assertIn("agent.toml", row.invocation)
            self.assertIn("packaging/fn-native operator", row.invocation)
            self.assertIn("post --message-id", row.invocation)
            self.assertIn("accepted post path=control "
                          "message-id=<profile-a@example.invalid>", row.observed)
            self.assertIn("UNSUPPORTED-PROFILE agent", row.observed)
            self.assertIn("path-identity", row.limit)

    def test_a_post_that_left_no_log_line_is_not_accepted(self):
        class Silent(HarnessOnlyNativeGate):
            def canned(self, name):
                if name.endswith("profile service log"):
                    return "NO-LOG-FILE"
                return super().canned(name)
        with tempfile.TemporaryDirectory() as home:
            row = self.profile_row(Silent(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"}))
            self.assertEqual(row.verdict, v0_matrix.REFUSED)
            self.assertIn("left no line", row.limit)

    def test_an_agent_the_run_accepts_is_not_accepted(self):
        class Silent(HarnessOnlyNativeGate):
            CANNED_RC = {k: v for k, v in HarnessOnlyNativeGate.CANNED_RC.items()
                         if k != "node A profile agent refusal"}
        with tempfile.TemporaryDirectory() as home:
            row = self.profile_row(Silent(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"}))
            self.assertEqual(row.verdict, v0_matrix.REFUSED)
            self.assertIn("did not refuse `[posting] agent`", row.limit)

    def test_a_failed_post_leaves_the_row_not_exercised_with_its_code(self):
        class Failed(HarnessOnlyNativeGate):
            CANNED_RC = dict(HarnessOnlyNativeGate.CANNED_RC,
                             **{"node A profile post": 4})
        with tempfile.TemporaryDirectory() as home:
            row = self.profile_row(Failed(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"}))
            self.assertEqual(row.verdict, v0_matrix.NOT_EXERCISED)
            self.assertIn("exited 4", row.blocker)

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

    def test_a_config_that_does_not_open_names_the_credential_rows_reason(self):
        class UnopenableConfig(HarnessOnlyNativeGate):
            def native_config_status(self, node):
                if node.name == "b":
                    self.emit("V0-NODE-STATUS", v0_matrix.UNCERTAIN,
                              self.native_operator(node, "status"),
                              "uncertain operator status", node=node.name,
                              exit_code=3, client=v0_matrix.CLIENT_CLI)
                    return False
                return super().native_config_status(node)
        with tempfile.TemporaryDirectory() as home:
            gate = UnopenableConfig(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND, native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            for rid in ("V0-AUTH-PASSWORD-B", "V0-AUTH-LIST-B", "V0-AUTH-GATED-B"):
                self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED, rid)
                self.assertIn("did not open cleanly", rows[rid].blocker, rid)
            # Node A is unaffected: one node's configuration is not the other's.
            self.assertEqual(rows["V0-AUTH-PASSWORD-A"].verdict, v0_matrix.ACCEPTED)

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


class RelayedArticleTests(unittest.TestCase):
    """V0-TRANSIT-IDENTICAL against fn-peer-relayed-octets (specs/peering.md 2.3).

    Since 9a659682 the target serves the source's article with its own
    <path-identity>, a section 3.2.1 diagnostic and "!" prepended to Path and
    every Xref removed; the row checks exactly that and names what else moved.
    """

    ID, EXPECTED = "b.gate.example.invalid", "a.gate.example.invalid"
    POSTED = ("Path: a.gate.example.invalid!not-for-mail\r\n"
              "From: gate@example.invalid\r\n"
              "Subject: outcome, written on A\r\n"
              "Newsgroups: fn.letters\r\n"
              "Date: Wed, 23 Sep 2026 02:47:25 +0000\r\n"
              "Message-ID: <alpha@a.example.invalid>\r\n"
              "Xref: a.gate.example.invalid fn.letters:1\r\n"
              "\r\n"
              "The first line of the body.\r\n"
              "The second line of the body.\r\n")
    RELAYED = (POSTED.replace("Path: a.gate", "Path: b.gate.example.invalid!!a.gate")
               .replace("Xref: a.gate.example.invalid fn.letters:1\r\n", ""))

    def differences(self, served, sent=None, expected=EXPECTED):
        return v0_matrix.relayed_article_differences(
            sent if sent is not None else self.POSTED, served, self.ID, expected)

    def test_identical_modulo_the_prepend_and_the_xref_removal_passes(self):
        self.assertEqual(self.differences(self.RELAYED), [])
        self.assertEqual(self.differences(self.RELAYED.encode()), [])
        self.assertEqual(v0_matrix.relayed_article_differences(
            self.POSTED.split("\r\n")[:-1], self.RELAYED.split("\r\n")[:-1],
            self.ID, self.EXPECTED), [])

    def test_the_mismatch_diagnostic_must_name_the_expected_source(self):
        mismatch = self.RELAYED.replace(
            "b.gate.example.invalid!!", "b.gate.example.invalid!.MISMATCH."
            "a.gate.example.invalid!")
        self.assertEqual(self.differences(mismatch), [])
        wrong = mismatch.replace(".MISMATCH.a.gate", ".MISMATCH.c.gate")
        found = self.differences(wrong)
        self.assertEqual(len(found), 1)
        self.assertIn(".MISMATCH.c.gate", found[0])

    def test_a_changed_body_fails_naming_the_line(self):
        found = self.differences(self.RELAYED.replace("second line", "2nd line"))
        self.assertIn("only posted: 'The second line of the body.'", found)
        self.assertIn("only served: 'The 2nd line of the body.'", found)
        self.assertEqual(len(found), 2)

    def test_a_changed_other_header_fails_naming_the_line(self):
        found = self.differences(self.RELAYED.replace("Subject: outcome",
                                                      "Subject: Outcome"))
        self.assertEqual(found, ["only posted: 'Subject: outcome, written on A'",
                                 "only served: 'Subject: Outcome, written on A'"])

    def test_a_surviving_xref_fails(self):
        survived = self.RELAYED.replace(
            "\r\n\r\n", "\r\nXref: a.gate.example.invalid fn.letters:1\r\n\r\n", 1)
        self.assertEqual(self.differences(survived),
                         ["Xref survived: 'Xref: a.gate.example.invalid fn.letters:1'"])
        folded = self.RELAYED.replace(
            "\r\n\r\n", "\r\nxref: a.gate.example.invalid\r\n fn.letters:1\r\n\r\n", 1)
        self.assertEqual(self.differences(folded),
                         ["Xref survived: 'xref: a.gate.example.invalid'"])

    def test_a_path_without_the_identity_fails(self):
        # The byte-identical article the row expected before 9a659682.
        found = self.differences(self.POSTED.replace(
            "Xref: a.gate.example.invalid fn.letters:1\r\n", ""))
        self.assertEqual(len(found), 1)
        self.assertIn("Path is not the posted Path with b.gate.example.invalid!!", found[0])
        self.assertIn("'Path: a.gate.example.invalid!not-for-mail'", found[0])
        other = self.RELAYED.replace("Path: b.gate.example.invalid!!",
                                     "Path: c.gate.example.invalid!!")
        self.assertEqual(len(self.differences(other)), 1)

    def test_a_path_that_already_names_the_node_is_left_alone(self):
        sent = self.RELAYED
        self.assertEqual(self.differences(sent, sent=sent), [])
        twice = sent.replace("Path: b.gate.example.invalid!!",
                             "Path: b.gate.example.invalid!!b.gate.example.invalid!!")
        self.assertEqual(len(self.differences(twice, sent=sent)), 1)

    def test_an_article_with_no_path_gets_none(self):
        sent = self.POSTED.replace("Path: a.gate.example.invalid!not-for-mail\r\n", "")
        served = self.RELAYED.replace(
            "Path: b.gate.example.invalid!!a.gate.example.invalid!not-for-mail\r\n", "")
        self.assertEqual(self.differences(served, sent=sent), [])
        found = self.differences(self.RELAYED, sent=sent)
        self.assertEqual(len(found), 1)
        self.assertIn("posted 0 Path field(s), served 1", found[0])

    def test_the_row_names_the_differing_lines(self):
        with tempfile.TemporaryDirectory() as home:
            gate = native_gate(home)
            lines = self.POSTED.split("\r\n")[:-1]
            relayed = self.RELAYED.split("\r\n")[:-1]
            gate.transit_identical(
                {"reread": "220 0 <alpha@a.example.invalid> article follows",
                 "sent_lines": lines, "reread_lines": relayed},
                gate.a, gate.b, "ab", "feed.py relay")
            broken = [line.replace("second", "2nd") for line in relayed]
            gate.transit_identical(
                {"reread": "220 0 <beta@b.example.invalid> article follows",
                 "sent_lines": [line.replace("a.gate", "b.gate", 1) if line.startswith("Path")
                                else line for line in lines],
                 "reread_lines": broken},
                gate.b, gate.a, "ba", "feed.py relay")
        rows = {row.json("", None)["id"]: row.json("", None) for row in gate.rows}
        ab, ba = rows["V0-TRANSIT-IDENTICAL-AB"], rows["V0-TRANSIT-IDENTICAL-BA"]
        self.assertEqual(ab["verdict"], v0_matrix.ACCEPTED)
        self.assertIn("b.gate.example.invalid!!a.gate", ab["observed"])
        self.assertEqual(ba["verdict"], v0_matrix.REFUSED)
        self.assertIn("The 2nd line of the body.", ba["observed"])
        self.assertIn("Path is not the posted Path with a.gate.example.invalid!!",
                      ba["observed"])

    def test_the_relay_driver_reports_both_sides(self):
        source = v0_matrix.V0Matrix.feed_driver()
        self.assertIn('out["sent_lines"] = lines', source)
        self.assertIn('out["reread_lines"] = got', source)
        compile(source, "feed.py", "exec")


class ProtectedTransitTests(unittest.TestCase):
    """The owner's feed over STARTTLS and AUTHINFO (PRF-047, PRF-051; T9c).

    These pin the planning and the mapping of the protected rows.  No image
    runs here, so the only measured verdicts below come from canned witness
    lines; the first test is what a run without an image records.
    """

    IDS = ("V0-TRANSIT-TLS-AB", "V0-TRANSIT-TLS-BA", "V0-TRANSIT-AUTHINFO-AB",
           "V0-TRANSIT-AUTHINFO-BA", "V0-TRANSIT-TLS-WRONG-ANCHOR",
           "V0-TRANSIT-AUTHINFO-WRONG")

    @staticmethod
    def identity(core="b" * 64):
        one = {"status": "observed", "runtime_sha256": "a" * 64, "core_sha256": core}
        return {"a": dict(one), "b": dict(one)}

    @classmethod
    def witness_lines(cls, alter=None):
        feed = {"kind": "protected-feed", "security": "starttls", "auth": "authinfo",
                "target_policy": {"required": True, "protected_only": True},
                "transit": {"ab": {"identical": True,
                                   "unauthenticated_offer": "502 transit is not permitted"},
                            "ba": {"identical": True,
                                   "unauthenticated_offer": "502 transit is not permitted"}},
                "reconnect": {"ab": {"identical": True}, "ba": {"identical": True}},
                "identity": cls.identity()}
        password = {"kind": "protected-refusal", "case": "wrong-password",
                    "delivered": False, "source_alive": True, "target_alive": True,
                    "identity": cls.identity()}
        anchor = {"kind": "protected-refusal", "case": "wrong-anchor",
                  "delivered": False, "journal": True, "source_alive": True,
                  "target_alive": True, "identity": cls.identity()}
        if alter:
            alter(feed, password, anchor)
        return "\n".join(["NATIVE-PROTECTED-EXPECTED-RUNTIME " + "a" * 64,
                          "NATIVE-PROTECTED-EXPECTED-CORE " + "b" * 64]
                         + ["NATIVE-PROTECTED-WITNESS " + json.dumps(one)
                            for one in (feed, password, anchor)])

    def gate(self, home, output=None):
        class Protected(HarnessOnlyNativeGate):
            def canned(self, name):
                if name == "native protected peering witness" and output is not None:
                    return output
                return super().canned(name)
        return Protected(v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234",
                         "dev", backend=v0_matrix.NATIVE_BACKEND,
                         native_image="/opt/fn/fn-host",
                         native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})

    def rows(self, output=None):
        with tempfile.TemporaryDirectory() as home:
            gate = self.gate(home, output)
            gate.execute_native_acceptance()
            return {row.id: row for row in gate.rows}

    def test_the_rows_are_planned_per_direction_with_the_refusals_single(self):
        planned = set(v0_matrix.PLANNED_IDS)
        for rid in self.IDS:
            self.assertIn(rid, planned)
        self.assertEqual(v0_matrix.PLAN_BY_KEY["V0-TRANSIT-TLS"].expected,
                         v0_matrix.ACCEPTED)
        self.assertEqual(v0_matrix.PLAN_BY_KEY["V0-TRANSIT-AUTHINFO-WRONG"].expected,
                         v0_matrix.REFUSED)

    def test_without_an_image_every_protected_row_is_not_exercised_with_a_blocker(self):
        rows = self.rows()
        for rid in self.IDS:
            self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED, rid)
            self.assertIn("protected peering witness", rows[rid].blocker, rid)
            self.assertIn("test_native_protected_peering", rows[rid].invocation, rid)

    def test_a_structured_witness_measures_both_directions_and_both_refusals(self):
        rows = self.rows(self.witness_lines())
        for rid in self.IDS[:4]:
            self.assertEqual(rows[rid].verdict, v0_matrix.ACCEPTED, rid)
            self.assertIn("502", rows[rid].observed, rid)
        for rid in self.IDS[4:]:
            self.assertEqual(rows[rid].verdict, v0_matrix.REFUSED, rid)
        self.assertIn("test_reciprocal_starttls_authinfo_transfer_and_reconnect",
                      rows["V0-TRANSIT-TLS-AB"].invocation)

    def test_witnesses_after_a_unittest_verbose_prefix_are_read(self):
        # `unittest -v` prints `test_x (...) ... ` and no newline before the
        # body runs; the 1a9dd747 run lost both refusals and FEED-ONCE to it.
        lines = self.witness_lines().splitlines()
        prefixed = "\n".join(
            line if not line.startswith("NATIVE-PROTECTED-WITNESS ") or index == 2
            else "test_case_{} (tests.x.Y.test_case_{}) ... {}".format(index, index, line)
            for index, line in enumerate(lines))
        self.assertNotEqual(prefixed, "\n".join(lines))
        rows = self.rows(prefixed)
        for rid in self.IDS[4:]:
            self.assertEqual(rows[rid].verdict, v0_matrix.REFUSED, rid)

    def test_owners_that_are_not_this_image_are_not_evidence(self):
        def alter(feed, password, anchor):
            for one in (feed, password, anchor):
                one["identity"] = self.identity(core="c" * 64)
        rows = self.rows(self.witness_lines(alter))
        for rid in self.IDS:
            self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED, rid)
            self.assertIn("this run's image", rows[rid].blocker, rid)

    def test_a_target_that_does_not_refuse_the_clear_channel_is_not_evidence(self):
        def alter(feed, password, anchor):
            feed["target_policy"] = {"required": True, "protected_only": False}
        rows = self.rows(self.witness_lines(alter))
        for rid in self.IDS[:4]:
            self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED, rid)
            self.assertIn("refuses both without them", rows[rid].blocker, rid)

    def test_a_direction_whose_clear_offer_was_taken_is_not_measured(self):
        def alter(feed, password, anchor):
            feed["transit"]["ba"]["unauthenticated_offer"] = "335 send it"
        rows = self.rows(self.witness_lines(alter))
        self.assertEqual(rows["V0-TRANSIT-TLS-AB"].verdict, v0_matrix.ACCEPTED)
        self.assertEqual(rows["V0-TRANSIT-AUTHINFO-AB"].verdict, v0_matrix.ACCEPTED)
        self.assertEqual(rows["V0-TRANSIT-TLS-BA"].verdict, v0_matrix.NOT_EXERCISED)
        self.assertEqual(rows["V0-TRANSIT-AUTHINFO-BA"].verdict, v0_matrix.NOT_EXERCISED)
        self.assertIn("malformed protected-feed ba", rows["V0-TRANSIT-TLS-BA"].blocker)

    def test_a_delivered_refusal_case_is_not_read_as_a_refusal(self):
        def alter(feed, password, anchor):
            password["delivered"] = True
        rows = self.rows(self.witness_lines(alter))
        self.assertEqual(rows["V0-TRANSIT-AUTHINFO-WRONG"].verdict,
                         v0_matrix.NOT_EXERCISED)
        self.assertEqual(rows["V0-TRANSIT-TLS-WRONG-ANCHOR"].verdict, v0_matrix.REFUSED)

    def test_feed_once_needs_replayed_done_and_no_new_offer_after_restart(self):
        base = self.witness_lines()
        one = {"kind": "feed-once", "security": "starttls", "auth": "authinfo",
               "source_killed": True, "source_restarted": True,
               "recipient_articles": 1, "identity": self.identity(),
               "before": {"state_before_restart": "done",
                          "state_after_restart": "done",
                          "records": {"feed-offer": 1, "feed-sent": 1,
                                      "feed-outcome": 1}},
               "after": {"state_after_restart": "done",
                         "records": {"feed-offer": 1, "feed-sent": 1,
                                     "feed-outcome": 1}}}
        cut = {"kind": "feed-sent-restart", "security": "starttls",
               "auth": "authinfo", "sender_stopped_after_sent": True,
               "sender_killed": True, "sender_restarted": True,
               "recipient_articles": 1, "identity": self.identity(),
               "developer_identity": {"status": "observed",
                                      "runtime_sha256": "a" * 64,
                                      "core_sha256": "c" * 64},
               "interrupted": {"sent_before_restart": "t",
                               "state_after_restart": "queued",
                               "records": {"feed-offer": 1, "feed-sent": 1}},
               "settled": {"state_after_restart": "done",
                           "records": {"feed-offer": 2, "feed-sent": 2,
                                       "feed-outcome": 1}}}
        marker = "NATIVE-PROTECTED-EXPECTED-DEVELOPER-CORE " + "c" * 64
        rows = self.rows(base + "\nNATIVE-PROTECTED-WITNESS " + json.dumps(one))
        self.assertEqual(rows["V0-FEED-ONCE"].verdict, v0_matrix.NOT_EXERCISED)
        self.assertIn("acknowledged and durable-sent", rows["V0-FEED-ONCE"].blocker)
        lines = (base + "\n" + marker + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(one) + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(cut))
        rows = self.rows(lines)
        self.assertEqual(rows["V0-FEED-ONCE"].verdict, v0_matrix.ACCEPTED)
        cut["settled"]["records"]["feed-offer"] = 1
        lines = (base + "\n" + marker + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(one) + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(cut))
        rows = self.rows(lines)
        self.assertEqual(rows["V0-FEED-ONCE"].verdict, v0_matrix.NOT_EXERCISED)
        cut["settled"]["records"]["feed-offer"] = 2
        one["after"]["records"]["feed-offer"] = 2
        lines = (base + "\n" + marker + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(one) + "\n"
                 + "NATIVE-PROTECTED-WITNESS " + json.dumps(cut))
        rows = self.rows(lines)
        self.assertEqual(rows["V0-FEED-ONCE"].verdict, v0_matrix.NOT_EXERCISED)
        self.assertIn("settled owner queue", rows["V0-FEED-ONCE"].blocker)

    def test_failed_protected_suite_cannot_turn_earlier_witnesses_green(self):
        class FailedSuite(HarnessOnlyNativeGate):
            def sh(self, name, script, timeout=600, note="", expect=0):
                step = super().sh(name, script, timeout, note, expect)
                if name == "native protected peering witness":
                    step.rc = 1
                return step

        with tempfile.TemporaryDirectory() as home:
            gate = FailedSuite(v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40,
                               "abc1234", "dev", backend=v0_matrix.NATIVE_BACKEND,
                               native_image="/opt/fn/fn-host",
                               native_configs={"a": "/srv/fn/a.toml",
                                               "b": "/srv/fn/b.toml"})
            gate.witness_output = lambda: self.witness_lines()
            gate.execute_native_acceptance()
            rows = {row.id: row for row in gate.rows}
            for rid in self.IDS + ("V0-FEED-ONCE",):
                self.assertEqual(rows[rid].verdict, v0_matrix.NOT_EXERCISED)
                self.assertIn("did not finish cleanly", rows[rid].blocker)


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


class TickingClock:
    """A clock that never gives the same second twice."""

    def __init__(self):
        self.reads = 0

    def now(self, tz=None):
        self.reads += 1
        return dt.datetime(2026, 9, 22, 3, 8, self.reads, tzinfo=tz)


class RecordingGate(HarnessOnlyNativeGate):
    """Keeps every octet the gate would have installed on the node."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.pushed = []

    def push_file(self, content, remote, mode="644"):
        if isinstance(content, str):
            content = content.encode()
        self.pushed.append((remote, content))


class DuplicateOutcomeTests(unittest.TestCase):
    """The octets decide the word, so the harness must hold them fixed.

    The two native runs of 2026-09-22 read `V0-OUT-REFUSED` as refused on one
    node and accepted-as-duplicate on the other, and swapped on the rerun.
    The node was not the variable: `article()` re-stamped `Date` from the
    clock on every call, so the second submission of one Message-ID crossed a
    second boundary about half the time and stopped being a resubmission.
    """

    def setUp(self):
        v0_matrix.ARTICLE_STAMPS.clear()
        self.clock = v0_matrix.dt
        self.temporary = tempfile.TemporaryDirectory()

    def tearDown(self):
        v0_matrix.dt = self.clock
        v0_matrix.ARTICLE_STAMPS.clear()
        self.temporary.cleanup()

    def tick(self):
        clock = TickingClock()
        v0_matrix.dt = types.SimpleNamespace(datetime=clock, timezone=dt.timezone)
        return clock

    def test_one_message_id_keeps_one_date_across_a_second_boundary(self):
        clock = self.tick()
        first = v0_matrix.article("<x@example.invalid>", "fn.letters", "s", "b")
        second = v0_matrix.article("<x@example.invalid>", "fn.letters", "s", "b")
        self.assertEqual(first, second)
        self.assertEqual(clock.reads, 1)
        self.assertIn(b"Date: Tue, 22 Sep 2026 03:08:01 +0000", first)

    def test_a_different_message_id_still_gets_its_own_date(self):
        clock = self.tick()
        one = v0_matrix.article("<x@example.invalid>", "fn.letters", "s", "b")
        two = v0_matrix.article("<y@example.invalid>", "fn.letters", "s", "b")
        self.assertNotEqual(one, two)
        self.assertEqual(clock.reads, 2)

    def gate(self):
        return RecordingGate(
            v0_matrix.LocalHost(Path(self.temporary.name)), ROOT, "a" * 40,
            "abc1234", "dev", backend=v0_matrix.NATIVE_BACKEND,
            native_image="/opt/fn/fn-host",
            native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"},
            native_group="fn.letters")

    def test_the_resubmission_row_submits_the_octets_the_node_holds(self):
        self.tick()
        gate = self.gate()
        gate.native_outcomes(gate.a)
        posts = [(path, blob) for path, blob in gate.pushed
                 if path.endswith(".article")]
        self.assertEqual(len(posts), 3)
        (first_path, first), (again_path, again), (other_path, other) = posts
        # The idempotent duplicate is the SAME octets, not merely the same
        # Message-ID: this is the assertion the two 2026-09-22 runs failed.
        self.assertEqual(first, again)
        self.assertEqual(first_path, again_path)
        # The refusal is a real conflict: one Message-ID, different octets,
        # and its own file, so it never overwrites the accepted article.
        msgid = v0_matrix.ART["a"].encode()
        self.assertIn(msgid, first)
        self.assertIn(msgid, other)
        self.assertNotEqual(first, other)
        self.assertNotEqual(first_path, other_path)
        self.assertIn("conflict", other_path)

    def test_the_refusal_row_names_the_octets_and_the_duplicate_is_recorded(self):
        self.tick()
        gate = self.gate()
        gate.native_outcomes(gate.a)
        row = [r for r in gate.rows if r.id == "V0-OUT-REFUSED-A"][0]
        self.assertIn("DIFFERENT octets", row.limit)
        self.assertNotIn("the same submission a second time", row.limit)
        self.assertIn("conflict", row.invocation)
        fact = gate.facts["duplicate resubmission a"]
        self.assertIn("identical octets", fact)
        self.assertIn("different octets under the same Message-ID", fact)


class InnRowTests(unittest.TestCase):
    """The INN rows are read from tools/inn_lab.py's findings and nothing else."""

    @staticmethod
    def findings(overrides=None, verdict="held"):
        rows = []
        for _, names in v0_matrix.INN_ROWS:
            for name in names:
                key, _, instance = name.partition("[")
                rows.append({"key": key, "instance": instance.rstrip("]"),
                             "verdict": "held", "observed": "obs " + name})
        for row in rows:
            name = row["key"] + ("[{}]".format(row["instance"]) if row["instance"] else "")
            if overrides and name in overrides:
                row["verdict"] = overrides[name]
        return {"verdict": verdict, "counts": {"held": len(rows)}, "rows": rows}

    def test_every_inn_row_is_planned_and_every_lab_finding_is_named_once(self):
        for key in v0_matrix.INN_ROW_KEYS:
            self.assertIn(key, v0_matrix.PLANNED_IDS)
        names = [name for _, names in v0_matrix.INN_ROWS for name in names]
        self.assertEqual(len(names), len(set(names)))
        import inn_lab
        declared = {key + ("[{}]".format(one) if one else "")
                    for key, (_, instances) in inn_lab.InnLab.ASSERTIONS.items()
                    for one in instances}
        self.assertLessEqual(set(names), declared,
                             "a row reads a finding the lab never declares")

    def test_all_held_carries_each_row_s_expected_verdict(self):
        got = {key: (verdict, blocker) for key, verdict, _, blocker in
               v0_matrix.inn_rows(self.findings())}
        self.assertEqual(set(got), set(v0_matrix.INN_ROW_KEYS))
        for key in v0_matrix.INN_ROW_KEYS:
            self.assertEqual(got[key][0], v0_matrix.PLAN_BY_KEY[key].expected, key)
            self.assertIsNone(got[key][1])

    def test_a_violated_finding_is_the_opposite_outcome_not_a_pass(self):
        got = {key: verdict for key, verdict, _, _ in v0_matrix.inn_rows(self.findings(
            {"fn-serves-no-sender-xref": "violated", "fn-loop-refused": "violated"},
            verdict="violated"))}
        self.assertEqual(got["V0-INN-SERVING-AGENT"], v0_matrix.REFUSED)
        self.assertEqual(got["V0-INN-LOOP-FN"], v0_matrix.ACCEPTED)
        self.assertEqual(got["V0-INN-INTEROP"], v0_matrix.REFUSED)
        self.assertEqual(got["V0-INN-FEED-OUT"], v0_matrix.ACCEPTED)

    def test_an_undecided_or_absent_finding_is_not_exercised_with_its_reason(self):
        doc = self.findings({"innd-died": "not-exercised"}, verdict="inconclusive")
        doc["rows"] = [row for row in doc["rows"] if row["key"] != "fn-feeds-inn"]
        got = {key: (verdict, blocker) for key, verdict, _, blocker in
               v0_matrix.inn_rows(doc)}
        self.assertEqual(got["V0-INN-RESTART"][0], v0_matrix.NOT_EXERCISED)
        self.assertIn("innd-died=not-exercised", got["V0-INN-RESTART"][1])
        self.assertEqual(got["V0-INN-FEED-OUT"][0], v0_matrix.NOT_EXERCISED)
        self.assertIn("fn-feeds-inn=absent", got["V0-INN-FEED-OUT"][1])
        self.assertEqual(got["V0-INN-INTEROP"][0], v0_matrix.NOT_EXERCISED)

    def test_without_inn_or_off_the_native_backend_every_row_says_why(self):
        with tempfile.TemporaryDirectory() as home:
            gate = native_gate(home)
            gate.inn()
            rows = {row.id: row for row in gate.rows}
            self.assertEqual(set(rows), set(v0_matrix.INN_ROW_KEYS))
            for row in rows.values():
                self.assertEqual(row.verdict, v0_matrix.NOT_EXERCISED)
                self.assertIn("--inn", row.blocker)
            gate = native_gate(home)
            gate.want_inn = True
            gate.backend = v0_matrix.DEVELOPMENT_BACKEND
            gate.inn()
            for row in gate.rows:
                self.assertIn("D07", row.blocker)

    def test_the_lab_is_run_from_this_checkout_with_the_image(self):
        with tempfile.TemporaryDirectory() as home:
            gate = native_gate(home)
            command = gate.inn_command(Path("/tmp/x/inn-lab.md"))
            self.assertEqual(command[1], str(ROOT / "tools/inn_lab.py"))
            self.assertEqual(command[command.index("--native-image") + 1],
                             "/opt/fn/fn-host")
            self.assertEqual(command[command.index("--host") + 1], gate.host.label)
            self.assertEqual(command[-1], "/tmp/x/inn-lab.md")
            self.assertNotIn("--native-openssl-prefix", command)
            gate.native_openssl_prefix = "/tank/fn/OpenSSL 3.5.8"
            command = gate.inn_command(Path("/tmp/x/inn-lab.md"))
            self.assertEqual(command[command.index("--native-openssl-prefix") + 1],
                             "/tank/fn/OpenSSL 3.5.8")


class FromMailboxTests(unittest.TestCase):
    """V0-POST-FROM-MAILBOX: RFC 5536 3.1.2, the agents run's `From: yue`.

    The postcycle phase posts an unaddressed From on its own connection under
    a Message-ID of its own and asks for it back; the verdict is refused only
    when the POST was answered 441 AND the Message-ID is not served.
    """

    FAKE_DRIVER = r"""
import json, os

def note(kind, value=""):
    with open(os.environ["POST_LOG"], "a", encoding="utf-8") as out:
        out.write(json.dumps([kind, value]) + "\n")

class Sock:
    def __init__(self, conn):
        self.conn = conn
    def sendall(self, payload):
        text = payload.decode("ascii")
        self.conn.last = text
        note("sendall", text)
    def close(self):
        note("close")

class Conn:
    def __init__(self, port, timeout=30):
        self.sock = Sock(self)
        self.greeting = "200 ready"
        self.last = ""
    def cmd(self, text, multiline=False):
        note("cmd", text)
        if text == "POST":
            return "340 send article", []
        if text.startswith("GROUP"):
            return "211 1 1 1 fn.letters", []
        if text.startswith("STAT"):
            return "430 no article with that message-id", []
        if text.startswith("ARTICLE"):
            return "220 0 <m@example.invalid> article follows", []
        if text == "DATE":
            return "111 20260922212647", []
        return "500 command not recognized", []
    def line(self):
        if "From: yue" in self.last:
            return "441 posting failed; From is not a valid mailbox list"
        return "240 article received OK"
    def close(self):
        self.sock.close()
"""

    def run_post(self, directory):
        (directory / "drive.py").write_text(self.FAKE_DRIVER)
        (directory / "matrix.py").write_text(v0_matrix.MATRIX_DRIVER)
        log = directory / "post.log"
        done = subprocess.run(
            [sys.executable, "matrix.py", "postcycle", "--port", "1",
             "--group", "fn.letters", "--msgid", "<m@example.invalid>",
             "--user", "", "--secret", ""],
            cwd=directory, env=dict(os.environ, POST_LOG=str(log)), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        return done, calls

    def test_the_unaddressed_post_is_its_own_article_and_is_asked_for(self):
        with tempfile.TemporaryDirectory() as name:
            done, calls = self.run_post(Path(name))
            self.assertEqual(done.returncode, 0, done.stderr + done.stdout)
            result = json.loads(done.stdout.strip().splitlines()[-1])
            self.assertTrue(result["COMMIT"].startswith("240"))
            self.assertEqual(result["FROM"],
                             "441 posting failed; From is not a valid mailbox list")
            self.assertTrue(result["FROM ARTICLE"].startswith("430"))
            blocks = [value for kind, value in calls
                      if kind == "sendall" and "From: yue" in value]
            self.assertEqual(len(blocks), 1)
            self.assertIn("Message-ID: <m.from@example.invalid>\r\n", blocks[0])
            self.assertIn(["cmd", "STAT <m.from@example.invalid>"], calls)
            self.assertEqual(v0_matrix.from_mailbox_verdict(result["FROM"],
                                                             result["FROM ARTICLE"]),
                             v0_matrix.REFUSED)

    def test_the_verdict_needs_both_the_refusal_and_the_absence(self):
        verdict = v0_matrix.from_mailbox_verdict
        self.assertEqual(verdict("441 posting failed", "430 no such article"),
                         v0_matrix.REFUSED)
        # The defect: taken, or served.
        self.assertEqual(verdict("240 article received OK", "223 0 <m>"),
                         v0_matrix.ACCEPTED)
        self.assertEqual(verdict("441 posting failed", "223 0 <m>"),
                         v0_matrix.ACCEPTED)
        # No answer is no decision.
        self.assertEqual(verdict("", ""), v0_matrix.UNCERTAIN)
        self.assertEqual(v0_matrix.PLAN_BY_KEY["V0-POST-FROM-MAILBOX"].expected,
                         v0_matrix.REFUSED)


if __name__ == "__main__":
    unittest.main()
