"""Native execution-backend contract for tools/v0_matrix.py.

These tests do not stand in for a two-node native run.  They pin the harness
boundary so that such a run cannot silently select a Python server, lose its
image/source labels, or report the currently inactive feed as exercised.
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
            "FN_NATIVE_HOST=/opt/fn/fn-host packaging/fn-native operator "
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
            "FN_NATIVE_HOST=/opt/fn/fn-host packaging/fn-native operator "
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

    def sh(self, name, script, timeout=600, note="", expect=0):
        step = Step(name, script, 0, "", 0.0, note, expect)
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


class NativeSliceAccountingTests(unittest.TestCase):
    def test_first_slice_never_claims_the_inactive_feed(self):
        with tempfile.TemporaryDirectory() as home:
            gate = HarnessOnlyNativeGate(
                v0_matrix.LocalHost(Path(home)), ROOT, "a" * 40, "abc1234", "dev",
                backend=v0_matrix.NATIVE_BACKEND,
                native_image="/opt/fn/fn-host",
                native_configs={"a": "/srv/fn/a.toml", "b": "/srv/fn/b.toml"})
            gate.execute_native_acceptance()
            feed = [row for row in gate.rows if row.id.startswith("V0-FEED-")]
            self.assertEqual(len(feed), len(gate.FEED_KEYS))
            self.assertTrue(all(row.verdict == v0_matrix.NOT_BUILT for row in feed))
            self.assertTrue(all(row.owner == "native outbound feed activation"
                                for row in feed))
            starts = [row for row in gate.rows if row.id.startswith("V0-NODE-START-")]
            self.assertEqual({row.node for row in starts}, {"a", "b"})
            self.assertTrue(all("packaging/fn-native operator" in row.invocation
                                for row in starts))


if __name__ == "__main__":
    unittest.main()
