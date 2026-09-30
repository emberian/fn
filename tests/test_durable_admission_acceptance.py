"""Real caller harness; missing current entry is a failure, never a skip.

The selected entry must be built/loaded from the assembly source manifest.
No recording callbacks, synthetic installed carriers or supplied demands.
"""
import os
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import uuid
from tests.native_harness import Node, EXIT

ROOT = Path(__file__).resolve().parents[1]


class DurableAdmissionAcceptance(unittest.TestCase):
    def test_real_post_and_restart(self):
        entry = os.environ.get("FN_DURABLE_ACCEPTANCE_ENTRY")
        self.assertTrue(entry and Path(entry).is_file(),
                        "MISSING-LOADING-INTERFACE: matched current real owner entry")
        manifest_path = os.environ.get("FN_DURABLE_ACCEPTANCE_MANIFEST")
        self.assertTrue(manifest_path, "MISSING-COORDINATE: actual entry/core/source manifest")
        manifest = json.loads(Path(manifest_path).read_text())
        inputs = manifest["inputs"]
        self.assertIn(str(Path(entry).resolve()), inputs)
        for name, digest in inputs.items():
            self.assertEqual(hashlib.sha256(Path(name).read_bytes()).hexdigest(), digest, name)
        base = ROOT / "build" / "acceptance-runs"
        base.mkdir(parents=True, exist_ok=True)
        scratch = Path(tempfile.mkdtemp(prefix="owned-", dir=base))
        # Keep failed fixtures/evidence; never accept an external Store path.
        (scratch / ".fn-acceptance-owned").write_text(uuid.uuid4().hex + "\n")
        self.assertEqual(scratch.parent.resolve(), base.resolve())
        node = Node(self, entry, root=scratch / "node")
        node.init("fn.test", expect=EXIT.OK)
        node.start(timeout=60)
        # Written by the actual internal read-only operation observation
        # boundary; ordinary successful legacy startup cannot satisfy this.
        observation = scratch / "node" / "admission-observation.json"
        self.assertTrue(observation.is_file(),
                        "MISSING-IMPLEMENTATION: genuine internal installed-operation observation")
        observed = json.loads(observation.read_text())
        self.assertEqual(observed["source_manifest_sha256"],
                         hashlib.sha256(Path(manifest_path).read_bytes()).hexdigest())
        self.assertEqual(observed["installation_status"], ":installed")
        self.assertTrue(observed["pool_association"])
        self.assertTrue(observed["initial_operation_receipt"])
        msgid = b"<durable-assembly-real-entry@example.invalid>"
        wire = (b"From: assembly@example.invalid\r\nNewsgroups: fn.test\r\n"
                b"Subject: real durable admission\r\nMessage-ID: " + msgid +
                b"\r\n\r\nretained input survives restart\r\n")
        with node.session(timeout=15) as client:
            first, final = client.post(wire)
            self.assertTrue(first.startswith(b"340 "), first)
            self.assertIsNotNone(final)
            self.assertTrue(final.startswith(b"240 "), final)
        node.stop(expect=EXIT.OK)
        node.start(timeout=60)
        with node.session(timeout=15) as client:
            restored = client.article(msgid)
            self.assertIsNotNone(restored, "accepted article absent after real restart")
            self.assertIn(b"retained input survives restart", restored)
        node.stop(expect=EXIT.OK)
        final_observed = json.loads(observation.read_text())
        self.assertTrue(final_observed["post_operation_receipt"])
        self.assertTrue(final_observed["restart_operation_receipt"])
        for name, digest in inputs.items():
            self.assertEqual(hashlib.sha256(Path(name).read_bytes()).hexdigest(), digest, name)


if __name__ == "__main__":
    unittest.main()
