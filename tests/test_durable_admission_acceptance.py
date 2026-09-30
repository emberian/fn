"""Real caller harness; missing current entry is a failure, never a skip.

The selected entry must be built/loaded from the assembly source manifest.
No recording callbacks, synthetic installed carriers or supplied demands.
"""
import os
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
        base = ROOT / "build" / "acceptance-runs"
        base.mkdir(parents=True, exist_ok=True)
        scratch = Path(tempfile.mkdtemp(prefix="owned-", dir=base))
        # Keep failed fixtures/evidence; never accept an external Store path.
        (scratch / ".fn-acceptance-owned").write_text(uuid.uuid4().hex + "\n")
        self.assertEqual(scratch.parent.resolve(), base.resolve())
        node = Node(self, entry, root=scratch / "node")
        node.init("fn.test", expect=EXIT.OK)
        node.start(timeout=60)
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


if __name__ == "__main__":
    unittest.main()
