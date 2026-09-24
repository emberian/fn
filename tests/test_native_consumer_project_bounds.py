"""Exact-file consumer projection rejects overbound inputs before allocation.

The fixture bytes are intentionally invalid.  ACL2 owns the cursor/event
limits and parsing; this test checks the native no-follow read and CLI outcome.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
ENABLED = os.environ.get("FN_RUN_CONSUMER_PROJECT_BOUNDS") == "1"


@unittest.skipUnless(ENABLED and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_RUN_CONSUMER_PROJECT_BOUNDS=1 and a qualified image")
class NativeConsumerProjectBoundsTests(unittest.TestCase):
    def test_overbound_cursor_and_event_refuse_without_projection(self):
        with tempfile.TemporaryDirectory(prefix="fn-consumer-project-bound-") as td:
            root = Path(td)
            cursor = root / "cursor.fncu"
            event = root / "event.fn-e"
            cases = ((b"\0" * 347, b"\0"),
                     (b"\0", b"\0" * 196609))
            for cursor_bytes, event_bytes in cases:
                with self.subTest(cursor=len(cursor_bytes), event=len(event_bytes)):
                    cursor.write_bytes(cursor_bytes)
                    event.write_bytes(event_bytes)
                    result = subprocess.run(
                        [str(IMAGE), "--fn", "consumer-project", str(cursor), str(event)],
                        cwd=ROOT, capture_output=True, timeout=30, check=False,
                        env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"})
                    self.assertEqual(result.returncode, 1, result.stderr)
                    self.assertEqual(result.stdout.strip(),
                                     b"fn-consumer-project-refused-v1 limit")

    def test_malformed_within_bound_uses_acl2_codec_refusal(self):
        with tempfile.TemporaryDirectory(prefix="fn-consumer-project-malformed-") as td:
            root = Path(td)
            cursor = root / "cursor.fncu"
            event = root / "event.fn-e"
            cursor.write_bytes(b"\0")
            event.write_bytes(b"\0")
            result = subprocess.run(
                [str(IMAGE), "--fn", "consumer-project", str(cursor), str(event)],
                cwd=ROOT, capture_output=True, timeout=30, check=False,
                env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"})
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(result.stdout.strip(),
                             b"fn-consumer-project-refused-v1 codec")


if __name__ == "__main__":
    unittest.main()
