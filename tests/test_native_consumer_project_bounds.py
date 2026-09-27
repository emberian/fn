"""Exact-file consumer projection rejects overbound inputs before allocation.

The fixture bytes are intentionally invalid.  ACL2 owns the cursor/event
limits and parsing; this test checks the native no-follow read and CLI outcome.
The two ceilings are ASKED of the image (`consumer-project --bounds', which
answers fn-cpj-max-cursor-octets and fn-cpj-max-event-octets), never copied
here: a fixed "over-bound" size went stale when the event ceiling became the
u32 composite's (dev-health packet 2).  The over-bound event file is sparse
(the host refuses on its fstat size before reading a byte).
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
    def bounds(self):
        result = subprocess.run(
            [str(IMAGE), "--fn", "consumer-project", "--bounds"],
            cwd=ROOT, capture_output=True, timeout=30, check=False,
            env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"})
        self.assertEqual(result.returncode, 0, result.stderr)
        words = result.stdout.split()
        self.assertEqual(len(words), 3, result.stdout)
        self.assertEqual(words[0], b"fn-consumer-project-bounds-v1")
        return int(words[1]), int(words[2])

    @staticmethod
    def write_sized(path, size):
        with open(path, "wb") as stream:
            stream.write(b"\0")
            stream.truncate(size)

    def test_overbound_cursor_and_event_refuse_without_projection(self):
        cursor_bound, event_bound = self.bounds()
        with tempfile.TemporaryDirectory(prefix="fn-consumer-project-bound-") as td:
            root = Path(td)
            cursor = root / "cursor.fncu"
            event = root / "event.fn-e"
            cases = ((cursor_bound + 1, 1), (1, event_bound + 1))
            for cursor_size, event_size in cases:
                with self.subTest(cursor=cursor_size, event=event_size):
                    self.write_sized(cursor, cursor_size)
                    self.write_sized(event, event_size)
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
            # At each ceiling exactly: within bound, so the codec decides.
            cursor_bound, _ = self.bounds()
            for cursor_size in (1, cursor_bound):
                with self.subTest(cursor=cursor_size):
                    self.write_sized(cursor, cursor_size)
                    event.write_bytes(b"\0")
                    self.assert_codec(cursor, event)

    def assert_codec(self, cursor, event):
        result = subprocess.run(
            [str(IMAGE), "--fn", "consumer-project", str(cursor), str(event)],
            cwd=ROOT, capture_output=True, timeout=30, check=False,
            env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"})
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(result.stdout.strip(),
                         b"fn-consumer-project-refused-v1 codec")


if __name__ == "__main__":
    unittest.main()
