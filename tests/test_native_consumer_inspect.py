"""The native offline fncu inspector uses the ACL2 decoder and byte ceiling.

Run against a source-matched developer image with
FN_RUN_CONSUMER_INSPECT=1 and FN_NATIVE_DEVELOPER_HOST set. The binary
fixtures mirror vectors in consumer-position-tests.lisp.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
FIXTURES = ROOT / "tests" / "fixtures" / "consumer-position"
ENABLED = os.environ.get("FN_RUN_CONSUMER_INSPECT") == "1"


@unittest.skipUnless(ENABLED and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_RUN_CONSUMER_INSPECT=1 and a source-matched image")
class NativeConsumerInspectTests(unittest.TestCase):
    def run_inspect(self, path):
        return subprocess.run(
            [str(IMAGE), "--fn", "consumer-inspect", str(path)], cwd=ROOT,
            capture_output=True, timeout=30, check=False,
            env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"})

    def test_exact_max_cursor_and_high_octet_ids(self):
        fixture = FIXTURES / "max-cursor-v1.fncu"
        self.assertEqual(fixture.stat().st_size, 346)
        result = self.run_inspect(fixture)
        self.assertEqual(result.returncode, 0, result.stderr)
        ff = "ff" * 64
        self.assertEqual(
            result.stdout.decode("ascii").strip(),
            "fn-consumer-inspect-v1 history={0} incarnation={0} consumer={0} "
            "principal={0} query={0} query-version=4294967295 "
            "view-version=4294967295 registration-epoch=4294967295 "
            "position=4294967295 currentness=unverified "
            "acceptance=unverified processing=unverified".format(ff))

    def test_zero_position_is_reported_exactly(self):
        result = self.run_inspect(
            FIXTURES / "zero-position-high-octets-v1.fncu")
        self.assertEqual(result.returncode, 0, result.stderr)
        ff = "ff" * 64
        self.assertIn(("history={0} incarnation={0} consumer={0} principal={0} "
                       "query={0} query-version=1 view-version=1 "
                       "registration-epoch=1 position=0 ").format(ff),
                      result.stdout.decode("ascii"))

    def test_truncated_trailing_and_unknown_version_refuse(self):
        valid = (FIXTURES / "max-cursor-v1.fncu").read_bytes()
        short = (FIXTURES / "five-field-v1.fncu").read_bytes()
        cases = (("truncated", valid[:-1], b"grammar"),
                 ("trailing", short + b"\x00", b"grammar"),
                 ("empty-id", short[:5] + b"\x00" + short[6:], b"grammar"),
                 ("unknown-version", valid[:4] + b"\x02" + valid[5:],
                  b"version"))
        with tempfile.TemporaryDirectory(prefix="fn-consumer-inspect-") as td:
            for name, contents, reason in cases:
                with self.subTest(name=name):
                    path = Path(td) / (name + ".fncu")
                    path.write_bytes(contents)
                    result = self.run_inspect(path)
                    self.assertEqual(result.returncode, 1, result.stderr)
                    self.assertEqual(
                        result.stdout.strip(),
                        b"fn-consumer-inspect-refused-v1 " + reason)

    def test_oversize_is_refused_at_the_acl2_encoding_ceiling(self):
        with tempfile.TemporaryDirectory(prefix="fn-consumer-inspect-bound-") as td:
            path = Path(td) / "oversize.fncu"
            path.write_bytes(b"\x00" * 347)
            result = self.run_inspect(path)
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(result.stdout.strip(),
                             b"fn-consumer-inspect-refused-v1 limit")


if __name__ == "__main__":
    unittest.main()
