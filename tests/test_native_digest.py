"""A-CRYPTO-NATIVE: the served image's BLAKE3 is the ACL2 reference's.

host/native/digest.lisp replaces the raw definitions of fn-blake3-stobj,
fn-blake3-of-prefixed-buffer and fn-blake3-of-prefixed-range with the
vendored BLAKE3 C (lib/libfn-blake3) after a start-up check against the
official vectors and ACL2's fn-b3x-hash.  These witnesses run the saved
images:

* the developer verb `digest-check run COUNT SEED' hashes COUNT inputs
  (8,000 by default; 100,000 in the lane's evidence run) natively and by
  ACL2's fn-b3x-hash (every length 0..4200, the chunk, block and copy-chunk
  edges, then log-uniform lengths to 1 MiB; list, prefixed-buffer and window
  forms) and reports agreement;
* `digest-check bench' reports MB/s of both (recorded, not asserted);
* the production image's `blake3' verb over a file equals
  tools/blake3_ref.py's pure-Python BLAKE3 (a third implementation, over the
  served image's native path) on the official vector inputs and random
  octets across the chunk edges, and the production image refuses
  `digest-check' by name.

Each witness skips, naming the image, when that image is absent.
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import blake3_ref  # noqa: E402
from tests.native_harness import (  # noqa: E402
    EXIT, environment, executable, native_image, run as harness_run)


IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
# The module's default fits the 20 s test budget; the lane's evidence run
# sets FN_TEST_DIGEST_COUNT=100000 (planning/evidence/digest-native-2026-09-27.md).
COUNT = int(os.environ.get("FN_TEST_DIGEST_COUNT", "8000"))


def run(image, args, timeout=3000):
    # The image's own control stack (no SBCL_USER_ARGS), as the bench measures it.
    return harness_run([image, "--fn", *args], env=environment({"SBCL_USER_ARGS": None}),
                       stdin=subprocess.DEVNULL, timeout=timeout)


class DeveloperDifferentialTests(unittest.TestCase):
    def setUp(self):
        if not executable(DEVELOPER):
            self.skipTest(f"no developer image at {DEVELOPER}")

    def test_native_agrees_with_reference_on_every_input(self):
        done = run(DEVELOPER, ["digest-check", "run", str(COUNT), "1"])
        out = done.stdout.decode()
        print(out.strip())
        self.assertEqual(done.returncode, 0, out + done.stderr.decode())
        found = re.search(r"digest-check \(:agree (\d+)\s+:reference (\d+)\s+"
                          r":octets (\d+)\)", out)
        self.assertIsNotNone(found, out)
        # Every generated input agreed in the list, buffer and window forms.
        self.assertEqual(int(found.group(1)), max(COUNT, 4201 + 66 + 24 + 1))
        # The ACL2 reference ran on at least every length 0..4200.
        self.assertGreaterEqual(int(found.group(2)), 4201)

    def test_bench_reports_both(self):
        done = run(DEVELOPER, ["digest-check", "bench"])
        out = done.stdout.decode()
        print(out.strip())
        self.assertEqual(done.returncode, 0, out + done.stderr.decode())
        self.assertIn(":native", out)


class ProductionTests(unittest.TestCase):
    def setUp(self):
        if not executable(IMAGE):
            self.skipTest(f"no production image at {IMAGE}")

    def test_blake3_verb_is_the_reference(self):
        with tempfile.TemporaryDirectory() as directory:
            for size in (0, 1, 63, 64, 65, 1023, 1024, 1025, 2049, 16384, 16385, 102400, 1 << 20):
                path = Path(directory) / f"m{size}"
                data = bytes((i * 131 + size) & 0xFF for i in range(size))
                path.write_bytes(data)
                done = run(IMAGE, ["blake3", str(path)], timeout=300)
                self.assertEqual(done.returncode, 0, done.stderr.decode())
                self.assertEqual(done.stdout.decode().strip(),
                                 blake3_ref.blake3_py(data).hex(), size)

    def test_production_refuses_digest_check(self):
        done = run(IMAGE, ["digest-check", "run", "1"], timeout=300)
        self.assertEqual(done.returncode, EXIT.USAGE, done.stdout + done.stderr)
        self.assertIn(b"digest-check is available only in the developer image",
                      done.stderr + done.stdout)


if __name__ == "__main__":
    unittest.main()
