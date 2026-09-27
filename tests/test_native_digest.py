"""A-CRYPTO-NATIVE: the served image's SHA-256 is the ACL2 reference's.

host/native/digest.lisp replaces the raw definitions of fn-sha256-stobj,
fn-sha256-of-string and fn-sha256-of-prefixed-buffer with the pinned
libcrypto's EVP SHA-256 after a start-up check.  These witnesses run the
saved images:

* the developer verb `digest-check run COUNT SEED' digests COUNT inputs
  (8,000 by default; 100,000 in the lane's evidence run)
  natively and by the ACL2 references captured before installation (every
  length 0..4200, the block and copy-chunk edges, then log-uniform lengths
  to 1 MiB; list, prefixed-buffer and string forms) and reports agreement;
* `digest-check bench' reports MB/s of both (recorded, not asserted);
* the production image's `sha256' verb over a file equals Python's hashlib
  (a third implementation, over the served image's native path), and the
  production image refuses `digest-check' by name.

Each witness skips, naming the image, when that image is absent.
"""
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
# The module's default fits the 20 s test budget; the lane's evidence run
# sets FN_TEST_DIGEST_COUNT=100000 (planning/evidence/digest-native-2026-09-27.md).
COUNT = int(os.environ.get("FN_TEST_DIGEST_COUNT", "8000"))
EXIT_USAGE = 5


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("SBCL_USER_ARGS", None)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def run(image, args, timeout=3000):
    return subprocess.run([str(image), "--fn"] + args, env=environment(),
                          stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout)


class DeveloperDifferentialTests(unittest.TestCase):
    def setUp(self):
        if not executable(DEVELOPER):
            self.skipTest(f"no developer image at {DEVELOPER}")

    def test_native_agrees_with_reference_on_every_input(self):
        done = run(DEVELOPER, ["digest-check", "run", str(COUNT), "1"])
        out = done.stdout.decode()
        print(out.strip())
        self.assertEqual(done.returncode, 0, out + done.stderr.decode())
        found = re.search(r"digest-check \(:agree (\d+) :buffer-reference (\d+) "
                          r":string-reference (\d+) :octets (\d+)\)", out)
        self.assertIsNotNone(found, out)
        self.assertEqual(int(found.group(1)), max(COUNT, 4201 + 90 + 24 + 1))
        self.assertGreater(int(found.group(2)), 0)
        self.assertEqual(int(found.group(3)), 4201 + sum(
            1 for j in range(15) for d in (-1, 0, 1, 55, 56, 63)
            if 64 * (1 << j) + d <= 4200))

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

    def test_sha256_verb_is_hashlib(self):
        with tempfile.TemporaryDirectory() as directory:
            for size in (0, 55, 56, 64, 16384, 16385, 1 << 20):
                path = Path(directory) / f"m{size}"
                data = bytes((i * 131 + size) & 0xFF for i in range(size))
                path.write_bytes(data)
                done = run(IMAGE, ["sha256", str(path)], timeout=300)
                self.assertEqual(done.returncode, 0, done.stderr.decode())
                self.assertEqual(done.stdout.decode().strip(),
                                 hashlib.sha256(data).hexdigest(), size)

    def test_production_refuses_digest_check(self):
        done = run(IMAGE, ["digest-check", "run", "1"], timeout=300)
        self.assertEqual(done.returncode, EXIT_USAGE, done.stdout + done.stderr)
        self.assertIn(b"digest-check is available only in the developer image",
                      done.stderr + done.stdout)


if __name__ == "__main__":
    unittest.main()
