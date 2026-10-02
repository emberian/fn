"""tools/build_native_host.sh refuses a build whose log carries an ACL2 error.

A fake ACL2 (FN_ACL2) prints one marker line and the ready marker and makes
the image files, so the only thing between it and "built" is the log check
at build_native_host.sh's grep (PKT-284's refusal; PKT-305 owed its test).
Every path is in a temporary directory: FN_NATIVE_IMAGE and FN_NATIVE_LOG.
"""
import os
import pathlib
import subprocess
import tempfile
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import profile_limits  # noqa: E402
TLS = profile_limits.get("tls-limit")
SCRIPT = ROOT / "tools" / "build_native_host.sh"
FAKE = """#!/bin/sh
cat > /dev/null
printf '%s\\n' "$FAKE_LINE"
echo "mldsa=$FN_MLDSA_LIBRARY openssl=${FN_OPENSSL_PREFIX:-unset}"
echo FN_NATIVE_BUILD_LOADED
echo "FN_NATIVE_TLS_LIMIT $FAKE_TLS"
echo FN_NATIVE_WORLD_STRIPPED
echo 'fn-world-deps 2' > "$FN_NATIVE_IMAGE.world-deps"
printf '#!/bin/sh\\nexec "/sbcl" --tls-limit 16384 --dynamic-space-size 32000 --core "c"\\n' > "$FN_NATIVE_IMAGE"
chmod +x "$FN_NATIVE_IMAGE"
echo core > "$FN_NATIVE_IMAGE.core"
"""
MARKERS = ("ACL2 Error [Failure] in ( DEFUN FNN-X ...)",
           "HARD ACL2 ERROR in FMT: bad directive",
           "ABORTING from raw Lisp for (INCLUDE-BOOK ...)",
           "ACL2 Warning [Uncertified] in ( INCLUDE-BOOK \"x\" ...)")


class BuildNativeHostRefusalTests(unittest.TestCase):
    def build(self, line, build_text="(value :q)\n", **extra):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "acl2"
            fake.write_text(FAKE)
            fake.chmod(0o755)
            env = {**os.environ, "FN_ACL2": str(fake), "FAKE_LINE": line,
                   "FAKE_TLS": str(TLS),
                   "FN_NATIVE_BUILD": str(base / "build.lisp"),
                   "FN_NATIVE_IMAGE": str(base / "fn-host-test"),
                   "FN_NATIVE_LOG": str(base / "build.log")}
            env.pop("FN_NATIVE_CATALOG", None)
            env.update({k: (v.replace("$BASE", str(base))) for k, v in extra.items()})
            env.pop("FN_OPENSSL_PREFIX", None)
            env.pop("FN_TLS_LIMIT", None)
            (base / "build.lisp").write_text(build_text)
            answer = subprocess.run(["sh", str(SCRIPT)], env=env, cwd=ROOT,
                                    capture_output=True, text=True, timeout=60)
            library = [p for p in (base / "lib").glob("libfn-mldsa65.*")]
            launcher = base / "fn-host-test"
            self.launcher_text = launcher.read_text() if launcher.exists() else ""
            record = base / "fn-host-test.catalog"
            self.catalog_text = record.read_text() if record.exists() else None
            log = base / "build.log"
            return answer, (log.read_text() if log.exists() else ""), library, base

    def test_each_marker_refuses_the_build_and_prints_the_line(self):
        for line in MARKERS:
            with self.subTest(line=line):
                answer, log, _, _ = self.build(line)
                self.assertIn(line, log)
                self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
                self.assertIn("error or uncertified-book marker", answer.stderr)
                self.assertIn(line, answer.stderr)
                self.assertNotIn("built ", answer.stdout)

    def test_a_build_that_prints_no_tls_figure_is_refused(self):
        global TLS
        saved, TLS = TLS, ""
        try:
            answer, _log, _, _ = self.build("ACL2 !>")
        finally:
            TLS = saved
        self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
        self.assertIn("printed no FN_NATIVE_TLS_LIMIT", answer.stderr)

    def test_a_clean_log_builds(self):
        answer, log, library, base = self.build("ACL2 !>")
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        self.assertIn("built ", answer.stdout)
        # The saved launcher runs at the profile's TLS limit, which the build
        # printed (FN_NATIVE_TLS_LIMIT), not ACL2's 16384.
        launcher = self.launcher_text
        self.assertIn("--tls-limit {} ".format(TLS), launcher)
        self.assertNotIn("--tls-limit 16384", launcher)
        # HST-016: the ML-DSA-65 library is built into lib/ beside the image
        # and named to the build; no OpenSSL prefix is needed.
        self.assertEqual(len(library), 1, answer.stderr)
        line = [x for x in log.splitlines() if x.startswith("mldsa=")][0]
        named, openssl = line[len("mldsa="):].split(" openssl=")
        self.assertEqual(os.path.realpath(named), os.path.realpath(library[0]))
        self.assertEqual(openssl, "unset")
        # The catalog is recorded beside the image (tools/image_set.py reads it).
        self.assertEqual(self.catalog_text, "old\n")

    def test_old_catalog_refuses_paged_build_by_name_before_running_acl2(self):
        answer, log, _, _ = self.build(
            "ACL2 !>", FN_NATIVE_CATALOG="old",
            FN_NATIVE_BUILD="build/native-build-paged.lisp", FN_NATIVE_IMAGE="build/fn-host")
        self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
        self.assertIn("build/native-build-paged.lisp is a paged build script", answer.stderr)
        self.assertEqual(log, "")
        self.assertIsNone(self.catalog_text)

    def test_old_catalog_refuses_paged_build_by_content_before_running_acl2(self):
        answer, log, _, _ = self.build(
            "ACL2 !>", build_text='(include-book "books/image-world-paged")\n(value :q)\n',
            FN_NATIVE_CATALOG="old")
        self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
        self.assertIn("build.lisp includes books/image-world-paged", answer.stderr)
        self.assertEqual(log, "")
        self.assertIsNone(self.catalog_text)

    def test_the_image_name_says_its_catalog(self):
        # Codex r21 F2: a paged core is never built under the old name, and
        # an old one never under a -paged name.
        answer, _log, _, _ = self.build("ACL2 !>", FN_NATIVE_CATALOG="paged",
                                        FN_NATIVE_BUILD="host/native/build.lisp")
        self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
        self.assertIn("builds an image named *-paged", answer.stderr)
        self.assertNotIn("built ", answer.stdout)
        answer, _log, _, _ = self.build("ACL2 !>", FN_NATIVE_IMAGE="$BASE/fn-host-x-paged")
        self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
        self.assertIn("a paged image's name", answer.stderr)


if __name__ == "__main__":
    unittest.main()
