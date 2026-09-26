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
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "build_native_host.sh"
FAKE = """#!/bin/sh
cat > /dev/null
printf '%s\\n' "$FAKE_LINE"
echo FN_NATIVE_BUILD_LOADED
printf '#!/bin/sh\\n' > "$FN_NATIVE_IMAGE"; chmod +x "$FN_NATIVE_IMAGE"
echo core > "$FN_NATIVE_IMAGE.core"
"""
MARKERS = ("ACL2 Error [Failure] in ( DEFUN FNN-X ...)",
           "HARD ACL2 ERROR in FMT: bad directive",
           "ABORTING from raw Lisp for (INCLUDE-BOOK ...)",
           "ACL2 Warning [Uncertified] in ( INCLUDE-BOOK \"x\" ...)")


class BuildNativeHostRefusalTests(unittest.TestCase):
    def build(self, line):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "acl2"
            fake.write_text(FAKE)
            fake.chmod(0o755)
            env = {**os.environ, "FN_ACL2": str(fake), "FAKE_LINE": line,
                   "FN_NATIVE_BUILD": str(base / "build.lisp"),
                   "FN_NATIVE_IMAGE": str(base / "fn-host-test"),
                   "FN_NATIVE_LOG": str(base / "build.log"),
                   "FN_OPENSSL_PREFIX": str(base)}
            (base / "build.lisp").write_text("(value :q)\n")
            answer = subprocess.run(["sh", str(SCRIPT)], env=env, cwd=ROOT,
                                    capture_output=True, text=True, timeout=60)
            return answer, (base / "build.log").read_text()

    def test_each_marker_refuses_the_build_and_prints_the_line(self):
        for line in MARKERS:
            with self.subTest(line=line):
                answer, log = self.build(line)
                self.assertIn(line, log)
                self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
                self.assertIn("error or uncertified-book marker", answer.stderr)
                self.assertIn(line, answer.stderr)
                self.assertNotIn("built ", answer.stdout)

    def test_a_clean_log_builds(self):
        answer, _ = self.build("ACL2 !>")
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        self.assertIn("built ", answer.stdout)


if __name__ == "__main__":
    unittest.main()
