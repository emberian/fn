"""Source-level rules on the native image build scripts (burn-down S141, S138)."""
import re
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ("host/native/build.lisp", "host/native/build-dtn.lisp")


def _code(path):
    text = (ROOT / path).read_text()
    return "\n".join(l for l in text.splitlines() if not l.lstrip().startswith(";"))


class BuildScripts(unittest.TestCase):
    def test_no_host_file_is_ld_ed_twice(self):
        # S141: a second ld of host/page-read-host.lisp redoes every defun for nothing.
        for script in SCRIPTS:
            lds = re.findall(r'^\(ld "(host/[^"]+)"', _code(script), re.M)
            dups = [f for f, n in Counter(lds).items() if n > 1]
            self.assertEqual(dups, [], f"{script} ld's twice: {dups}")

    def test_native_library_checks_run_inside_startup_guard(self):
        # S138: the crypto/TLS/digest/signature/deflate startup checks must run
        # under fnn-native-startup (refused start, exit 5), in both builds.
        for script in SCRIPTS:
            code = _code(script)
            self.assertIn("(fnn-native-startup", code, script)
            m = re.search(r"\(defun fn-native-entry \(st\)(.*?)\n        \(load", code, re.S)
            self.assertIsNotNone(m, script)
            body = m.group(1)
            self.assertNotRegex(
                body, r"^\s*\(fnn-crypto-startup\)", f"{script}: unguarded startup checks")


if __name__ == "__main__":
    unittest.main()
