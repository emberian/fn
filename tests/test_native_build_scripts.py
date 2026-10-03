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


class IoLispLeftovers(unittest.TestCase):
    """S078: dead code and a stale docstring in host/native/io.lisp."""

    def setUp(self):
        self.io = (ROOT / "host/native/io.lisp").read_text()

    def test_import_checks_store_exists_once(self):
        form = '(when (fnn-lstat root)\n    (fnn-refuse "import refused reason=store-exists"))'
        self.assertEqual(self.io.count(form), 1)

    def test_dead_accept_any_loop_is_gone(self):
        self.assertNotIn("(defun fnn-accept-any-loop", self.io)

    def test_recovery_barrier_docstring_matches_the_three(self):
        self.assertNotIn("five recovery\nbarriers", self.io)
        self.assertNotIn("five recovery barriers", self.io)


class LfJoinedSweepIsGone(unittest.TestCase):
    def test_lf_joined_staging_sweep_removed(self):
        # S117: no caller remained after the native sweep took the structured round.
        text = (ROOT / "host/store-node-host.lisp").read_text()
        self.assertNotIn("(defun fn-store-sn-sweep-staging", text)
        self.assertNotIn("(defun fn-store-sn-join-octet-names", text)


class TlsOversizeSan(unittest.TestCase):
    def test_uncopyable_san_extension_is_not_reported_as_no_names(self):
        # S094: an extension that is present but cannot be copied must not
        # reach ACL2 as NIL (= "no names", accepted).
        text = (ROOT / "host/native/tls.lisp").read_text()
        m = re.search(r"\(defun fnn-tls-leaf-facts .*?\n\n", text, re.S)
        self.assertIsNotNone(m)
        self.assertIn("(list 0)", m.group(0))


class AnchorKeyWidth(unittest.TestCase):
    def test_host_does_not_compare_key_width_with_nonce_width(self):
        # S095: the key width is ACL2's decision (the parser refuses a wrong one).
        text = (ROOT / "host/native/anchor.lisp").read_text()
        self.assertNotIn("(/= (length key) nonce-octets)", text)
        self.assertNotIn("'(:fault :pinned-key)", text)


if __name__ == "__main__":
    unittest.main()
