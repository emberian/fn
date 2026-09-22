"""Native credential replacement EIO/death cuts and fresh-process recovery."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
ACL2 = os.environ.get("FN_ACL2") or shutil.which("acl2")
RAW = ROOT / "host" / "native" / "auth-admin.lisp"

MODEL_CUTS = {
    "cleanup-unlinked", "cleanup-directory-durable",
    "recovery-file-durable", "recovery-directory-durable",
    "stage-durable", "replace-issued", "replace-returned",
    "final-directory-durable",
}


def lisp_string(text: str) -> str:
    return '"{}"'.format(text.replace("\\", "\\\\").replace('"', '\\"'))


def run_acl2(driver: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    process_env = dict(os.environ)
    process_env["ACL2_CUSTOMIZATION"] = "NONE"
    process_env.pop("ACL2_SYSTEM_BOOKS", None)
    if env:
        process_env.update(env)
    return subprocess.run(
        [str(ACL2)], cwd=ROOT, input=driver.encode("ascii"),
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        env=process_env, timeout=900, check=False,
    )


def raw_prefix() -> str:
    return """(in-package \"ACL2\")
(ld \"books/native-auth-admin.lisp\" :ld-error-action :error)
(ld \"host/native-auth-admin-host.lisp\" :ld-error-action :error)
(defttag :fn-native-auth-admin-fidelity)
(progn!
 (set-raw-mode t)
 (load \"host/native/io.lisp\")
 ; FN_NATIVE_AUTH_ADMIN_FAULT is a developer-image selector: it reads as NIL
 ; under the production profile (host/native/io.lisp fnn-developer-selector).
 (fnn-select-image-profile \"developer\")
 (load \"host/native/auth-admin.lisp\")
"""


def publish_driver(root: Path) -> str:
    quoted = lisp_string(str(root))
    return raw_prefix() + f"""
 (let* ((root {quoted})
        (final (fnn-concat root \"/auth.toml\"))
        (stage (fnn-concat final \".stage\"))
        (name (map 'list #'char-code \"native-reader\"))
        (secret (map 'list #'char-code \"correct-horse\"))
        (salt '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
        (result (fnn-core 'fn-native-auth-admin-host-set-password
                          nil nil name secret secret salt nil nil t))
        (octets (fnn-core 'fn-native-auth-admin-host-result-octets result))
        (*fnn-native-auth-admin-cut-callback*
          (fnn-native-auth-admin-test-cut))
        (outcome (fnn-native-auth-admin-publish stage final root octets)))
   (unless (eq outcome :uncertain)
     (error \"post-replace EIO was not uncertain: ~s\" outcome))
   (format t \"FN_NATIVE_AUTH_ADMIN_UNCERTAIN_PASS~%\")))
(set-raw-mode nil)
(defttag nil)
(quit)
"""


def recover_driver(root: Path) -> str:
    quoted = lisp_string(str(root))
    return raw_prefix() + f"""
 (let* ((root {quoted})
        (final (fnn-concat root \"/auth.toml\"))
        (stage (fnn-concat final \".stage\")))
   (unless (fnn-native-auth-admin-recover stage final root)
     (error \"fresh process did not recover published final\"))
   (let* ((octets (fnn-native-auth-admin-read-held final t))
          (listed (fnn-core 'fn-native-auth-admin-host-list octets t))
          (report (fnn-core 'fn-native-auth-admin-host-result-report listed)))
     (unless (and (eq (fnn-core
                       'fn-native-auth-admin-host-result-status listed)
                      :accepted)
                  (search \"native-reader\"
                          (fnn-octets-string (fnn-octets report))))
       (error \"recovered registry did not list its credential\")))
   ; A fixed stage from a different dead attempt is cleaned and its unlink is
   ; directory-barriered before final-name recovery.
   (fnn-write-staged stage (fnn-octets '(35 32 100 101 98 114 105 115 10)))
   (unless (fnn-native-auth-admin-recover stage final root)
     (error \"stage cleanup did not preserve final\"))
   (when (probe-file stage) (error \"stage survived recovery\"))
   (format t \"FN_NATIVE_AUTH_ADMIN_RECOVERY_PASS~%\")))
(set-raw-mode nil)
(defttag nil)
(quit)
"""


class NativeAuthAdminSourceMapTests(unittest.TestCase):
    def test_each_model_cut_is_on_the_actual_raw_executor(self):
        source = RAW.read_text(encoding="utf-8")
        block = re.search(
            r"\(defparameter \+fnn-native-auth-admin-test-cuts\+(.*?)\)\n\n",
            source, re.S,
        )
        self.assertIsNotNone(block)
        self.assertEqual(set(re.findall(r'"([a-z-]+)"', block.group(1))), MODEL_CUTS)
        for anchor in (
            "(fnn-native-auth-admin-at :cleanup-unlinked)",
            "(fnn-native-auth-admin-at :replace-issued)",
            "(fnn-replace stage final)",
            "(fnn-native-auth-admin-at :replace-returned)",
            "(fnn-native-auth-admin-at :final-directory-durable)",
        ):
            self.assertIn(anchor, source)


@unittest.skipUnless(ACL2 and os.access(str(ACL2), os.X_OK), "real ACL2 is required")
class NativeAuthAdminFidelityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-auth-admin-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def assert_recovery(self):
        recovered = run_acl2(recover_driver(self.root))
        self.assertEqual(recovered.returncode, 0, recovered.stdout.decode("utf-8", "replace"))
        self.assertIn(b"FN_NATIVE_AUTH_ADMIN_RECOVERY_PASS", recovered.stdout)
        self.assertNotIn(b"ACL2 Error", recovered.stdout)

    def test_post_rename_eio_is_uncertain_then_fresh_process_recovers(self):
        attempted = run_acl2(
            publish_driver(self.root),
            {"FN_NATIVE_AUTH_ADMIN_FAULT": "replace-returned:eio"},
        )
        self.assertEqual(attempted.returncode, 0, attempted.stdout.decode("utf-8", "replace"))
        self.assertIn(b"FN_NATIVE_AUTH_ADMIN_UNCERTAIN_PASS", attempted.stdout)
        self.assertTrue((self.root / "auth.toml").is_file())
        self.assert_recovery()

    def test_sigkill_after_rename_recovers_in_a_new_process(self):
        killed = run_acl2(
            publish_driver(self.root),
            {"FN_NATIVE_AUTH_ADMIN_FAULT": "replace-returned:kill"},
        )
        self.assertEqual(killed.returncode, -9, killed.stdout.decode("utf-8", "replace"))
        self.assertTrue((self.root / "auth.toml").is_file())
        self.assert_recovery()


if __name__ == "__main__":
    unittest.main()
