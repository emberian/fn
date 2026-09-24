"""Teeth for `tools/build_lists_check.py`: the DTN build's missing `ld`.

native-subsets-6c0626c5 failure 2: host/native/build-dtn.lisp did not `ld`
host/checkpoint-host.lisp, and io.lisp names its
`fn-store-checkpoint-clone-fence-name` when a Store opens.  The first case
restores that omission and requires both findings; the others show each
clause of the check fails without its premise.
"""

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import build_lists_check as check  # noqa: E402

CHECKPOINT_LD = '(ld "host/checkpoint-host.lisp" :ld-error-action :error)\n'


class BuildListsCheckTests(unittest.TestCase):
    def dtn_text(self):
        return (ROOT / check.DTN_BUILD).read_text()

    def test_tree_is_clean(self):
        self.assertEqual(check.findings(), [])

    def test_missing_checkpoint_ld_is_found_twice(self):
        text = self.dtn_text()
        self.assertIn(CHECKPOINT_LD, text)
        found = check.findings(dtn_text=text.replace(CHECKPOINT_LD, ""))
        self.assertTrue(any(line.startswith("omitted: host/checkpoint-host.lisp")
                            for line in found), found)
        self.assertTrue(any("host/native/io.lisp names 'fn-store-checkpoint-clone-fence-name"
                            in line for line in found), found)

    def test_allowlisted_omission_is_still_checked_for_reach(self):
        # Listing the file as omitted does not excuse io.lisp's reference.
        text = self.dtn_text().replace(CHECKPOINT_LD, "")
        omitted = dict(check.DTN_OMITTED)
        omitted["host/checkpoint-host.lisp"] = ("pretend", {})
        found = check.findings(dtn_text=text, omitted=omitted)
        self.assertFalse(any(line.startswith("omitted:") for line in found), found)
        self.assertTrue(any("fn-store-checkpoint-clone-fence-name" in line
                            for line in found), found)

    def test_unlisted_reference_into_an_omitted_file_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        reason, _ = omitted["host/native-control-host.lisp"]
        omitted["host/native-control-host.lisp"] = (reason, {})
        found = check.findings(omitted=omitted)
        self.assertTrue(any("host/native/operator.lisp names "
                            "'fn-native-control-host-status-exit-code"
                            in line for line in found), found)

    def test_unexplained_omission_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        del omitted["host/native-auth-host.lisp"]
        found = check.findings(omitted=omitted)
        self.assertIn("omitted: host/native-auth-host.lisp", "\n".join(found))

    def test_stale_entry_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        omitted["host/store-host.lisp"] = ("loaded by both", {})
        found = check.findings(omitted=omitted)
        self.assertIn("stale: DTN_OMITTED lists host/store-host.lisp", "\n".join(found))

    def test_raw_call_into_an_unloaded_module_is_found(self):
        # The second layer of the same failure: with checkpoint-host loaded,
        # the c7b76b59 DTN images still refused `store init`, because io.lisp
        # called fnn-checkpoint-name-result and only checkpoint.lisp, which
        # build-dtn.lisp does not load, defined it.  Restore those two files.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            for path in ("host/native/io.lisp", "host/native/checkpoint.lisp"):
                old = subprocess.run(["git", "show", f"c7b76b59:{path}"], cwd=ROOT,
                                     check=True, capture_output=True, text=True).stdout
                (root / path).write_text(old)
            found = check.findings(root=root)
            self.assertIn("raw: host/native/io.lisp calls fnn-checkpoint-name-result, "
                          "defined only in host/native/checkpoint.lisp", "\n".join(found))

    def test_unlisted_raw_reach_is_found(self):
        reach = dict(check.DTN_RAW_REACH)
        del reach[("host/native/operator.lisp", "fnn-native-auth-admin-execute")]
        found = check.findings(reach=reach)
        self.assertEqual(found, ["raw: host/native/operator.lisp calls "
                                 "fnn-native-auth-admin-execute, defined only in "
                                 "host/native/auth-admin.lisp, which "
                                 "host/native/build-dtn.lisp does not load"])

    def test_docstring_mention_is_not_a_call(self):
        text = check.strip_code('(defun f () "see (fnn-x y) here" (fnn-y #\\( 1)) ; (fnn-z)')
        self.assertEqual(check.RAW_USE.findall(text), ["fnn-y"])


if __name__ == "__main__":
    unittest.main()
