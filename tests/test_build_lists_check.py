"""Teeth for `tools/build_lists_check.py`: the DTN build's missing `ld`.

native-subsets-6c0626c5 failure 2: host/native/build-dtn.lisp did not `ld`
host/checkpoint-host.lisp, and io.lisp names its
`fn-store-checkpoint-clone-fence-name` when a Store opens.  The first case
restores that omission and requires both findings; the others show each
clause of the check fails without its premise.
"""

import sys
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
        reason, _ = omitted["host/bp-release-owner-host.lisp"]
        omitted["host/bp-release-owner-host.lisp"] = (reason, {})
        found = check.findings(omitted=omitted)
        self.assertTrue(any("host/native/workflow.lisp names 'fn-owner-workflow-reset"
                            in line for line in found), found)

    def test_unexplained_omission_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        del omitted["host/native-operator-host.lisp"]
        found = check.findings(omitted=omitted)
        self.assertIn("omitted: host/native-operator-host.lisp", "\n".join(found))

    def test_stale_entry_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        omitted["host/store-host.lisp"] = ("loaded by both", {})
        found = check.findings(omitted=omitted)
        self.assertIn("stale: DTN_OMITTED lists host/store-host.lisp", "\n".join(found))


if __name__ == "__main__":
    unittest.main()
