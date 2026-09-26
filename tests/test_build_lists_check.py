"""Teeth for `tools/build_lists_check.py`: the DTN build's missing `ld`.

native-subsets-6c0626c5 failure 2: host/native/build-dtn.lisp did not `ld`
host/checkpoint-host.lisp, and io.lisp names its
`fn-store-checkpoint-clone-fence-name` when a Store opens.  The first case
restores that omission and requires both findings; the others show each
clause of the check fails without its premise.
"""

import contextlib
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


BUFFER_INCLUDES = ('(include-book "books/octets-stobj")\n'
                   '(include-book "books/poster-bytes-buffer")\n'
                   ';; host/native/io.lisp fnn-subject-id-buffer calls '
                   'fn-shb-subject-id-bounded, as in build.lisp.\n'
                   '(include-book "books/sha256-buffer")\n'
                   ';; D13 (STO-014): the duplicate-versus-conflict verdict over a '
                   'store that may\n'
                   ';; hold tombstones.  host/owner-host.lisp and '
                   'host/store-node-host.lisp call\n'
                   ';; fn-rcl-existing-action (list payload) and '
                   'fn-rclb-existing-action (buffer).\n'
                   '(include-book "books/store-reclaim-buffer")\n')
BUFFER_FINDINGS = [
    "included: host/owner-host.lisp uses fn-octets, defined in "
    "books/octets-stobj.lisp, which host/native/build-dtn.lisp has not "
    "included when it loads host/owner-host.lisp",
    "included: host/owner-host.lisp uses fn-rclb-existing-action, defined in "
    "books/store-reclaim-buffer.lisp, which host/native/build-dtn.lisp has not "
    "included when it loads host/owner-host.lisp"]
# fn-rcl-existing-action is no longer a finding: host/store-node-host.lisp
# includes books/store-reclaim itself since test-latency (the Python bridge
# loads that host file alone).
# host/owner-host.lisp no longer names fn-shb-subject-id: the served POST calls
# the guard-verified fn-shb-subject-id-bounded from host/native/io.lisp
# (qual-e747dbcc A4), outside the `ld` closure this check reads.


OWNER_HOST_SELF_INCLUDES = ('(include-book "../books/records-concrete-owner")\n'
                            '(include-book "../books/octets-stobj")\n'
                            '(include-book "../books/store-reclaim-buffer")\n')


@contextlib.contextmanager
def bare_owner_host():
    """A copy of books/ and host/ whose owner-host.lisp does not include the
    books it uses from the octet buffer and the owner record codec: the tree
    before harness-repair, for the checks' teeth."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        shutil.copytree(ROOT / "books", root / "books",
                        ignore=shutil.ignore_patterns("*.cert", "*.fasl", "*.port", "*.out"))
        shutil.copytree(ROOT / "host", root / "host")
        owner = root / "host" / "owner-host.lisp"
        text = owner.read_text()
        assert OWNER_HOST_SELF_INCLUDES in text
        owner.write_text(text.replace(OWNER_HOST_SELF_INCLUDES, ""))
        yield root


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

    def test_missing_buffer_includes_are_found(self):
        # native-drift-2026-09-25 finding 3: at 32842f50 build-dtn.lisp did
        # not include the octet buffer books host/owner-host.lisp uses, and
        # the DTN image did not build.  host/owner-host.lisp now includes
        # them itself (harness-repair), so the omission is restored in a copy
        # whose owner-host.lisp does not.
        text = self.dtn_text()
        self.assertIn(BUFFER_INCLUDES, text)
        with bare_owner_host() as root:
            found = check.include_findings(root, text.replace(BUFFER_INCLUDES, ""))
        self.assertEqual(found, BUFFER_FINDINGS)

    def test_include_after_the_ld_is_too_late(self):
        # The order matters: an include after the `ld` does not serve it.
        text = self.dtn_text().replace(BUFFER_INCLUDES, "") + BUFFER_INCLUDES
        with bare_owner_host() as root:
            found = check.include_findings(root, text)
        self.assertEqual(len(found), len(BUFFER_FINDINGS), found)

    def test_owner_host_declares_its_own_books(self):
        # The same omission in the real tree is no finding: every loader of
        # host/owner-host.lisp gets its books from the file itself.
        text = self.dtn_text().replace(BUFFER_INCLUDES, "")
        self.assertEqual(check.include_findings(ROOT, text), [])

    def test_bridges_satisfy_the_include_rule(self):
        self.assertEqual(check.bridge_findings(), [])

    def test_owner_bridge_missing_books_are_found(self):
        # harness-repair (PKT-176): at 483987b1 the owner bridge's boot,
        # tools/bridge_image.OWNER_FORMS, reached host/owner-host.lisp
        # without these three books, and the bridge did not boot.
        with bare_owner_host() as root:
            found = check.bridge_findings(root)
        loader = "the owner bridge (tools/bridge_image.py)"
        self.assertEqual(found, [
            f"included: host/owner-host.lisp uses {name}, defined in {book}, "
            f"which {loader} has not included when it loads host/owner-host.lisp"
            for name, book in (
                ("fn-octets", "books/octets-stobj.lisp"),
                ("fn-rclb-existing-action", "books/store-reclaim-buffer.lisp"),
                ("fn-rcon-ocfg-io", "books/records-concrete-owner.lisp"))])

    def test_default_build_satisfies_the_include_rule(self):
        # The same rule over build.lisp: the default image already builds.
        default = (ROOT / check.DEFAULT_BUILD).read_text()
        self.assertEqual(check.include_findings(ROOT, default), [])

    def test_local_include_does_not_count(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "books/b.lisp").write_text('(local (include-book "a"))\n')
            (root / "books/c.lisp").write_text('(include-book "a")\n')
            (root / "host/h.lisp").write_text('(defun fn-h (x) (fn-a x))\n')
            ld = '(ld "host/h.lisp" :ld-error-action :error)\n'
            self.assertEqual(len(check.include_findings(
                root, '(include-book "books/b")\n' + ld)), 1)
            self.assertEqual(check.include_findings(
                root, '(include-book "books/c")\n' + ld), [])

    def test_docstring_mention_is_not_a_call(self):
        text = check.strip_code('(defun f () "see (fnn-x y) here" (fnn-y #\\( 1)) ; (fnn-z)')
        self.assertEqual(check.RAW_USE.findall(text), ["fnn-y"])


if __name__ == "__main__":
    unittest.main()
