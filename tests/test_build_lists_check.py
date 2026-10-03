"""Teeth for `tools/build_lists_check.py`: the DTN build's missing `ld`.

native-subsets-6c0626c5 failure 2: host/native/build-dtn.lisp did not `ld`
host/checkpoint-host.lisp, and io.lisp names its
`fn-store-checkpoint-clone-fence-name` when a Store opens.  The first case
restores that omission and requires both findings; the others show each
clause of the check fails without its premise.
"""

import contextlib
import re
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


# The octet-buffer books host/owner-host.lisp and host/store-node-host.lisp
# use (native-drift-2026-09-25 finding 3: at 32842f50 build-dtn.lisp lacked
# them and the DTN image did not build).  The host files include them
# themselves now, so removing them from the build list is no finding.
BUFFER_BOOKS = ("octets-stobj", "poster-bytes-buffer", "store-reclaim-buffer",
                "post-identity-index", "post-retain-carried", "owner-prepare-served")


def drop_includes(text: str, books) -> str:
    """TEXT without its top-level include-book of each of BOOKS."""
    for book in books:
        text = re.sub(r'^\(include-book "books/%s"\)\n' % re.escape(book), "", text,
                      flags=re.M)
    return text


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
        reason, _ = omitted["host/native/reader-model-host.lisp"]
        omitted["host/native/reader-model-host.lisp"] = (reason, {})
        found = check.findings(omitted=omitted)
        self.assertTrue(any("host/native/io.lisp names 'fn-reader-model-octets"
                            in line for line in found), found)

    def test_an_excuse_nothing_needs_is_stale(self):
        omitted = dict(check.DTN_OMITTED)
        reason, allowed = omitted["host/reader-host.lisp"]
        omitted["host/reader-host.lisp"] = (
            reason, {**allowed, "fn-reader-observe-clock": "pretend"})
        found = check.findings(omitted=omitted)
        self.assertEqual(found, ["stale: DTN_OMITTED excuses fn-reader-observe-clock "
                                 "(host/reader-host.lisp), which nothing "
                                 "host/native/build-dtn.lisp loads names any more"])

    def test_unexplained_omission_is_found(self):
        omitted = dict(check.DTN_OMITTED)
        del omitted["host/native-auth-admin-host.lisp"]
        found = check.findings(omitted=omitted)
        self.assertIn("omitted: host/native-auth-admin-host.lisp", "\n".join(found))

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
        # Batch AX: at 6f397c158 the DTN image's operator.lisp called the
        # live surfaces (auth-admin, control, tls-reload, ...) behind a
        # run-time flag.  Restore that operator.lisp.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            old = subprocess.run(["git", "show", "6f397c158:host/native/operator.lisp"],
                                 cwd=ROOT, check=True, capture_output=True,
                                 text=True).stdout
            (root / "host/native/operator.lisp").write_text(old)
            found = check.findings(root=root)
        self.assertIn("raw: host/native/operator.lisp calls fnn-native-auth-admin-execute, "
                      "defined only in host/native/auth-admin.lisp, which "
                      "host/native/build-dtn.lisp does not load", found)
        self.assertIn("raw: host/native/operator.lisp calls fnn-control-live-status, "
                      "defined only in host/native/control.lisp, which "
                      "host/native/build-dtn.lisp does not load", found)

    def test_an_unused_raw_reach_excuse_is_stale(self):
        found = check.findings(reach={("host/native/operator.lisp",
                                       "fnn-native-auth-admin-execute"): "pretend"})
        self.assertEqual(found, ["stale: DTN_RAW_REACH excuses host/native/operator.lisp "
                                 "calling fnn-native-auth-admin-execute, which it no longer "
                                 "does (or the DTN image now loads its definition)"])

    def test_a_missing_or_late_loader_include_is_found(self):
        # The loader must include a host file's book BEFORE the `ld`: omitted
        # or after it, the use is a finding (the 32842f50 DTN build failure).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/h.lisp").write_text('(defun fn-h (x) (fn-a x))\n')
            include, ld = '(include-book "books/a")\n', '(ld "host/h.lisp" :ld-error-action :error)\n'
            self.assertEqual(check.include_findings(root, include + ld), [])
            for loader in (ld, ld + include):
                with self.subTest(loader=loader):
                    found = check.include_findings(root, loader)
                    self.assertEqual(found, [
                        "included: host/h.lisp uses fn-a, defined in books/a.lisp, which "
                        "host/native/build-dtn.lisp has not included when it loads "
                        "host/h.lisp"], found)

    def test_owner_host_declares_its_own_books(self):
        # The same omission in the real tree is no finding: every loader of
        # host/owner-host.lisp gets its books from the file itself.
        text = self.dtn_text()
        bare = drop_includes(text, BUFFER_BOOKS)
        self.assertLess(len(bare), len(text))
        self.assertEqual(check.include_findings(ROOT, bare), [])

    def test_a_nested_ld_serves_its_loader(self):
        # host/store-node-host.lisp loads host/store-host.lisp, which includes
        # books/store-config, before it calls fn-store-group-name; a loader of
        # store-node-host.lisp alone is not short of that book.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/inner.lisp").write_text('(include-book "../books/a")\n')
            (root / "host/outer.lisp").write_text(
                '(ld "inner.lisp" :ld-error-action :error)\n(defun fn-o (x) (fn-a x))\n')
            (root / "host/bare.lisp").write_text('(defun fn-o (x) (fn-a x))\n')
            self.assertEqual(check.include_findings(
                root, '(ld "host/outer.lisp" :ld-error-action :error)\n'), [])
            self.assertEqual(len(check.include_findings(
                root, '(ld "host/bare.lisp" :ld-error-action :error)\n')), 1)

    def test_later_host_include_cannot_justify_earlier_use(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/inner.lisp").write_text('(include-book "../books/a")\n')
            early = '(defun fn-before (x) (fn-a x))\n'
            late = '(defun fn-after (x) (fn-a x))\n'
            for directive in ('(include-book "../books/a")\n',
                              '(ld "inner.lisp" :ld-error-action :error)\n'):
                with self.subTest(directive=directive):
                    outer = root / "host/outer.lisp"
                    outer.write_text(early + directive + late)
                    found = check.include_findings(root, '(ld "host/outer.lisp")\n')
                    self.assertEqual(len(found), 1, found)
                    self.assertIn('host/outer.lisp uses fn-a', found[0])
                    outer.write_text(directive + early + late)
                    self.assertEqual(check.include_findings(
                        root, '(ld "host/outer.lisp")\n'), [])

    def test_nested_child_order_and_earlier_sibling_include(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            child = root / "host/child.lisp"
            child.write_text('(defun fn-child (x) (fn-a x))\n'
                             '(include-book "../books/a")\n')
            (root / "host/outer.lisp").write_text('(ld "child.lisp")\n')
            found = check.include_findings(root, '(ld "host/outer.lisp")\n')
            self.assertEqual(len(found), 1, found)
            self.assertIn('host/child.lisp uses fn-a', found[0])
            (root / "host/first.lisp").write_text('(include-book "../books/a")\n')
            child.write_text('(defun fn-child (x) (fn-a x))\n')
            (root / "host/outer.lisp").write_text(
                '(ld "first.lisp")\n(ld "child.lisp")\n')
            self.assertEqual(check.include_findings(
                root, '(ld "host/outer.lisp")\n'), [])

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
