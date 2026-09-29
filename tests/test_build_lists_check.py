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
                   'fn-sidb-subject-id-bounded, as in build.lisp.\n'
                   '(include-book "books/subject-id-buffer")\n'
                   ';; D13 (STO-014): the tombstone-aware same-article test over '
                   'the buffer\n'
                   ';; (fn-rclb-same-articlep), which fn-pidx-existing-action, '
                   "the served POST's\n"
                   ';; duplicate verdict, calls.\n'
                   '(include-book "books/store-reclaim-buffer")\n'
                   # post-identity-index (PRF-191): the served POST's calls.
                   ';; PRF-191: fn-owner-existing-action-buffer and '
                   'fn-owner-prepare-buffer call\n'
                   ';; fn-pidx-existing-action and fn-pidx-sbud-prepare.\n'
                   '(include-book "books/post-identity-index")\n'
                   # post-alloc-2: the served POST's retention admission.
                   ';; fn-owner-prepare-buffer calls fn-prc-refresh and '
                   'fn-prc-sbud-prepare.\n'
                   '(include-book "books/post-retain-carried")\n'
                   # prepare-served: the served decision inside the prepares.
                   ';; PRF-284: host/owner-host.lisp calls fn-pvc-make and the carried budget,\n'
    ';; verdict and POST boundary (fn-pvc-*-carried).\n'
    '(include-book "books/store-profile-carried")\n'
    ';; lane prepare-served: fn-owner-prepare-buffer, fn-owner-prepare,\n'
                   ';; fn-owner-prepare-identity, fn-owner-prepare-topic, '
                   'fn-owner-reconfigure-unstage\n'
                   ';; call books/owner-prepare-served (fn-psrv-).\n'
                   '(include-book "books/owner-prepare-served")\n')
# rep-wave-d-2: the state checkpoint's publication over the buffer.  The book
# includes books/octets-stobj itself, so a fixture that omits the buffer
# includes omits this one too, or the omission is served transitively.
CHECKPOINT_BUFFER_INCLUDES = (
    ";; The octet buffer's checkpoint writers (rep-wave-d-2; the frames' octets):\n"
    ';; host/native/io.lisp fnn-plan-write-all writes fn-sccb-plan-octets per step.\n'
    '(include-book "books/store-checkpoint-buffer")\n'
    ';; The FNSC segments read from the octet buffer (rep-wave-d-3):\n'
    ';; host/store-node-host.lisp fn-store-sco-segment-admit calls fn-sccr-admit-segment.\n'
    '(include-book "books/store-checkpoint-reader")\n'
    ';; The schema-3 tables and the pipeline (lane checkpoint-pipeline, D33/D34):\n'
    ';; host/store-node-host.lisp fn-store-sco-decode calls fn-sct-load,\n'
    ';; fn-store-sco-select calls fn-sco-select-named and\n'
    ';; fn-store-sco-publish-setup calls fn-ockp-setup.\n'
    '(include-book "books/store-checkpoint-tables")\n'
    '(include-book "books/store-checkpoint-tables-reader")\n'
    '(include-book "books/owner-checkpoint-pipeline")\n'
    # ingress-span: the served read over the octet buffer.  The book includes
    # books/octets-stobj (through books/wire-span), so a fixture that omits the
    # buffer includes omits this one too, or the buffer is served transitively.
    ';; The served read over the octet buffer (ingress-span): host/owner-host.lisp\n'
    ';; fn-owner-chunk-span calls fn-scar-ocfg-read-span.\n'
    '(include-book "books/served-span")\n')
# checkpoint-capture-stream (2026-09-26): host/owner-host.lisp now also
# includes books/owner-checkpoint-pipeline, whose closure holds octets-stobj,
# so the bare copy (its three self-includes removed) still reaches fn-octets
# and that finding is gone; the store-reclaim-buffer one stays.
# post-identity-index (PRF-191): the served POST's owner-host calls are now
# fn-pidx-existing-action and fn-pidx-sbud-prepare (books/post-identity-index,
# which includes store-reclaim-buffer), so those two are the findings.
# post-alloc-2: the prepare is fn-prc-sbud-prepare over fn-prc-refresh's
# carry (books/post-retain-carried), which replaced fn-pidx-sbud-prepare.
# commit-onto-log: the bare copy drops books/owner-log-route too, so the
# owner's log-route names are findings in any loader (health-truth, PRF-359:
# the free-space need reads fn-olr-omax).
LOG_ROUTE_NAMES = ("fn-olr-bounds", "fn-olr-ocfg-order", "fn-olr-ocfg-reserve", "fn-olr-omax")
# host-decisions-2 (packet A): the owner entries' words are
# books/owner-prepare-outcome's (fn-pout-); the host no longer calls
# fn-oiis-prepare-identity, fn-psrv-prepare, fn-psrv-prepare-topic or
# fn-psrv-refusal-kind itself (the fn-pout- entries do).
POUT_NAMES = ("fn-pout-begin", "fn-pout-declare-group", "fn-pout-known-abort",
              "fn-pout-prepare-article", "fn-pout-prepare-consumer",
              "fn-pout-prepare-identity", "fn-pout-prepare-retention",
              "fn-pout-prepare-topic", "fn-pout-refuse-reservation")
BUFFER_FINDINGS = [
    f"included: host/owner-host.lisp uses {name}, defined in "
    "books/owner-log-route.lisp, which host/native/build-dtn.lisp has not "
    "included when it loads host/owner-host.lisp"
    for name in LOG_ROUTE_NAMES] + [
    f"included: host/owner-host.lisp uses {name}, defined in "
    f"{book}, which host/native/build-dtn.lisp has not "
    "included when it loads host/owner-host.lisp"
    for name, book in (
        (("fn-pidx-existing-action", "books/post-identity-index.lisp"),)
        + tuple((n, "books/owner-prepare-outcome.lisp") for n in POUT_NAMES)
        + (("fn-prc-refresh", "books/post-retain-carried.lisp"),
           # prepare-served: the configuration un-stage; its book is
           # dropped with the rest.
           ("fn-psrv-unstage", "books/owner-prepare-served.lisp")))]
# served-readers-cat (catalog step 8): fn-owner-chunk-span-at reads through
# books/served-catalog-chain's fn-scr-ocfg-read-span, which the bare copy
# still reaches, so the served-span finding is gone.
# checkpoint-pipeline (2026-09-26): host/store-node-host.lisp includes
# books/store-checkpoint-tables-reader and books/owner-checkpoint-pipeline
# itself (their closure holds octets-stobj, the buffer and the reader), so
# the bare copy reaches fn-octets, fn-sccr-admit-segment,
# fn-sccr-file-read-bound, fn-sct-load and fn-ockp-setup on its own and
# those findings are gone; the build lists keep the explicit includes.
STORE_NODE_HOST_FINDINGS = []
# The store-node host's duplicate verdict (fn-store-existing-action) is no
# finding: host/store-node-host.lisp includes books/store-reclaim and
# books/acceptance-payload-ref itself (the Python bridge loads that host file
# alone).  fn-rcl-existing-action was retired (PKT-860).
# host/owner-host.lisp names no subject-id-buffer entry: the served POST calls
# the guard-verified fn-sidb-subject-id-bounded from host/native/io.lisp
# (qual-e747dbcc A4), outside the `ld` closure this check reads.
# In build-dtn.lisp fn-octets itself is no finding: it includes
# books/bp-node-rotation-buffer (which includes books/octets-stobj) before it
# loads host/store-node-host.lisp (lane bp-checkpoint-open).
DTN_STORE_NODE_HOST_FINDINGS = STORE_NODE_HOST_FINDINGS[1:]


OWNER_HOST_SELF_INCLUDES = ('(include-book "../books/records-concrete-owner")\n'
                            '(include-book "../books/octets-stobj")\n'
                            '(include-book "../books/store-reclaim-buffer")\n')
# post-identity-index (PRF-191): the book of the two calls that replaced
# fn-rclb-existing-action and fn-pcar-sbud-prepare in the served POST.
# post-alloc-2: the carried obligation-id trie's book (it includes
# post-identity-index, so it is removed with it).
OWNER_HOST_PIDX_INCLUDE = ('(include-book "../books/post-identity-index")\n'
                           '; The retention admission of a POST through a carried obligation-id trie\n'
                           '; (fn-prc-refresh, fn-prc-sbud-prepare; fn-owner-prepare-buffer).\n'
                           '(include-book "../books/post-retain-carried")\n'
                           ';; lane prepare-served: the served decision inside the prepares the host calls\n'
                           ';; (fn-psrv-prepare, fn-psrv-refusal-kind, fn-psrv-prepare-identity,\n'
                           ';; fn-psrv-prepare-topic) and the configuration un-stage (fn-psrv-unstage).\n'
                           '(include-book "../books/owner-prepare-served")\n')
# commit-onto-log: the owner's log-route composites (it includes
# books/records-concrete-owner too, so the bare copy drops it with the rest).
OWNER_HOST_LOG_ROUTE_INCLUDE = ('(include-book "../books/owner-log-route")\n')


# batch AW (signed-post x prepare-served): books/owner-identity-served's
# closure holds owner-prepare-served-ocl and with it the log route, so the
# bare copy drops it too.
OWNER_HOST_IDENTITY_SERVED_INCLUDE = '(include-book "../books/owner-identity-served")\n'
# host-decisions-2 (packet A): the owner entries' words; the book includes
# owner-identity-served, so the bare copy drops it too.
OWNER_HOST_OUTCOME_INCLUDE = '(include-book "../books/owner-prepare-outcome")\n'


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
        assert OWNER_HOST_PIDX_INCLUDE in text
        assert OWNER_HOST_LOG_ROUTE_INCLUDE in text
        assert OWNER_HOST_IDENTITY_SERVED_INCLUDE in text
        assert OWNER_HOST_OUTCOME_INCLUDE in text
        owner.write_text(text.replace(OWNER_HOST_SELF_INCLUDES, "")
                         .replace(OWNER_HOST_PIDX_INCLUDE, "")
                         .replace(OWNER_HOST_LOG_ROUTE_INCLUDE, "")
                         .replace(OWNER_HOST_IDENTITY_SERVED_INCLUDE, "")
                         .replace(OWNER_HOST_OUTCOME_INCLUDE, ""))
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
        self.assertTrue(any("host/native/owner.lisp names "
                            "'fn-native-control-host-refusal-status"
                            in line for line in found), found)

    def test_an_excuse_nothing_needs_is_stale(self):
        omitted = dict(check.DTN_OMITTED)
        reason, allowed = omitted["host/native-control-host.lisp"]
        omitted["host/native-control-host.lisp"] = (
            reason, {**allowed, "fn-native-control-host-liveness": "pretend"})
        found = check.findings(omitted=omitted)
        self.assertEqual(found, ["stale: DTN_OMITTED excuses fn-native-control-host-liveness "
                                 "(host/native-control-host.lisp), which nothing "
                                 "host/native/build-dtn.lisp loads names any more"])

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

    def test_missing_buffer_includes_are_found(self):
        # native-drift-2026-09-25 finding 3: at 32842f50 build-dtn.lisp did
        # not include the octet buffer books host/owner-host.lisp uses, and
        # the DTN image did not build.  host/owner-host.lisp now includes
        # them itself (harness-repair), so the omission is restored in a copy
        # whose owner-host.lisp does not.
        text = self.dtn_text()
        self.assertIn(BUFFER_INCLUDES, text)
        self.assertIn(CHECKPOINT_BUFFER_INCLUDES, text)
        with bare_owner_host() as root:
            found = check.include_findings(
                root, text.replace(BUFFER_INCLUDES, "").replace(CHECKPOINT_BUFFER_INCLUDES, ""))
        self.assertEqual(found, DTN_STORE_NODE_HOST_FINDINGS + BUFFER_FINDINGS)

    def test_include_after_the_ld_is_too_late(self):
        # The order matters: an include after the `ld` does not serve it.
        text = (self.dtn_text().replace(BUFFER_INCLUDES, "").replace(CHECKPOINT_BUFFER_INCLUDES, "")
                + BUFFER_INCLUDES + CHECKPOINT_BUFFER_INCLUDES)
        with bare_owner_host() as root:
            found = check.include_findings(root, text)
        self.assertEqual(len(found), len(DTN_STORE_NODE_HOST_FINDINGS) + len(BUFFER_FINDINGS), found)

    def test_owner_host_declares_its_own_books(self):
        # The same omission in the real tree is no finding: every loader of
        # host/owner-host.lisp gets its books from the file itself.
        text = self.dtn_text().replace(BUFFER_INCLUDES, "")
        self.assertEqual(check.include_findings(ROOT, text), [])

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
