"""tools/native_reuse.py: when an image run may start from the train's certified tree.

No box and no ACL2: records, a temp git repo, a tree that is `git archive` of
it, and cache entries written the way certs.py publishes them."""
import contextlib
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock
from tests.scratch_git import run as scratch_git

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import acl2_toolchain  # noqa: E402
import certs  # noqa: E402
import native_reuse  # noqa: E402
import proof_artifacts  # noqa: E402

BOX = "hbox"
TOOLCHAIN = "toolchain-identity-1"
BOOKS = {"books/a.lisp": '(in-package "ACL2")\n(defun f (x) x)\n',
         "books/b.lisp": '(in-package "ACL2")\n(include-book "a")\n(defun g (x) x)\n',
         "README": "hello\n"}


def git(repo, *argv):
    return scratch_git(["git", "-C", str(repo), "-c", "commit.gpgsign=false", *argv], check=True, capture_output=True,
                          text=True).stdout.strip()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


class PlanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q", "-b", "lane/x")
        git(self.repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q",
            "--allow-empty", "-m", "c")
        self.rev = git(self.repo, "rev-parse", "HEAD")
        self.remote = "/tank/fn/batch/tree"
        self.state = {"box_run": "run-1"}
        self.record = {"sha": self.rev, "ran_at": self.rev, "box": BOX, "run": "run-1",
                       "certify_id": "cid-1", "known_reds_seen": []}
        self.farm = {"host": BOX, "box_manifest": "passed", "certify_id": "cid-1",
                     "remote_path": self.remote}

    def write(self):
        train, farm = self.repo / "build" / "train", self.repo / "build" / "farm"
        train.mkdir(parents=True, exist_ok=True)
        farm.mkdir(parents=True, exist_ok=True)
        (train / "lane__x.json").write_text(json.dumps(self.state))
        (train / "lane__x.box-step.json").write_text(json.dumps(self.record))
        (farm / "run-1.json").write_text(json.dumps(self.farm))

    def refused(self, fragment, box=BOX):
        self.write()
        with self.assertRaises(native_reuse.Refusal) as caught:
            native_reuse.plan(self.repo, self.rev, box)
        self.assertIn(fragment, str(caught.exception))

    def test_a_consistent_record_set_is_accepted(self):
        self.write()
        got = native_reuse.plan(self.repo, self.rev, BOX)
        self.assertEqual(got["remote_path"], self.remote)
        self.assertEqual((got["run"], got["certify_id"]), ("run-1", "cid-1"))

    def test_box_mismatch(self):
        self.refused("certified on 'hbox'", box="persvati")

    def test_farm_run_on_another_host(self):
        self.farm["host"] = "persvati"
        self.refused("farm run was on")

    def test_sha_not_rev(self):
        self.record["sha"] = "0" * 40
        self.refused("box step ran at 000000000000")

    def test_ran_at_not_rev(self):
        self.record["ran_at"] = "1" * 40
        self.refused("ran_at 111111111111")

    def test_rev_must_be_a_full_sha(self):
        self.write()
        with self.assertRaises(native_reuse.Refusal):
            native_reuse.plan(self.repo, self.rev[:12], BOX)

    def test_box_run_mismatch(self):
        self.state["box_run"] = "run-2"
        self.refused("box_run is 'run-2'")

    def test_known_reds_seen(self):
        self.record["known_reds_seen"] = ["books/red"]
        self.refused("known reds: books/red")

    def test_manifest_not_passed(self):
        self.farm["box_manifest"] = "failed"
        self.refused("manifest is 'failed'")

    def test_manifest_absent(self):
        del self.farm["box_manifest"]
        self.refused("manifest is None")

    def test_certify_id_mismatch(self):
        self.farm["certify_id"] = "cid-2"
        self.refused("certify id 'cid-2'")

    def test_bad_remote_paths(self):
        for bad in ("relative/tree", "/tank/a b", "/tank/$(x)", "/tank/a;b", None):
            with self.subTest(bad=bad):
                self.farm["remote_path"] = bad
                self.refused("not a plain absolute path")

    def test_a_run_name_that_is_a_path_is_refused(self):
        self.record["run"] = "../run-1"
        self.refused("names no farm run")

    def test_missing_records_are_a_refusal_not_a_crash(self):
        with self.assertRaises(native_reuse.Refusal):
            native_reuse.plan(self.repo, self.rev, BOX)


class VerifyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.repo, self.tree, self.cache = base / "repo", base / "tree", base / "cache"
        for path, text in BOOKS.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(text)
        git(self.repo, "init", "-q")
        git(self.repo, "add", ".")
        git(self.repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "c")
        self.rev = git(self.repo, "rev-parse", "HEAD")
        self.tree.mkdir()
        archive = scratch_git(["git", "-C", str(self.repo), "archive", self.rev],
                                 check=True, capture_output=True).stdout
        subprocess.run(["tar", "-x", "-C", str(self.tree)], input=archive, check=True)
        self.expect = base / "expect.json"
        self.assertEqual(native_reuse.main(["expect", "--repo", str(self.repo), "--rev", self.rev,
                                            "--out", str(self.expect)]), 0)
        for name in ("books/a", "books/b"):
            self.certify(name, f"cert of {name}\n".encode())

    def certify(self, name, cert=b"cert\n", port=b"port\n", fasl=b"fasl\n", entry=True):
        """Put the book's cert, port and fasl in the tree and the same bytes in
        the cache at its closure key, as certs.publish stores them."""
        source = self.tree / f"{name}.lisp"
        for suffix, data in ((".cert", cert), (".port", port), (".fasl", fasl)):
            source.with_suffix(suffix).write_bytes(data)
        if not entry:
            return
        key, _ = certs.closure_key(self.tree, name)
        directory = self.cache / key / "entry"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "book.cert").write_bytes(cert)
        (directory / "book.port").write_bytes(port)
        (directory / "book.fasl").write_bytes(fasl)
        (directory / "meta.json").write_text(json.dumps({
            "cert_sha256": sha256(cert), "port_sha256": sha256(port), "has_port": True,
            "fasl_sha256": sha256(fasl), "toolchain_identity": TOOLCHAIN}))

    def verify(self):
        arguments = ["verify", "--root", str(self.tree), "--expect", str(self.expect),
                     "--cache", str(self.cache), "--acl2", "/nowhere/acl2", "--profile", "default"]
        fingerprint = acl2_toolchain.Fingerprint(True, TOOLCHAIN, {}, "")
        out = io.StringIO()
        with mock.patch.object(acl2_toolchain, "fingerprint", return_value=fingerprint), \
                mock.patch.object(proof_artifacts, "profile_roots", return_value=["books/b"]), \
                contextlib.redirect_stdout(out):
            code = native_reuse.main(arguments)
        return code, out.getvalue()

    def test_git_archive_plus_matching_cache_pairs_passes(self):
        code, said = self.verify()
        self.assertEqual(code, 0, said)
        self.assertIn("is the commit", said)

    def test_an_edited_tracked_file(self):
        (self.tree / "README").write_text("edited\n")
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("content differs: README", said)

    def test_a_missing_tracked_file(self):
        (self.tree / "README").unlink()
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("missing: README", said)

    def test_an_extra_source_file(self):
        (self.tree / "books" / "extra.lisp").write_text("(x)\n")
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("not in the commit: books/extra.lisp", said)

    def test_generated_files_and_build_are_not_extra_source(self):
        (self.tree / "build").mkdir()
        (self.tree / "build" / "anything").write_text("x")
        (self.tree / "tools").mkdir()
        (self.tree / "tools" / "__pycache__").mkdir()
        (self.tree / "tools" / "__pycache__" / "m.pyc").write_bytes(b"x")
        code, said = self.verify()
        self.assertEqual(code, 0, said)

    def test_a_missing_certificate(self):
        (self.tree / "books" / "a.cert").unlink()
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("no certificate: books/a", said)

    def test_a_certificate_whose_bytes_differ_from_the_cache_entry(self):
        (self.tree / "books" / "b.cert").write_bytes(b"other bytes\n")
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("certificate not a cache pair for this closure and toolchain", said)
        self.assertIn("books/b", said)

    def test_no_cache_entry_at_the_key(self):
        shutil.rmtree(self.cache / certs.closure_key(self.tree, "books/a")[0])
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("(0 entries at the key): books/a", said)

    def test_an_entry_of_another_toolchain_is_not_a_pair(self):
        for meta in self.cache.glob("*/entry/meta.json"):
            data = json.loads(meta.read_text())
            data["toolchain_identity"] = "another"
            meta.write_text(json.dumps(data))
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("certificate not a cache pair", said)

    def test_a_port_that_differs_from_the_entrys(self):
        (self.tree / "books" / "a.port").write_bytes(b"changed\n")
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("port or compiled file differs from the cache pair: books/a", said)

    def test_a_missing_compiled_file(self):
        (self.tree / "books" / "a.fasl").unlink()
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("port or compiled file differs from the cache pair: books/a", said)

    def test_an_included_book_is_checked_too(self):
        # the profile names books/b only; books/a is in its include closure
        (self.tree / "books" / "a.cert").write_bytes(b"other\n")
        code, said = self.verify()
        self.assertEqual(code, 1)
        self.assertIn("books/a", said)

    def test_an_unqualified_launcher_refuses(self):
        out = io.StringIO()
        fingerprint = acl2_toolchain.Fingerprint(False, None, {}, "no such launcher")
        with mock.patch.object(acl2_toolchain, "fingerprint", return_value=fingerprint), \
                contextlib.redirect_stdout(out):
            code = native_reuse.main(["verify", "--root", str(self.tree), "--expect",
                                      str(self.expect), "--cache", str(self.cache),
                                      "--acl2", "/x", "--profile", "default"])
        self.assertEqual(code, 1)
        self.assertIn("unqualified ACL2 launcher", out.getvalue())


class ClaimTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.dead = subprocess.Popen([sys.executable, "-c", "pass"])
        self.dead.wait()  # a pid that has exited and been reaped

    def test_the_first_claim_is_taken_and_a_second_while_the_pid_lives_is_refused(self):
        self.assertEqual(native_reuse.claim(self.root, "/s/main"), "")
        native_reuse.claim(self.root, "/s/main", pid=os.getpid())
        with self.assertRaises(native_reuse.Refusal) as caught:
            native_reuse.claim(self.root, "/s/heap")
        self.assertIn("the train tree is claimed by /s/main", str(caught.exception))

    def test_a_claim_whose_pid_is_dead_is_taken_over_and_said(self):
        native_reuse.claim(self.root, "/s/main")
        native_reuse.claim(self.root, "/s/main", pid=self.dead.pid)
        note = native_reuse.claim(self.root, "/s/heap")
        self.assertIn("took over the stale claim of /s/main", note)
        owner = (self.root / "build" / "native-reuse.claim" / "owner").read_text().strip()
        self.assertEqual(owner, "/s/heap")
        self.assertFalse((self.root / "build" / "native-reuse.claim" / "pid").exists())

    def test_a_claim_with_no_pid_yet_holds_until_it_is_old(self):
        native_reuse.claim(self.root, "/s/main")
        with self.assertRaises(native_reuse.Refusal):
            native_reuse.claim(self.root, "/s/heap")
        later = __import__("time").time() + native_reuse.PENDING_SECONDS + 5
        self.assertIn("took over", native_reuse.claim(self.root, "/s/heap", now=later))

    def test_a_pid_is_recorded_only_on_the_owners_own_claim(self):
        native_reuse.claim(self.root, "/s/main")
        with self.assertRaises(native_reuse.Refusal):
            native_reuse.claim(self.root, "/s/other", pid=1)

    def test_the_cli_exits_1_naming_the_holder(self):
        out = io.StringIO()
        base = ["claim", "--root", str(self.root)]
        with contextlib.redirect_stdout(out):
            self.assertEqual(native_reuse.main([*base, "--owner", "/s/main"]), 0)
            self.assertEqual(native_reuse.main([*base, "--owner", "/s/main", "--pid", str(os.getpid())]), 0)
            self.assertEqual(native_reuse.main([*base, "--owner", "/s/heap"]), 1)
        self.assertIn("the train tree is claimed by /s/main", out.getvalue())

    def test_the_claim_does_not_disturb_the_trees_verify(self):
        native_reuse.claim(self.root, "/s/main")
        self.assertEqual(native_reuse.tree_differences(self.root, {}), [])


if __name__ == "__main__":
    unittest.main()
