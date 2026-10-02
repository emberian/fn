"""The evidence archive is fail-closed (Codex review r56, findings F1-F11).

After the history rewrite the archive is the ONLY copy of the evidence, so
every reader verifies bytes against the hash the committed index names,
every writer verifies what it publishes (including an object already at its
name) before the index line is written, and an unreadable or mismatched
claim is UNAVAILABLE (exit 3), never absent, never silently older-green.
Each test below reproduces one finding's construction.
"""

from __future__ import annotations

import argparse
import contextlib
import gzip
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import evidence_store as store  # noqa: E402
import evidence_manifests  # noqa: E402

REL = "planning/evidence/manifests/certify-20261002T000000Z-1.json"
OLDER = "planning/evidence/manifests/certify-20261001T000000Z-1.json"
REAL_RUN = subprocess.run


def git(root: Path, *args: str) -> str:
    return REAL_RUN(["git", "-C", str(root), *args], check=True,
                    capture_output=True, text=True).stdout


def init_repo(root: Path) -> None:
    for command in (["init", "-q"], ["config", "user.email", "t@example"],
                    ["config", "user.name", "t"], ["config", "commit.gpgsign", "false"]):
        git(root, *command)


class Sandbox(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.base = Path(self._dir.name).resolve()
        self.root = self.base / "tree"
        self.archive = self.base / "archive"
        self.cache = self.base / "cache"
        (self.root / "planning/evidence/manifests").mkdir(parents=True)
        self._env = mock.patch.dict(os.environ, {
            "FN_EVIDENCE_ARCHIVE": str(self.archive),
            "FN_EVIDENCE_CACHE": str(self.cache)})
        self._env.start()
        store._INDEX.clear()

    def tearDown(self):
        self._env.stop()
        self._dir.cleanup()

    def write(self, rel: str, data: bytes) -> None:
        (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
        (self.root / rel).write_bytes(data)

    def remote(self) -> Path:
        """Point the archive at `box:<dir>` and return the directory."""
        remote = self.base / "remote"
        remote.mkdir(exist_ok=True)
        os.environ["FN_EVIDENCE_ARCHIVE"] = f"box:{remote}"
        return remote

    def fake_box(self, remote: Path, rsync_corrupts: bool = False):
        """rsync copies files; `ssh box CMD` runs CMD here (the real ingest)."""
        def run(command, *args, **kwargs):
            if command[0] == "rsync":
                listing = Path(command[command.index("--files-from") + 1]).read_text()
                source, target = command[-2], command[-1]
                source_dir = Path(source.partition(":")[2] if source.startswith("box:")
                                  else source)
                target_dir = Path(target.partition(":")[2] if target.startswith("box:")
                                  else target)
                for rel in listing.split():
                    src = source_dir / rel
                    if src.is_file():
                        (target_dir / rel).parent.mkdir(parents=True, exist_ok=True)
                        data = src.read_bytes()
                        if rsync_corrupts:
                            data = gzip.compress(b"tampered")
                        (target_dir / rel).write_bytes(data)
                return subprocess.CompletedProcess(command, 0, "", "")
            if command[0] == "ssh":
                return REAL_RUN(["bash", "-c", command[2]],
                                input=kwargs.get("input"), capture_output=True,
                                text=True, check=False)
            return REAL_RUN(command, *args, **kwargs)
        return run


# ---------------------------------------------------------------- F1, F8, F11


class LocalFilesAreVerifiedTests(Sandbox):
    def test_F1_an_indexed_local_file_that_differs_from_the_index_is_an_error(self):
        # r56 F1: index REL at a hash the archive lacks, leave a local green
        # JSON at REL; the reader returned the local bytes as the claim.
        store.write_index(self.root, {REL: ("a" * 64, 20)})
        self.write(REL, b'{"status": "passed"}')
        with self.assertRaises(store.EvidenceMismatch):
            store.read_bytes(self.root, REL)
        self.assertTrue(issubclass(store.EvidenceMismatch, store.EvidenceUnavailable))

    def test_F1_a_matching_local_file_is_indexed_and_an_unindexed_one_is_local(self):
        data = b'{"status": "passed"}'
        self.write(REL, data)
        store.put(self.root, [REL])
        self.assertEqual(store.locate(self.root, REL), (data, "indexed"))
        self.write(OLDER, b"{}")
        self.assertEqual(store.locate(self.root, OLDER), (b"{}", "local"))
        self.assertTrue(store.indexed(self.root, REL))
        self.assertFalse(store.indexed(self.root, OLDER))

    def test_F1_green_check_labels_an_unindexed_local_manifest_unarchived(self):
        import green_check
        manifest = {"run_id": "certify-20261001T000000Z-1", "status": "passed",
                    "requested_books": [], "book_results": {}}
        self.write(OLDER, json.dumps(manifest).encode())
        runs = green_check.manifests(self.root)
        self.assertEqual([(run.run_id, run.archived) for run, _ in runs],
                         [("certify-20261001T000000Z-1", False)])
        # The same bytes, filed: archived.
        store.put(self.root, [OLDER])
        store._INDEX.clear()
        runs = green_check.manifests(self.root)
        self.assertEqual([run.archived for run, _ in runs], [True])
        # A local file that disagrees with its index line stops the audit.
        self.write(OLDER, json.dumps({**manifest, "status": "failed"}).encode())
        with self.assertRaises(store.EvidenceMismatch):
            green_check.manifests(self.root)

    def test_F8_a_mutated_materialization_is_never_returned(self):
        data = b'{"verdict": "passed"}'
        self.write(REL, data)
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        path = store.materialize(self.root, REL)
        self.assertEqual(path.read_bytes(), data)
        path.write_bytes(b'{"verdict": "failed"}')
        # Repaired from the verified object; the mutated file is kept aside.
        self.assertEqual(store.materialize(self.root, REL).read_bytes(), data)
        self.assertTrue(any((self.cache / "quarantine").iterdir()))
        # With no verified source left, it is UNAVAILABLE, not the mutation.
        path.write_bytes(b'{"verdict": "failed"}')
        shutil.rmtree(self.archive)
        with contextlib.suppress(FileNotFoundError):
            shutil.rmtree(self.cache / "objects")
        with self.assertRaises(store.EvidenceUnavailable):
            store.materialize(self.root, REL)
        self.assertEqual(sha, store.sha256_bytes(data))

    def test_F11_a_non_hex_hash_is_refused_and_cannot_escape_the_cache(self):
        evil = "../" * 21 + "x"
        self.assertEqual(len(evil), 64)
        with self.assertRaisesRegex(ValueError, "malformed"):
            store.parse_index(f"{evil} 1 planning/evidence/x.md\n")
        with self.assertRaisesRegex(ValueError, "malformed"):
            store.parse_index(f"{'A' * 64} 1 planning/evidence/x.md\n")
        with self.assertRaises(ValueError):
            store.object_rel(evil)
        for path in ("../x.md", "/etc/passwd", "planning/./x", "planning//x",
                     "planning/evidence/../../x"):
            with self.assertRaisesRegex(ValueError, "malformed", msg=path):
                store.parse_index(f"{'a' * 64} 1 {path}\n")


# ------------------------------------------------------------------------ F2


class UnreadableClaimsAreUnavailableTests(Sandbox):
    def test_F2_an_unreadable_indexed_object_is_unavailable_not_skipped(self):
        self.write(REL, b'{"status": "failed"}')
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        real = Path.read_bytes

        def deny(path):
            if path.name == f"{sha}.gz":
                raise PermissionError(13, "Permission denied", str(path))
            return real(path)
        with mock.patch.object(Path, "read_bytes", deny):
            with self.assertRaises(store.EvidenceUnavailable):
                evidence_manifests.load_archived(self.root, REL)

    def test_F2_indexed_bytes_that_are_not_json_are_unavailable(self):
        self.write(REL, b"{not json")
        store.put(self.root, [REL])
        (self.root / REL).unlink()
        with self.assertRaises(store.EvidenceUnavailable):
            evidence_manifests.load_archived(self.root, REL)

    def test_F2_a_partial_local_draft_is_still_skipped(self):
        self.write(REL, b"{partial")
        self.assertEqual(evidence_manifests.load_archived(self.root, REL), [])


# ------------------------------------------------------------------------ F3


class NamesAreNotBytesTests(Sandbox):
    def test_F3_verify_paths_refuses_an_index_row_whose_bytes_are_missing(self):
        store.write_index(self.root, {"planning/evidence/missing-report.md":
                                      ("a" * 64, 1)})
        problems = store.verify_paths(self.root, ["planning/evidence/missing-report.md",
                                                  "planning/evidence/unindexed.md"])
        self.assertIsInstance(problems["planning/evidence/missing-report.md"],
                              store.EvidenceUnavailable)
        self.assertIsInstance(problems["planning/evidence/unindexed.md"],
                              FileNotFoundError)
        self.write(REL, b"real\n")
        store.put(self.root, [REL])
        (self.root / REL).unlink()
        self.assertEqual(store.verify_paths(self.root, [REL]), {REL: None})

    def test_F3_the_cut_gate_command_checks_bytes_at_a_revision(self):
        init_repo(self.root)
        self.write(REL, b"present\n")
        store.put(self.root, [REL])
        index = store.read_index(self.root)
        index["planning/evidence/missing-report.md"] = ("a" * 64, 1)
        store.write_index(self.root, index)
        (self.root / REL).unlink()
        git(self.root, "add", store.INDEX_REL)
        git(self.root, "commit", "-q", "-m", "index")
        revision = git(self.root, "rev-parse", "HEAD").strip()
        with mock.patch.object(store, "ROOT", self.root):
            out = io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                self.assertEqual(store.main(["verify-paths", "--revision", revision, REL]), 0)
                self.assertEqual(store.main(["verify-paths", "--revision", revision,
                                             "planning/evidence/missing-report.md"]), 3)
                self.assertEqual(store.main(["verify-paths", "--revision", revision,
                                             "planning/evidence/nothing.md"]), 1)

    def test_F3_cut_release_no_longer_accepts_an_index_row_by_name(self):
        text = (TOOLS / "cut_release.sh").read_text()
        self.assertIn("evidence_store.py\" verify-paths --revision", text)
        self.assertNotIn("$0 == p { found = 1 }", text)

    def test_F3_cite_check_reports_an_indexed_citation_without_bytes(self):
        import cite_check
        store.write_index(self.root, {"planning/evidence/missing-report.md":
                                      ("a" * 64, 1),
                                      "planning/evidence/gone/a.md": ("b" * 64, 1)})
        self.write(REL, b"real\n")
        store.put(self.root, [REL])
        (self.root / REL).unlink()
        # A file answers with its own bytes; a directory with its first file's.
        failed = cite_check.unverified_evidence(
            self.root, ["planning/evidence/missing-report.md", REL,
                        "planning/evidence/manifests/", "planning/evidence/gone/",
                        "planning/evidence/gone"])
        self.assertEqual(set(failed), {"planning/evidence/missing-report.md",
                                       "planning/evidence/gone/",
                                       "planning/evidence/gone"})

    def test_F3_check_scaffold_refuses_an_indexed_link_without_bytes(self):
        import check_scaffold
        store.write_index(self.root, {"planning/evidence/missing-report.md":
                                      ("a" * 64, 1)})
        doc = self.root / "docs/x.md"
        doc.parent.mkdir(parents=True)
        doc.write_text("x\n")
        with mock.patch.object(check_scaffold, "ROOT", self.root), \
                mock.patch.object(check_scaffold, "ERRORS", []), \
                mock.patch.object(check_scaffold, "UNAVAILABLE", []):
            check_scaffold.link("../planning/evidence/missing-report.md", doc, "docs/x.md")
            self.assertEqual(len(check_scaffold.UNAVAILABLE), 1)
            self.assertEqual(check_scaffold.ERRORS, [])


# ------------------------------------------------------------------- F4, F5


class PublicationVerifiesTests(Sandbox):
    def test_F4_put_replaces_a_truncated_object_already_at_its_name_locally(self):
        data = b"evidence bytes\n" * 100
        sha = store.sha256_bytes(data)
        target = self.archive / store.object_rel(sha)
        target.parent.mkdir(parents=True)
        target.write_bytes(store.compress(data)[:20])
        self.write(REL, data)
        store.put(self.root, [REL])
        (self.root / REL).unlink()
        self.assertEqual(store.read_bytes(self.root, REL), data)
        self.assertEqual(len(list((self.archive / "quarantine").iterdir())), 1)

    def test_F4_F5_a_remote_put_ingests_verifies_and_replaces_a_bad_object(self):
        remote = self.remote()
        data = b"remote evidence\n"
        sha = store.sha256_bytes(data)
        target = remote / store.object_rel(sha)
        target.parent.mkdir(parents=True)
        target.write_bytes(store.compress(data)[:10])
        self.write(REL, data)
        with mock.patch.object(store.subprocess, "run", side_effect=self.fake_box(remote)):
            store.put(self.root, [REL])
        self.assertEqual(gzip.decompress(target.read_bytes()), data)
        self.assertEqual(len(list((remote / "quarantine").iterdir())), 1)
        self.assertEqual(list((remote / "incoming").iterdir()), [])
        self.assertIn(REL, store.read_index(self.root))

    def test_F5_no_index_line_when_the_box_cannot_read_the_object_back(self):
        remote = self.remote()
        self.write(REL, b"never arrives intact\n")
        with mock.patch.object(store.subprocess, "run",
                               side_effect=self.fake_box(remote, rsync_corrupts=True)):
            with self.assertRaises(store.EvidenceUnavailable):
                store.put(self.root, [REL])
        self.assertEqual(store.read_index(self.root), {})

    def test_F5_objects_and_the_index_are_fsynced(self):
        self.write(REL, b"durable\n")
        with mock.patch.object(os, "fsync", wraps=os.fsync) as fsync:
            store.put(self.root, [REL])
        # object file + its directories (archive) and the index file + directory
        self.assertGreaterEqual(fsync.call_count, 4)


# ------------------------------------------------------------------------ F6


class ConcurrentIndexWritersTests(Sandbox):
    def test_F6_concurrent_add_to_index_loses_no_rows(self):
        script = (
            "import sys; sys.path.insert(0, sys.argv[1]); import evidence_store as s\n"
            "from pathlib import Path\n"
            "root = Path(sys.argv[2]); w = sys.argv[3]\n"
            "for i in range(40):\n"
            "    s.add_to_index(root, {f'planning/evidence/{w}-{i}.md': ('%064x' % i, i)})\n")
        procs = [subprocess.Popen([sys.executable, "-c", script, str(TOOLS),
                                   str(self.root), f"w{n}"]) for n in range(4)]
        for proc in procs:
            self.assertEqual(proc.wait(), 0)
        store._INDEX.clear()
        self.assertEqual(len(store.read_index(self.root)), 160)


# ------------------------------------------------------------------------ F7


class IndexTreeArchivesFirstTests(Sandbox):
    def test_F7_index_tree_write_archives_before_indexing(self):
        init_repo(self.root)
        self.write("planning/evidence/new.log", b"new log\n")
        git(self.root, "add", ".")
        git(self.root, "commit", "-q", "-m", "new")
        with mock.patch.object(store, "ROOT", self.root):
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(store.main(["index-tree", "--write"]), 0)
        sha, _ = store.read_index(self.root)["planning/evidence/new.log"]
        self.assertEqual(gzip.decompress(
            (self.archive / store.object_rel(sha)).read_bytes()), b"new log\n")

    def test_F7_index_tree_write_refuses_when_the_archive_refuses(self):
        init_repo(self.root)
        self.write("planning/evidence/new.log", b"new log\n")
        git(self.root, "add", ".")
        git(self.root, "commit", "-q", "-m", "new")
        remote = self.remote()
        with mock.patch.object(store, "ROOT", self.root), \
                mock.patch.object(store.subprocess, "run",
                                  side_effect=self.fake_box(remote, rsync_corrupts=True)):
            with contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(store.main(["index-tree", "--write"]), 3)
        self.assertEqual(store.read_index(self.root), {})


# ------------------------------------------------------------------------ F9


class FetchVerifiesPresentObjectsTests(Sandbox):
    def test_F9_fetch_all_verifies_and_repairs_a_corrupt_cached_object(self):
        remote = self.remote()
        data = b"good bytes\n"
        sha = store.sha256_bytes(data)
        store.store_object(remote, data)
        store.write_index(self.root, {REL: (sha, len(data))})
        bad = self.cache / store.object_rel(sha)
        bad.parent.mkdir(parents=True)
        bad.write_bytes(gzip.compress(b"wrong"))
        with mock.patch.object(store.subprocess, "run", side_effect=self.fake_box(remote)):
            with mock.patch.object(store, "ROOT", self.root), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(store.main(["fetch", "--all"]), 0)
        self.assertEqual(gzip.decompress(bad.read_bytes()), data)

    def test_F9_fetch_fails_when_a_corrupt_object_has_no_good_source(self):
        data = b"good bytes\n"
        sha = store.sha256_bytes(data)
        store.write_index(self.root, {REL: (sha, len(data))})
        bad = self.archive / store.object_rel(sha)
        bad.parent.mkdir(parents=True)
        bad.write_bytes(gzip.compress(b"wrong"))
        with mock.patch.object(store, "ROOT", self.root), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(store.main(["fetch", "--all"]), 3)


# ----------------------------------------------------------------------- F10


class UnavailableIsDistinctTests(Sandbox):
    def test_F10_sync_add_returns_the_archive_refusal(self):
        args = argparse.Namespace(source=[], add=True, record_lost=False,
                                  list_missing=False)
        run_id = "certify-20261002T000000Z-1"
        with mock.patch.object(evidence_manifests, "cited_run_ids",
                               return_value={run_id: ["x"]}), \
                mock.patch.object(evidence_manifests, "archived", return_value={run_id}), \
                mock.patch.object(evidence_manifests, "local_candidates", return_value={}), \
                mock.patch.object(evidence_manifests, "tracked_manifests",
                                  return_value=set()), \
                mock.patch.object(evidence_manifests, "commit_paths", return_value=3), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(evidence_manifests.cmd_sync(args), 3)

    def test_F10_claim_tools_exit_3_on_unavailable_evidence(self):
        import certified_claims
        import current_view
        import green_check
        boom = store.EvidenceUnavailable("object x did not arrive")
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            with mock.patch.object(green_check, "audit", side_effect=boom):
                self.assertEqual(green_check.main(["--summary"]), 3)
            with mock.patch.object(certified_claims, "audit", side_effect=boom):
                self.assertEqual(certified_claims.main([]), 3)
            with mock.patch.object(current_view, "build", side_effect=boom):
                self.assertEqual(current_view.main(["--check"]), 3)
        self.assertIn("UNAVAILABLE", out.getvalue())


class MigrationLedgersAccumulateTests(Sandbox):
    def test_a_narrower_migration_never_replaces_an_earlier_ledger(self):
        # evidence-out-3: every migrate-history run wrote history-ledger.tsv
        # (or -extra.tsv) and copied it over the archive's, so a one-path run
        # replaced the ledger of the all-history run.
        init_repo(self.root)
        self.write("planning/evidence/a.md", b"a\n")
        self.write("planning/lanes/x.md", b"x\n")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "e")
        self.archive.mkdir()
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), contextlib.redirect_stdout(out):
            self.assertEqual(store.main(["migrate-history", "--path", "planning/lanes"]), 0)
            self.assertEqual(store.main(["migrate-history", "--path", "planning/evidence"]), 0)
        ledgers = sorted(self.cache.glob("history-ledger-extra-*.tsv"))
        self.assertEqual(len(ledgers), 2)
        self.assertEqual({p.read_text().split()[3] for p in ledgers},
                         {"planning/lanes/x.md", "planning/evidence/a.md"})
        self.assertEqual(store.object_bytes(self.root, store.sha256_bytes(b"x\n")), b"x\n")


if __name__ == "__main__":
    unittest.main()
