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
        self.assertTrue(issubclass(store.EvidenceMismatch, store.EvidenceRefused))

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

    def test_F2_indexed_bytes_that_are_not_json_are_refused(self):
        # Verified bytes that are not a manifest: there, and refused (r61 F3).
        self.write(REL, b"{not json")
        store.put(self.root, [REL])
        (self.root / REL).unlink()
        with self.assertRaises(store.EvidenceRefused):
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
            self.assertEqual(store.main(["fetch", "--all"]), 4)  # bytes there and wrong: refused (r61 F3)


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



# ===================================================================== r61
# Codex review r61 (11/11 confirmed) blocked the history rewrite.  Each test
# below reproduces one r61 finding against evidence-out-3 41ec96a81.


def commit_all(root: Path, message: str) -> str:
    git(root, "add", "-A")
    git(root, "commit", "-q", "--allow-empty", "-m", message)
    return git(root, "rev-parse", "HEAD").strip()


def deflate_corrupt(data: bytes) -> bytes:
    """A gzip stream whose DEFLATE block type is invalid: zlib.error, not OSError."""
    body = store.compress(data)
    return body[:10] + b"\x07" + body[11:]


class HistoryWalkTests(Sandbox):
    """r61 F11: the path-limited `rev-list --objects` walk simplifies history."""

    def merged_away(self) -> tuple[str, str]:
        """A blob version that lives only on a side branch merged with `-s ours`
        and then deleted: every simplified walk prunes the side commit."""
        init_repo(self.root)
        self.write("planning/evidence/f.md", b"v1\n")
        commit_all(self.root, "A")
        main = git(self.root, "symbolic-ref", "--short", "HEAD").strip()
        git(self.root, "checkout", "-q", "-b", "side")
        self.write("planning/evidence/f.md", b"v2, only on the side branch\n")
        commit_all(self.root, "B")
        lost = git(self.root, "rev-parse", "HEAD:planning/evidence/f.md").strip()
        git(self.root, "checkout", "-q", main)
        self.write("other.txt", b"c\n")
        commit_all(self.root, "C")
        git(self.root, "merge", "-q", "-s", "ours", "--no-edit", "side")
        git(self.root, "branch", "-q", "-D", "side")
        return lost, main

    def test_F11_history_blobs_lists_a_version_simplification_prunes(self):
        lost, _ = self.merged_away()
        simplified = git(self.root, "rev-list", "--objects", "--all", "--",
                         "planning/evidence")
        self.assertNotIn(lost, simplified)  # the r61 construction holds
        self.assertIn(lost, store.history_blobs(self.root, ["--all"]))

    def test_F11_history_check_reports_it_missing_and_migrate_archives_it(self):
        lost, _ = self.merged_away()
        self.archive.mkdir()
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), contextlib.redirect_stdout(out):
            self.assertEqual(store.main(["history-check", "--all-refs"]), 1)
            self.assertEqual(store.main(["migrate-history", "--all-refs"]), 0)
            self.assertEqual(store.main(["history-check", "--all-refs"]), 0)
        data = git(self.root, "cat-file", "blob", lost).encode()
        self.assertEqual(store.object_bytes(self.root, store.sha256_bytes(data)), data)


RULES = """planning/evidence
glob:LANEDUMP*.md
glob:planning/backlog-*
regex:^planning/handoff-(?!keep\\.md$)[^/]*$
planning/swarm-board.md
"""


class RewriteRulesTests(Sandbox):
    """r61 F7/Q7/F8: every rule of the rewrite list, expanded over all refs."""

    def setUp(self):
        super().setUp()
        import evidence_history
        self.history = evidence_history
        init_repo(self.root)
        self.write("planning/evidence/a.md", b"a\n")
        self.write("LANEDUMP-old.md", b"lane dump\n")
        self.write("docs/LANEDUMP-kept.md", b"not top level\n")
        self.write("planning/backlog-1.md", b"backlog v1\n")
        self.write("planning/handoff-x.md", b"handoff\n")
        self.write("planning/handoff-keep.md", b"kept handoff\n")
        self.write("planning/swarm-board.md", b"board\n")
        self.write("planning/swarm-board.md.bak", b"not the literal\n")
        commit_all(self.root, "one")
        self.write("planning/backlog-1.md", b"backlog v2\n")
        (self.root / "LANEDUMP-old.md").unlink()
        commit_all(self.root, "two")
        self.rules_file = self.base / "rules.txt"
        self.rules_file.write_text(RULES)
        self.archive.mkdir()

    def run_complete(self, *extra: str) -> tuple[int, str]:
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = self.history.main(["complete", "--rules", str(self.rules_file), *extra])
        return code, out.getvalue()

    def test_F7_rules_match_as_filter_repo_does(self):
        rules = self.history.load_rules(self.rules_file)
        snapshot = self.history.snapshot_refs(self.root)
        per_rule = self.history.rule_blobs(self.root, rules, snapshot)
        paths = {rule: sorted(set(found.values())) for rule, found in per_rule.items()}
        self.assertEqual(paths["planning/evidence"], ["planning/evidence/a.md"])
        self.assertEqual(paths["glob:LANEDUMP*.md"], ["LANEDUMP-old.md"])  # deleted, still history
        self.assertEqual(len(per_rule["glob:planning/backlog-*"]), 2)       # both versions
        self.assertEqual(paths["regex:^planning/handoff-(?!keep\\.md$)[^/]*$"],
                         ["planning/handoff-x.md"])
        self.assertEqual(paths["planning/swarm-board.md"], ["planning/swarm-board.md"])

    def test_F7_complete_migrates_every_rule_and_verifies_canonically(self):
        code, out = self.run_complete()
        self.assertEqual(code, 1, out)           # nothing archived yet
        summary = self.base / "summary.json"
        code, out = self.run_complete("--migrate", "--write", str(summary))
        self.assertEqual(code, 0, out)
        pinned = json.loads(summary.read_text())
        self.assertEqual(pinned["missing"], 0)
        self.assertEqual(pinned["archived_verified"], pinned["blobs"])
        self.assertEqual(pinned["blobs"], 6)      # a, lanedump, backlog x2, handoff-x, board
        self.assertEqual(pinned["head"], git(self.root, "rev-parse", "HEAD").strip())
        self.assertTrue(pinned["refs"])
        self.assertEqual(pinned["rules"]["glob:planning/backlog-*"]["blobs"], 2)
        # One object moved to the wrong shard: no longer archived.
        sha = store.sha256_bytes(b"backlog v1\n")
        good = self.archive / store.object_rel(sha)
        wrong = self.archive / "objects" / "zz" / good.name
        wrong.parent.mkdir(parents=True)
        os.replace(good, wrong)
        code, out = self.run_complete()
        self.assertEqual(code, 1, out)
        self.assertIn(sha, out)
        # Corrupt bytes at the canonical name: refused (4), not absent.
        good.write_bytes(deflate_corrupt(b"backlog v1\n"))
        code, out = self.run_complete()
        self.assertEqual(code, 4, out)

    def test_F8_the_committed_completeness_summary_is_pinned_and_complete(self):
        pinned = json.loads((TOOLS.parent / "planning/evidence-history-completeness.json")
                            .read_text())
        self.assertEqual(pinned["missing"], 0)
        self.assertEqual(pinned["bad"], 0)
        self.assertEqual(pinned["archived_verified"], pinned["blobs"])
        self.assertRegex(pinned["head"], r"^[0-9a-f]{40}$")
        self.assertGreater(len(pinned["refs"]), 100)
        for rule in (TOOLS.parent / "planning/history-rewrite-paths.txt").read_text().splitlines():
            if rule and not rule.startswith("#"):
                self.assertIn(rule, pinned["rules"])


class CanonicalShardTests(Sandbox):
    """r61 F5: verify matched objects by file name, ignoring the shard."""

    def test_F5_verify_archive_refuses_an_object_in_the_wrong_shard(self):
        data = b"evidence\n"
        self.write(REL, data)
        sha, _ = store.put(self.root, [REL])[REL]
        good = self.archive / store.object_rel(sha)
        wrong = self.archive / "objects" / "zz" / good.name
        wrong.parent.mkdir(parents=True)
        os.replace(good, wrong)
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertNotEqual(store.main(["verify"]), 0)
            self.assertNotEqual(store.main(["verify", "--archive"]), 0)
        self.assertNotIn(sha, store.archive_listing())


class DurabilityTests(Sandbox):
    """r61 F1: barrier failures were swallowed; a present object was not synced."""

    def test_F1_a_failed_directory_fsync_is_an_error(self):
        import stat as stat_module
        real = os.fsync

        def fsync(fd):
            if stat_module.S_ISDIR(os.fstat(fd).st_mode):
                raise OSError(5, "Input/output error")
            return real(fd)
        with mock.patch.object(os, "fsync", side_effect=fsync):
            with self.assertRaises(store.EvidenceUnavailable):
                store.store_object(self.archive, b"durable?\n")

    def test_F1_an_already_present_object_is_synced_before_it_is_reported(self):
        import evidence_ingest
        data = b"present but maybe unsynced\n"
        sha = store.sha256_bytes(data)
        target = self.archive / store.object_rel(sha)
        target.parent.mkdir(parents=True)
        target.write_bytes(store.compress(data))
        synced: list[str] = []
        real = os.fsync

        def record(fd):
            import stat as stat_module
            synced.append("dir" if stat_module.S_ISDIR(os.fstat(fd).st_mode) else "file")
            return real(fd)
        with mock.patch.object(os, "fsync", side_effect=record):
            self.assertEqual(evidence_ingest.place(self.archive, sha, store.compress(data)),
                             "present")
        self.assertIn("file", synced)
        self.assertIn("dir", synced)

    def test_F1_new_shard_directories_are_synced_into_their_parents(self):
        import evidence_ingest
        data = b"fresh archive\n"
        sha = store.sha256_bytes(data)
        opened: list[str] = []
        real_open = os.open

        def track(path, flags, *args, **kwargs):
            opened.append(os.fspath(path))
            return real_open(path, flags, *args, **kwargs)
        with mock.patch.object(os, "open", side_effect=track):
            evidence_ingest.place(self.archive, sha, store.compress(data))
        # the archive root (holding the new objects/) and objects/ (holding the shard)
        self.assertIn(str(self.archive), opened)
        self.assertIn(str(self.archive / "objects"), opened)


class RefusedIsNotUnavailableTests(Sandbox):
    """r61 F3: a proven-bad hash and an absent object had one exception and one exit."""

    def test_F3_mismatch_and_corruption_are_refused_absence_is_unavailable(self):
        self.assertFalse(issubclass(store.EvidenceMismatch, store.EvidenceUnavailable))
        self.assertFalse(issubclass(store.EvidenceRefused, store.EvidenceUnavailable))
        self.write(REL, b"bytes\n")
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        (self.archive / store.object_rel(sha)).write_bytes(gzip.compress(b"other\n"))
        with self.assertRaises(store.EvidenceRefused):
            store.read_bytes(self.root, REL)
        (self.archive / store.object_rel(sha)).unlink()
        with self.assertRaises(store.EvidenceUnavailable):
            store.read_bytes(self.root, REL)

    def test_F3_verify_paths_exits_4_refused_3_unavailable_1_not_indexed(self):
        present, gone = REL, OLDER
        self.write(present, b"corrupted later\n")
        self.write(gone, b"lost later\n")
        entries = store.put(self.root, [present, gone])
        for rel in (present, gone):
            (self.root / rel).unlink()
        (self.archive / store.object_rel(entries[present][0])).write_bytes(
            gzip.compress(b"wrong\n"))
        (self.archive / store.object_rel(entries[gone][0])).unlink()
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(store.main(["verify-paths", present]), 4)
            self.assertEqual(store.main(["verify-paths", gone]), 3)
            self.assertEqual(store.main(["verify-paths", "planning/evidence/no.md"]), 1)

    def cut_gate(self, gate: str, py_exit: dict[str, int], checklist: str = "") -> tuple[int, str]:
        """Run cut_release.sh's real `gate`, `keep34` and gate function (cut
        out of the script by name) with PY a stub whose exit depends on its
        arguments; return (exit, verdict file)."""
        text = (TOOLS / "cut_release.sh").read_text()
        functions = []
        for name in ("gate", "keep34", gate):
            lines = text.splitlines()
            start = next(i for i, line in enumerate(lines) if line.startswith(f"{name}() {{"))
            end = start if lines[start].rstrip().endswith("}") else next(
                i for i in range(start, len(lines)) if lines[i] == "}")
            functions.append("\n".join(lines[start:end + 1]))
        stub = self.base / "py"
        stub.write_text("#!/bin/sh\ncase \"$*\" in\n" + "".join(
            f"  *{key}*) exit {code} ;;\n" for key, code in py_exit.items())
            + "esac\nexit 0\n")
        stub.chmod(0o755)
        script = self.base / "gate.sh"
        out = self.base / "out"
        out.mkdir(exist_ok=True)
        script.write_text("\n".join([
            "FROM=0 TO=99 DRY=no FIRST_RED= SKIPS=", f"OUT={out}", f"V={out}/verdict.txt",
            f"PY={stub}", f"ROOT={TOOLS.parent}", "REV=HEAD CHECKLIST=checklist.md",
            "stamp() { echo now; }", *functions, f"gate 05 x {gate}", "echo passed"]))
        done = REAL_RUN(["sh", str(script)], cwd=self.root if checklist else self.base,
                        capture_output=True, text=True)
        verdict = (out / "verdict.txt").read_text() if (out / "verdict.txt").exists() else ""
        return done.returncode, verdict

    def test_F3_the_cut_closure_gate_keeps_3_and_4_distinct_from_red(self):
        for code, word in ((3, "UNAVAILABLE"), (4, "REFUSED"), (1, "RED"), (2, "RED")):
            rc, verdict = self.cut_gate("g_closure", {"green_check": code})
            self.assertEqual(rc, 1 if word == "RED" else code, verdict)
            self.assertIn(f"VERDICT {word} at 05 x", verdict)
        rc, verdict = self.cut_gate("g_closure", {})
        self.assertEqual(rc, 0, verdict)

    def test_F3_the_cut_fundamentals_gate_keeps_3_and_4_distinct(self):
        init_repo(self.root)
        (self.root / "checklist.md").write_text(
            "<!-- fundamentals -->\n| F1 | thing | bar | MET | planning/evidence/x.md |\n"
            "<!-- end fundamentals -->\n")
        git(self.root, "add", "checklist.md")
        git(self.root, "commit", "-q", "-m", "c")
        for code, word in ((3, "UNAVAILABLE"), (4, "REFUSED"), (1, "RED")):
            rc, verdict = self.cut_gate("g_fundamentals", {"verify-paths": code}, checklist="y")
            self.assertEqual(rc, code, verdict)
            self.assertIn(f"VERDICT {word} at 05 x", verdict)
        # An open row beside a refused one: still REFUSED, never RED (r66 F5).
        (self.root / "checklist.md").write_text(
            "<!-- fundamentals -->\n| F1 | thing | bar | MET | planning/evidence/x.md |\n"
            "| F2 | other | bar | OPEN | none |\n<!-- end fundamentals -->\n")
        git(self.root, "commit", "-q", "-am", "open row")
        rc, verdict = self.cut_gate("g_fundamentals", {"verify-paths": 4}, checklist="y")
        self.assertEqual(rc, 4, verdict)
        self.assertIn("VERDICT REFUSED at 05 x", verdict)

    def test_F3_claim_tools_exit_4_on_refused_evidence(self):
        import certified_claims
        import current_view
        import green_check
        boom = store.EvidenceMismatch("x: the working-tree file differs")
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            with mock.patch.object(green_check, "audit", side_effect=boom):
                self.assertEqual(green_check.main(["--summary"]), 4)
            with mock.patch.object(certified_claims, "audit", side_effect=boom):
                self.assertEqual(certified_claims.main([]), 4)
            with mock.patch.object(current_view, "build", side_effect=boom):
                self.assertEqual(current_view.main(["--check"]), 4)
        self.assertIn("REFUSED", out.getvalue())


class DeflateCorruptionTests(Sandbox):
    """r61 F4: an invalid DEFLATE block raised zlib.error past every handler."""

    def test_F4_a_reader_refuses_invalid_deflate(self):
        data = b"abc" * 50
        self.write(REL, data)
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        (self.archive / store.object_rel(sha)).write_bytes(deflate_corrupt(data))
        with self.assertRaises(store.EvidenceRefused):
            store.read_bytes(self.root, REL)

    def test_F4_put_quarantines_and_replaces_an_invalid_deflate_object(self):
        data = b"abc" * 50
        sha = store.sha256_bytes(data)
        target = self.archive / store.object_rel(sha)
        target.parent.mkdir(parents=True)
        target.write_bytes(deflate_corrupt(data))
        self.write(REL, data)
        store.put(self.root, [REL])
        self.assertEqual(gzip.decompress(target.read_bytes()), data)
        self.assertEqual(len(list((self.archive / "quarantine").iterdir())), 1)

    def test_F4_fetch_repairs_an_invalid_deflate_cached_object(self):
        remote = self.remote()
        data = b"abc" * 50
        sha = store.sha256_bytes(data)
        store.store_object(remote, data)
        store.write_index(self.root, {REL: (sha, len(data))})
        bad = self.cache / store.object_rel(sha)
        bad.parent.mkdir(parents=True)
        bad.write_bytes(deflate_corrupt(data))
        with mock.patch.object(store.subprocess, "run", side_effect=self.fake_box(remote)):
            self.assertEqual(store.read_bytes(self.root, REL), data)


class IndexLockTests(Sandbox):
    """r61 F6: the index lock lived under the (overridable) cache directory."""

    def test_F6_the_lock_is_keyed_on_the_index_not_the_cache(self):
        first = store.index_lock_path(self.root)
        with mock.patch.dict(os.environ, {"FN_EVIDENCE_CACHE": str(self.base / "other")}):
            self.assertEqual(store.index_lock_path(self.root), first)
        self.assertTrue(first.resolve().is_relative_to(self.root.resolve()))

    def test_F6_writers_with_different_caches_lose_no_rows(self):
        script = (
            "import sys; sys.path.insert(0, sys.argv[1]); import evidence_store as s\n"
            "from pathlib import Path\n"
            "root = Path(sys.argv[2]); w = sys.argv[3]\n"
            "for i in range(40):\n"
            "    s.add_to_index(root, {f'planning/evidence/{w}-{i}.md': ('%064x' % i, i)})\n")
        procs = [subprocess.Popen([sys.executable, "-c", script, str(TOOLS),
                                   str(self.root), f"w{n}"],
                                  env={**os.environ,
                                       "FN_EVIDENCE_CACHE": str(self.base / f"cache{n}")})
                 for n in range(4)]
        for proc in procs:
            self.assertEqual(proc.wait(), 0)
        store._INDEX.clear()
        self.assertEqual(len(store.read_index(self.root)), 160)


class LocalShadowTests(Sandbox):
    """r61 F2: a plain local file answered an indexed citation or link."""

    def shadowed(self) -> str:
        rel = "planning/evidence/report.md"
        store.write_index(self.root, {rel: (store.sha256_bytes(b"the filed report\n"), 17)})
        self.write(rel, b"different, untracked bytes\n")
        return rel

    def test_F2_cite_check_does_not_accept_a_local_shadow(self):
        import cite_check
        rel = self.shadowed()
        init_repo(self.root)
        self.write("docs/x.md", f"See `{rel}`.\n".encode())
        git(self.root, "add", "docs/x.md", store.INDEX_REL)
        git(self.root, "commit", "-q", "-m", "cite")
        out = io.StringIO()
        with mock.patch.object(cite_check, "ROOT", self.root), contextlib.redirect_stdout(out):
            code = cite_check.main(["--json", "--strict"])
        report = json.loads(out.getvalue())
        self.assertIn(rel, {f["token"] for f in report["findings"]})
        self.assertNotEqual(code, 0)

    def test_F2_check_scaffold_link_does_not_accept_a_local_shadow(self):
        import check_scaffold
        rel = self.shadowed()
        doc = self.root / "docs/x.md"
        doc.parent.mkdir(parents=True)
        doc.write_text("x\n")
        with mock.patch.object(check_scaffold, "ROOT", self.root), \
                mock.patch.object(check_scaffold, "ERRORS", []), \
                mock.patch.object(check_scaffold, "REFUSED", []), \
                mock.patch.object(check_scaffold, "UNAVAILABLE", []):
            check_scaffold.link(f"../{rel}", doc, "docs/x.md")
            self.assertEqual(len(check_scaffold.REFUSED), 1)
            self.assertEqual(check_scaffold.ERRORS + check_scaffold.UNAVAILABLE, [])


class SchedulerReadsVerifiedTests(Sandbox):
    """r61 F9: chain_schedule preferred plain local manifests; a cold cache raised."""

    def manifest(self, wall: float) -> bytes:
        return json.dumps({"hostname": "hbox", "cpu_count": 16,
                           "book_wall_seconds": {"books/a": wall}}).encode()

    def patched(self):
        import chain_schedule
        history = self.root / "planning/evidence/manifests"
        return chain_schedule, mock.patch.multiple(chain_schedule, ROOT=self.root,
                                                   HISTORY=history)

    def test_F9_a_modified_local_indexed_manifest_is_not_read(self):
        chain_schedule, patch = self.patched()
        rel = "planning/evidence/manifests/certify-20261002T000000Z-1.json"
        self.write(rel, self.manifest(10.0))
        store.put(self.root, [rel])
        self.write(rel, self.manifest(99999.0))
        with patch:
            entries = chain_schedule.history_entries(chain_schedule.HISTORY)
            values = chain_schedule.summaries(entries, None)
        self.assertNotIn("99999", json.dumps(values))

    def test_F9_a_cold_cache_unavailable_manifest_does_not_raise(self):
        chain_schedule, patch = self.patched()
        rel = "planning/evidence/manifests/certify-20261002T000000Z-1.json"
        store.write_index(self.root, {rel: ("c" * 64, 10)})
        with patch, contextlib.redirect_stderr(io.StringIO()):
            entries = chain_schedule.history_entries(chain_schedule.HISTORY)
            self.assertEqual(chain_schedule.summaries(entries, None), [None])


class ManifestCheckReadsBytesTests(Sandbox):
    """r61 F10: `evidence_manifests check` counted an indexed NAME as resolvable."""

    def test_F10_check_does_not_count_a_lost_object_resolvable(self):
        run_id = "certify-20261002T000000Z-1"
        rel = f"planning/evidence/manifests/{run_id}.json"
        store.write_index(self.root, {rel: ("d" * 64, 10)})
        args = argparse.Namespace(strict=False, report_only=False, list_missing=False)
        out = io.StringIO()
        with mock.patch.object(evidence_manifests, "ROOT", self.root), \
                mock.patch.object(evidence_manifests, "cited_run_ids",
                                  return_value={run_id: ["books/x.lisp"]}), \
                mock.patch.object(evidence_manifests, "lost_run_ids", return_value={}), \
                mock.patch.object(evidence_manifests, "local_candidates", return_value={}), \
                mock.patch.object(evidence_manifests, "git", return_value=""), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = evidence_manifests.cmd_check(args)
        self.assertIn("cited and resolvable: 0", out.getvalue())
        self.assertEqual(code, 3)



# ===================================================================== r65
# Codex review r65 on 28e18380c (liaison-verified).


class R65RulesAndScopeTests(Sandbox):
    def setUp(self):
        super().setUp()
        import evidence_history
        self.history = evidence_history

    def test_F2_a_glob_not_ending_in_star_drops_directory_descendants(self):
        rules = self.history.parse_rules("glob:LANEDUMP*.md\nglob:planning/x/\nglob:a*\n")
        lanedump, slash, star = rules
        self.assertTrue(lanedump.matches("LANEDUMP-a.md"))
        self.assertTrue(lanedump.matches("LANEDUMP-a.md/inner.txt"))   # filter-repo's <glob>/*
        self.assertTrue(slash.matches("planning/x/y"))                 # <glob>* after a slash
        self.assertFalse(star.matches("b/a"))

    def test_scope_a_commit_named_only_by_a_reflog_is_measured(self):
        init_repo(self.root)
        self.write("planning/evidence/a.md", b"kept\n")
        commit_all(self.root, "one")
        self.write("planning/evidence/a.md", b"amended away, reflog only\n")
        commit_all(self.root, "two")
        lost = git(self.root, "rev-parse", "HEAD:planning/evidence/a.md").strip()
        git(self.root, "reset", "-q", "--hard", "HEAD~1")
        self.assertNotIn(lost, git(self.root, "rev-list", "--objects", "--all"))
        rules = self.history.parse_rules("planning/evidence\n")
        found = self.history.union(self.history.rule_blobs(
            self.root, rules, self.history.snapshot_refs(self.root)))
        self.assertIn(lost, found)

    def test_drift_from_the_pinned_summary_is_refused(self):
        init_repo(self.root)
        self.write("planning/evidence/a.md", b"a\n")
        commit_all(self.root, "one")
        rules = self.base / "rules.txt"
        rules.write_text("planning/evidence\n")
        self.archive.mkdir()
        pin = self.base / "pin.json"

        def run(*extra):
            out = io.StringIO()
            with mock.patch.object(store, "ROOT", self.root), \
                    contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                return self.history.main(["complete", "--rules", str(rules), *extra]), \
                    out.getvalue()
        self.assertEqual(run("--migrate", "--write", str(pin))[0], 0)
        self.assertEqual(json.loads(pin.read_text())["index"]["rows"], 0)
        self.write("docs/unrelated.md", b"moves a ref, drops nothing new\n")
        commit_all(self.root, "two")
        self.assertEqual(run("--check", str(pin))[0], 0)
        self.write("planning/evidence/b.md", b"filed the old way\n")
        commit_all(self.root, "three")
        code, out = run("--migrate", "--check", str(pin))
        self.assertEqual(code, 1, out)       # archived now, but not what was pinned
        self.assertIn("DRIFT dropped-blob set", out)

    def test_index_rows_are_measured_in_the_archive(self):
        init_repo(self.root)
        self.write(REL, b"filed\n")
        store.put(self.root, [REL], publish=False)   # indexed, never archived
        (self.root / REL).unlink()
        commit_all(self.root, "index")
        rules = self.base / "rules.txt"
        rules.write_text("planning/evidence\n")
        self.archive.mkdir()
        out = io.StringIO()
        with mock.patch.object(store, "ROOT", self.root), contextlib.redirect_stdout(out):
            self.assertEqual(self.history.main(["complete", "--rules", str(rules)]), 1)
        self.assertIn("INDEX ROW NOT ARCHIVED+VERIFIED", out.getvalue())


class R65DurabilityTests(Sandbox):
    def test_F3_every_placement_syncs_the_archive_root_and_its_parent(self):
        import evidence_ingest
        data = b"into an existing shard\n"
        sha = store.sha256_bytes(data)
        (self.archive / store.object_rel(sha)).parent.mkdir(parents=True)
        opened: list[str] = []
        real_open = os.open

        def track(path, flags, *args, **kwargs):
            opened.append(os.fspath(path))
            return real_open(path, flags, *args, **kwargs)
        for _ in range(2):          # placed, then present: both sync the chain
            opened.clear()
            with mock.patch.object(os, "open", side_effect=track):
                evidence_ingest.place(self.archive, sha, store.compress(data))
            self.assertIn(str(self.archive), opened)
            self.assertIn(str(self.archive.parent), opened)
            self.assertIn(str(self.archive / "objects"), opened)


class R65OutcomesTests(Sandbox):
    def test_F4_check_scaffold_keeps_3_and_4(self):
        import check_scaffold
        self.assertEqual(check_scaffold.exit_status([], [], []), 0)
        self.assertEqual(check_scaffold.exit_status([], [], ["u"]), 3)
        self.assertEqual(check_scaffold.exit_status(["e"], [], ["u"]), 1)
        self.assertEqual(check_scaffold.exit_status(["e"], ["r"], ["u"]), 4)

    def test_F4_scenario_implementation_refuses_a_mismatched_record(self):
        import check_scaffold
        record = "planning/evidence/run.md"
        log = "planning/evidence/run.log"
        self.write("tests/test_x.py", b"class Case: pass\n")
        self.write(log, b"tests.test_x Case ok\n")
        self.write(record, b"test_x ran\n")
        store.put(self.root, [log, record], publish=False)
        self.write(record, b"edited after filing\n")
        entry = {"status": "implemented", "implementation": {
            "test": "tests.test_x", "cases": ["Case"], "native": False,
            "log": log, "record": record}}
        with mock.patch.object(check_scaffold, "ROOT", self.root), \
                mock.patch.object(check_scaffold, "ERRORS", []), \
                mock.patch.object(check_scaffold, "REFUSED", []), \
                mock.patch.object(check_scaffold, "UNAVAILABLE", []):
            check_scaffold.scenario_implementation("SCN-001", entry)
            self.assertEqual(len(check_scaffold.REFUSED), 1, check_scaffold.ERRORS)

    def test_F5_a_cached_summary_never_stands_in_for_missing_bytes(self):
        import chain_schedule
        history = self.root / "planning/evidence/manifests"
        rel = "planning/evidence/manifests/certify-20261002T000000Z-1.json"
        sha = "e" * 64
        store.write_index(self.root, {rel: (sha, 10)})
        summary = self.base / "summary.json"
        summary.write_text(json.dumps({"version": chain_schedule.SUMMARY_VERSION, "files": {
            "certify-20261002T000000Z-1.json": {
                "stamp": ["sha256", sha],
                "summary": {"box": "hbox", "cpus": 1, "books": {"books/a": [1.0, None]}}}}}))
        with mock.patch.multiple(chain_schedule, ROOT=self.root, HISTORY=history), \
                contextlib.redirect_stderr(io.StringIO()):
            entries = chain_schedule.history_entries(history)
            self.assertEqual(chain_schedule.summaries(entries, summary), [None])



# ===================================================================== r66


class R66Tests(Sandbox):
    def test_F1_an_annotated_tag_of_a_tree_is_walked_as_that_tree(self):
        import evidence_history
        init_repo(self.root)
        self.write("planning/evidence/t.md", b"only in a tagged tree\n")
        git(self.root, "add", "-A")
        tree = git(self.root, "write-tree").strip()
        git(self.root, "rm", "-q", "--cached", "planning/evidence/t.md")
        (self.root / "planning/evidence/t.md").unlink()
        self.write("x.txt", b"x\n")
        commit_all(self.root, "unrelated")
        git(self.root, "tag", "-a", "-m", "a tree", "treetag", tree)
        blob = git(self.root, "rev-parse", f"{tree}:planning/evidence/t.md").strip()
        refs = evidence_history.snapshot_refs(self.root)
        found = evidence_history.union(evidence_history.rule_blobs(
            self.root, evidence_history.parse_rules("planning/evidence\n"), refs))
        self.assertIn(blob, found)

    def test_F2_every_sha_length_pair_is_checked(self):
        import evidence_history
        data = b"right length\n"
        sha = store.store_object(self.archive, data)
        report = evidence_history.archive_check({(sha, len(data)), (sha, len(data) + 1)},
                                                str(self.archive))
        self.assertEqual(report["checked"], 2)
        self.assertEqual(report["bad"], [sha])


    def test_a_worktree_that_cannot_be_asked_is_an_error(self):
        import evidence_history
        init_repo(self.root)
        commit_all(self.root, "one")
        other = self.base / "wt"
        git(self.root, "worktree", "add", "-q", "--detach", str(other))
        shutil.rmtree(other)        # listed by `worktree list`, unreadable
        with self.assertRaisesRegex(RuntimeError, "prune or restore"):
            evidence_history.snapshot_refs(self.root)


if __name__ == "__main__":
    unittest.main()
