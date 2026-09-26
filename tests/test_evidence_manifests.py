"""A cited certification run must resolve to a manifest a reader can open.

Measured on dev at 5698648: 316 certification run ids were cited in tracked
files and not one of them resolved, because every citation names a directory
under `build/`, which `.gitignore:6` excludes and which a worktree removal, a
farm root or a gate reaper deletes.  These tests hold the two halves
of the repair: the archive is keyed by run id alone, and `check` measures
what is COMMITTED rather than what is on this disk.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import evidence_manifests as archive  # noqa: E402


def repository(directory: str) -> Path:
    root = Path(directory).resolve()
    subprocess.run(["git", "-C", str(root), "init", "-q"], check=True)
    subprocess.run(["git", "-C", str(root), "config", "user.email", "t@example"],
                   check=True)
    subprocess.run(["git", "-C", str(root), "config", "user.name", "t"], check=True)
    # The developer's global commit.gpgsign would make every commit here wait
    # on the signing agent (tests/test_triage.py hit it; harness-repair).
    subprocess.run(["git", "-C", str(root), "config", "commit.gpgsign", "false"],
                   check=True)
    (root / ".gitignore").write_text("planning/evidence/manifests/*.json\n")
    return root


def commit(root: Path, name: str, body: str) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body)
    subprocess.run(["git", "-C", str(root), "add", "--", name], check=True)
    subprocess.run(["git", "-C", str(root), "commit", "-q", "-m", name], check=True)


def run_dir(root: Path, run_id: str, manifest: dict) -> Path:
    directory = root / "build" / "acl2" / run_id
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "manifest.json").write_text(json.dumps(manifest))
    return directory


RUN = "certify-20260921T010700Z-1373865"
OTHER = "certify-20260920T024318Z-1528458"


class CitationTests(unittest.TestCase):

    def test_a_run_id_in_a_tracked_file_is_cited_and_its_line_is_named(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            commit(root, "planning/lanes/HANDOFF-x.md",
                   f"certified in `build/acl2/{RUN}`\n")
            cites = archive.cited_run_ids(root)
        self.assertEqual(sorted(cites), [RUN])
        self.assertEqual(cites[RUN], ["planning/lanes/HANDOFF-x.md:1"])

    def test_an_untracked_claim_is_not_a_citation(self):
        """What a reader of the repository sees is what is committed."""
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            commit(root, "README.md", "nothing here\n")
            (root / "scratch.md").write_text(f"build/acl2/{RUN}\n")
            self.assertEqual(archive.cited_run_ids(root), {})

    def test_the_archive_does_not_cite_itself(self):
        """A manifest records its own run id; that must not look like a claim."""
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            archive.write_manifest(RUN, json.dumps({"status": "passed"}),
                                   "persvati:/home/ember/x", root)
            subprocess.run(["git", "-C", str(root), "add", "-f", "--",
                            f"planning/evidence/manifests/{RUN}.json"], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-q", "-m", "m"],
                           check=True)
            self.assertEqual(archive.cited_run_ids(root), {})
            self.assertEqual(archive.tracked_manifests(root), {RUN})


class ArchiveTests(unittest.TestCase):

    def test_the_archived_copy_keeps_the_claim_and_says_where_the_log_is(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            source = run_dir(root, RUN, {"status": "passed",
                                         "requested_books": ["books/a"]})
            self.assertEqual(archive.archive_run(source, root, "persvati:/gate/x"),
                             "written")
            kept = json.loads(
                (root / "planning/evidence/manifests" / f"{RUN}.json").read_text())
        self.assertEqual(kept["requested_books"], ["books/a"])
        self.assertEqual(kept["run_id"], RUN)
        self.assertEqual(kept["archived_from"], "persvati:/gate/x")

    def test_the_same_run_archived_twice_keeps_the_first_copy(self):
        """A farm run is produced on a box and later swept off it."""
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            body = json.dumps({"status": "passed"})
            self.assertEqual(archive.write_manifest(RUN, body, "persvati:/a", root),
                             "written")
            self.assertEqual(archive.write_manifest(RUN, body, "hbox:/b", root),
                             "present")
            kept = json.loads(
                (root / "planning/evidence/manifests" / f"{RUN}.json").read_text())
        self.assertEqual(kept["archived_from"], "persvati:/a")

    def test_two_different_runs_under_one_id_are_reported_not_merged(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            archive.write_manifest(RUN, json.dumps({"status": "passed"}), "a", root)
            self.assertEqual(
                archive.write_manifest(RUN, json.dumps({"status": "failed"}), "b",
                                       root),
                "conflict")
            kept = json.loads(
                (root / "planning/evidence/manifests" / f"{RUN}.json").read_text())
        self.assertEqual(kept["status"], "passed")

    def test_a_run_directory_with_no_manifest_is_skipped_not_fatal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            empty = root / "build" / "acl2" / RUN
            empty.mkdir(parents=True)
            self.assertEqual(archive.archive_run(empty, root), "skipped")


class CheckTests(unittest.TestCase):
    """`check` reads the index, so an uncommitted local copy does not count."""

    def test_an_archived_but_uncommitted_manifest_does_not_resolve_a_citation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            commit(root, "planning/lanes/HANDOFF-x.md", f"`build/acl2/{RUN}`\n")
            archive.write_manifest(RUN, json.dumps({"status": "passed"}), "a", root)
            self.assertEqual(archive.cited_run_ids(root), {RUN: [
                "planning/lanes/HANDOFF-x.md:1"]})
            self.assertEqual(archive.archived(root), {RUN})
            self.assertEqual(archive.tracked_manifests(root), set())

    def test_committing_the_manifest_resolves_the_citation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = repository(directory)
            commit(root, "planning/lanes/HANDOFF-x.md",
                   f"`build/acl2/{RUN}` and `build/acl2/{OTHER}`\n")
            archive.write_manifest(RUN, json.dumps({"status": "passed"}), "a", root)
            subprocess.run(["git", "-C", str(root), "add", "-f", "--",
                            f"planning/evidence/manifests/{RUN}.json"], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-q", "-m", "m"],
                           check=True)
            cited = set(archive.cited_run_ids(root))
            tracked = archive.tracked_manifests(root)
        self.assertEqual(cited, {RUN, OTHER})
        self.assertEqual(tracked, {RUN})
        # OTHER is the shape of the backlog: a claim with no evidence left.
        self.assertEqual(cited - tracked, {OTHER})


    def test_the_command_line_reports_the_four_counts_for_this_tree(self):
        done = subprocess.run(
            [sys.executable, str(TOOLS / "evidence_manifests.py"), "check"],
            capture_output=True, text=True, check=False)
        self.assertEqual(done.returncode, 0, done.stderr)
        for phrase in ("cited in tracked files:", "manifests committed under",
                       "cited and resolvable:", "cited and unresolvable:"):
            self.assertIn(phrase, done.stdout)


if __name__ == "__main__":
    unittest.main()
