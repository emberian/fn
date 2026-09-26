"""tools/merge_registry.py as a real git merge driver (friction review section 7)."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "tools" / "merge_registry.py"
sys.path.insert(0, str(ROOT / "tools"))
import merge_registry  # noqa: E402


def git(repo: Path, *words: str, check: bool = True) -> subprocess.CompletedProcess:
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    return subprocess.run(["git", "-C", str(repo), "-c", "commit.gpgsign=false",
                           "-c", "merge.fn-registry.driver="
                           f"{sys.executable} {DRIVER} %O %A %B %P", *words],
                          check=check, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True)


def write(repo: Path, rows: list, key: str = "proofs") -> None:
    path = repo / "planning/proofs.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"schema_version": 1, key: rows}, indent=2) + "\n")


def row(ident: str, **fields) -> dict:
    return {"id": ident, "status": "open", "evidence": [], **fields}


class DriverThroughGit(unittest.TestCase):
    def repo(self, directory: str, base: list) -> Path:
        repo = Path(directory)
        git(repo, "init", "-q", "-b", "dev")
        (repo / ".gitattributes").write_text("planning/proofs.json merge=fn-registry\n")
        write(repo, base)
        git(repo, "add", ".")
        git(repo, "commit", "-q", "-m", "base")
        return repo

    def branch(self, repo: Path, name: str, rows: list, start: str = "dev") -> None:
        git(repo, "checkout", "-q", "-b", name, start)
        write(repo, rows)
        git(repo, "commit", "-q", "-am", name)

    def test_two_lanes_appending_rows_merge_clean(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = self.repo(directory, [row("PRF-001")])
            self.branch(repo, "a", [row("PRF-001"), row("PRF-002", title="a")])
            self.branch(repo, "b", [row("PRF-001"), row("PRF-003", title="b")], "dev")
            git(repo, "checkout", "-q", "a")
            merged = git(repo, "merge", "--no-edit", "b", check=False)
            self.assertEqual(merged.returncode, 0, merged.stdout + merged.stderr)
            rows = json.loads((repo / "planning/proofs.json").read_text())["proofs"]
            self.assertEqual([r["id"] for r in rows], ["PRF-001", "PRF-002", "PRF-003"])

    def test_the_same_text_merge_conflicts_without_the_driver(self):
        # The control: plain git conflicts on exactly this history.
        with tempfile.TemporaryDirectory() as directory:
            repo = self.repo(directory, [row("PRF-001")])
            (repo / ".gitattributes").write_text("")
            git(repo, "commit", "-q", "-am", "no driver")
            self.branch(repo, "a", [row("PRF-001"), row("PRF-002", title="a")])
            self.branch(repo, "b", [row("PRF-001"), row("PRF-003", title="b")], "dev")
            git(repo, "checkout", "-q", "a")
            merged = git(repo, "merge", "--no-edit", "b", check=False)
            self.assertNotEqual(merged.returncode, 0)

    def test_fields_merge_three_way_and_evidence_unions(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = self.repo(directory, [row("PRF-001", evidence=["m0"])])
            self.branch(repo, "a", [row("PRF-001", status="proved",
                                        evidence=["m0", "m1"])])
            self.branch(repo, "b", [row("PRF-001", title="new title",
                                        evidence=["m0", "m2"])], "dev")
            git(repo, "checkout", "-q", "a")
            merged = git(repo, "merge", "--no-edit", "b", check=False)
            self.assertEqual(merged.returncode, 0, merged.stderr)
            (only,) = json.loads((repo / "planning/proofs.json").read_text())["proofs"]
            self.assertEqual(only["status"], "proved")
            self.assertEqual(only["title"], "new title")
            self.assertEqual(only["evidence"], ["m0", "m1", "m2"])

    def test_a_real_conflict_is_named_and_left_conflicted(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = self.repo(directory, [row("PRF-001")])
            self.branch(repo, "a", [row("PRF-001", status="proved")])
            self.branch(repo, "b", [row("PRF-001", status="refuted")], "dev")
            git(repo, "checkout", "-q", "a")
            merged = git(repo, "merge", "--no-edit", "b", check=False)
            self.assertNotEqual(merged.returncode, 0)
            self.assertIn("CONFLICT PRF-001 status", merged.stdout + merged.stderr)
            unmerged = git(repo, "diff", "--name-only", "--diff-filter=U").stdout
            self.assertIn("planning/proofs.json", unmerged)
            json.loads((repo / "planning/proofs.json").read_text())  # still JSON


class RuleTests(unittest.TestCase):
    def test_deleted_on_one_side_unchanged_on_the_other_stays_deleted(self):
        base = {"rows": [row("A"), row("B")]}
        merged, conflicts = merge_registry.merge_documents(
            base, {"rows": [row("A")]}, {"rows": [row("A"), row("B"), row("C")]},
            "x.json")
        self.assertEqual([r["id"] for r in merged["rows"]], ["A", "C"])
        self.assertEqual(conflicts, [])

    def test_an_id_both_sides_took_is_a_collision(self):
        merged, conflicts = merge_registry.merge_documents(
            {"rows": [row("A")]}, {"rows": [row("A"), row("B", title="ours")]},
            {"rows": [row("A"), row("B", title="theirs")]}, "x.json")
        self.assertEqual(merged["rows"][1]["title"], "ours")
        self.assertEqual(len(conflicts), 1)
        self.assertIn("CONFLICT B: both sides added this id", conflicts[0])

    def test_an_element_ours_removed_stays_removed(self):
        self.assertEqual(merge_registry.merge_list(["x", "y"], ["x"], ["x", "y", "z"]),
                         ["x", "z"])

    def test_generated_events_keep_ours(self):
        base = {"proofs": [row("P", events=[1])]}
        merged, conflicts = merge_registry.merge_documents(
            base, {"proofs": [row("P", events=[1, 2])]},
            {"proofs": [row("P", events=[1, 3])]}, "planning/proofs.json")
        self.assertEqual(merged["proofs"][0]["events"], [1, 2])
        self.assertEqual(conflicts, [])

    def test_the_four_registries_round_trip_unchanged(self):
        for path in ("planning/proofs.json", "planning/requirements.json",
                     "planning/proof-events.json", "tests/scenarios/catalog.json"):
            document = json.loads((ROOT / path).read_text())
            merged, conflicts = merge_registry.merge_documents(
                document, document, document, path)
            self.assertEqual((merged, conflicts), (document, []), path)


if __name__ == "__main__":
    unittest.main()
