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
            # And recorded where the batch runner reads it: `git add` of the
            # valid JSON would otherwise keep ours silently.
            record = repo / "build/merge-conflicts/registry.jsonl"
            (entry,) = [json.loads(line) for line in record.read_text().splitlines()]
            self.assertEqual((entry["path"], entry["id"], entry["field"], entry["ours_kept"]),
                             ("planning/proofs.json", "PRF-001", "status", True))
            listed = subprocess.run([sys.executable, str(DRIVER), "--pending"], cwd=repo,
                                    capture_output=True, text=True)
            self.assertEqual(listed.returncode, 1)
            self.assertIn("UNRESOLVED planning/proofs.json: PRF-001 status", listed.stdout)
            cleared = subprocess.run([sys.executable, str(DRIVER), "--clear"], cwd=repo,
                                     capture_output=True, text=True)
            self.assertEqual(cleared.returncode, 0)
            again = subprocess.run([sys.executable, str(DRIVER), "--pending"], cwd=repo,
                                   capture_output=True, text=True)
            self.assertEqual(again.returncode, 0, again.stdout)

    def test_a_clean_merge_records_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = self.repo(directory, [row("PRF-001")])
            self.branch(repo, "a", [row("PRF-001"), row("PRF-002", title="a")])
            self.branch(repo, "b", [row("PRF-001"), row("PRF-003", title="b")], "dev")
            git(repo, "checkout", "-q", "a")
            git(repo, "merge", "--no-edit", "b")
            self.assertFalse((repo / "build/merge-conflicts/registry.jsonl").exists())


class RequirementsAndCatalogThroughGit(unittest.TestCase):
    """C5 (COMPLETE-BEFORE-6.6.0): requirements.json and the scenario catalog
    merge by id like proofs.json, and the cross-file link stays reciprocal."""

    def write_all(self, repo: Path, requirements: list, scenarios: list, proofs: list) -> None:
        for path, key, rows in (("planning/requirements.json", "requirements", requirements),
                                ("tests/scenarios/catalog.json", "scenarios", scenarios),
                                ("planning/proofs.json", "proofs", proofs)):
            target = repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(json.dumps({"schema_version": 1, key: rows}, indent=2) + "\n")

    def test_two_lanes_linking_proofs_to_one_requirement_keep_both_links(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            git(repo, "init", "-q", "-b", "dev")
            (repo / ".gitattributes").write_text(
                "planning/proofs.json merge=fn-registry\n"
                "planning/requirements.json merge=fn-registry\n"
                "tests/scenarios/catalog.json merge=fn-registry\n")
            req = {"id": "NNT-034", "title": "t", "proof_targets": ["PRF-164"]}
            scn = {"id": "SCN-001", "title": "s", "requirements": ["NNT-034"]}
            prf = {"id": "PRF-164", "title": "p", "requirements": ["NNT-034"]}
            self.write_all(repo, [req], [scn], [prf])
            git(repo, "add", ".")
            git(repo, "commit", "-q", "-m", "base")
            # Lane a: PRF-374 on NNT-034 (both sides) and SCN-002.
            git(repo, "checkout", "-q", "-b", "a", "dev")
            self.write_all(repo, [dict(req, proof_targets=["PRF-164", "PRF-374"])],
                           [scn, {"id": "SCN-002", "title": "a", "requirements": ["NNT-034"]}],
                           [prf, {"id": "PRF-374", "title": "a", "requirements": ["NNT-034"]}])
            git(repo, "commit", "-q", "-am", "a")
            # Lane b: PRF-378 on NNT-034 (both sides) and SCN-003.
            git(repo, "checkout", "-q", "-b", "b", "dev")
            self.write_all(repo, [dict(req, proof_targets=["PRF-164", "PRF-378"])],
                           [scn, {"id": "SCN-003", "title": "b", "requirements": ["NNT-034"]}],
                           [prf, {"id": "PRF-378", "title": "b", "requirements": ["NNT-034"]}])
            git(repo, "commit", "-q", "-am", "b")
            git(repo, "checkout", "-q", "a")
            merged = git(repo, "merge", "--no-edit", "b", check=False)
            self.assertEqual(merged.returncode, 0, merged.stdout + merged.stderr)
            (only,) = json.loads((repo / "planning/requirements.json").read_text())["requirements"]
            self.assertEqual(only["proof_targets"], ["PRF-164", "PRF-374", "PRF-378"])
            scenarios = json.loads((repo / "tests/scenarios/catalog.json").read_text())
            self.assertEqual([r["id"] for r in scenarios["scenarios"]],
                             ["SCN-001", "SCN-002", "SCN-003"])
            check = subprocess.run([sys.executable, str(DRIVER), "--reciprocate", "--check"],
                                   cwd=repo, capture_output=True, text=True)
            self.assertEqual(check.returncode, 0, check.stdout)

    def test_a_one_way_registration_is_found_and_repaired_on_both_files(self):
        # The recurring break (PRF-374/378/379/383): the proof names the
        # requirement; the requirement never lists the proof.
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            self.write_all(repo,
                           [{"id": "NNT-034", "proof_targets": ["PRF-164", "PRF-900"]},
                            {"id": "HST-006", "proof_targets": []}],
                           [], [{"id": "PRF-164", "requirements": ["NNT-034"]},
                                {"id": "PRF-374", "requirements": ["NNT-034"]},
                                {"id": "PRF-383", "requirements": ["HST-006"]},
                                {"id": "PRF-500", "requirements": []}])
            requirements = json.loads((repo / "planning/requirements.json").read_text())
            requirements["requirements"][1]["proof_targets"].append("PRF-500")
            (repo / "planning/requirements.json").write_text(
                json.dumps(requirements, indent=2) + "\n")
            check = subprocess.run([sys.executable, str(DRIVER), "--reciprocate", "--check"],
                                   cwd=repo, capture_output=True, text=True)
            self.assertEqual(check.returncode, 1)
            self.assertIn("MISSING NNT-034 proof_targets += PRF-374", check.stdout)
            self.assertIn("MISSING HST-006 proof_targets += PRF-383", check.stdout)
            self.assertIn("MISSING PRF-500 requirements += HST-006", check.stdout)
            fixed = subprocess.run([sys.executable, str(DRIVER), "--reciprocate"],
                                   cwd=repo, capture_output=True, text=True)
            self.assertEqual(fixed.returncode, 0, fixed.stdout + fixed.stderr)
            rows = {r["id"]: r for r in json.loads(
                (repo / "planning/requirements.json").read_text())["requirements"]}
            # A link to an unknown proof (PRF-900) is left for check_scaffold.
            self.assertEqual(rows["NNT-034"]["proof_targets"], ["PRF-164", "PRF-900", "PRF-374"])
            self.assertEqual(rows["HST-006"]["proof_targets"], ["PRF-500", "PRF-383"])
            proofs = {r["id"]: r for r in json.loads(
                (repo / "planning/proofs.json").read_text())["proofs"]}
            self.assertEqual(proofs["PRF-500"]["requirements"], ["HST-006"])
            again = subprocess.run([sys.executable, str(DRIVER), "--reciprocate", "--check"],
                                   cwd=repo, capture_output=True, text=True)
            self.assertEqual(again.returncode, 0, again.stdout)

    def test_the_tree_is_reciprocal(self):
        requirements = json.loads((ROOT / "planning/requirements.json").read_text())
        proofs = json.loads((ROOT / "planning/proofs.json").read_text())
        self.assertEqual(merge_registry.reciprocate(requirements, proofs), [])

    def test_an_unregistered_clone_is_named_and_install_registers_it(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull)
            run = lambda *words: subprocess.run([sys.executable, str(DRIVER), *words],
                                                cwd=repo, capture_output=True, text=True,
                                                env=env)
            missing = run("--installed")
            self.assertEqual(missing.returncode, 1)
            self.assertIn("NOT REGISTERED", missing.stdout)
            self.assertEqual(run("--install").returncode, 0)
            driver = subprocess.run(["git", "-C", str(repo), "config", "--get",
                                     "merge.fn-registry.driver"], capture_output=True,
                                    text=True, env=env).stdout.strip()
            self.assertEqual(driver, "python3 tools/merge_registry.py %O %A %B %P")
            self.assertEqual(run("--installed").returncode, 0)


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
        self.assertEqual([r.get("title") for r in merged["rows"][1:]], ["ours", "theirs"])
        self.assertEqual(len(conflicts), 1)
        self.assertIn("CONFLICT B: both sides added this id", conflicts[0])

    def test_conflict_lines_parse_to_id_and_field(self):
        records = merge_registry.conflict_records("p.json", [
            "CONFLICT PRF-212 status: ours 'a' theirs 'b' base 'c'",
            "CONFLICT PRF-9 keystone_subjects fn-x: ours 1 theirs 2 base 3",
            "CONFLICT B: both sides added this id with different rows",
            "CONFLICT (top level) schema_version: ours 1 theirs 2 base 0"])
        self.assertEqual([(r["id"], r["field"]) for r in records],
                         [("PRF-212", "status"), ("PRF-9", "keystone_subjects fn-x"),
                          ("B", ""), ("(top level)", "schema_version")])

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
