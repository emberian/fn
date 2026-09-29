"""tools/next_id.py: ids taken anywhere, and the claims ledger that hands them out.

A scratch repository stands in for the fn checkout: a main tree with
build/coordinator/, a lane branch with a committed row, a worktree with an
uncommitted row and a LANEDUMP naming a packet.  The scan must see all of
them; two claims at once must get two numbers; `check` and the merge driver
must name a collision's claimant and an unclaimed row.
"""
from __future__ import annotations

import concurrent.futures
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import merge_registry  # noqa: E402
import next_id  # noqa: E402


def run(cwd: Path, *words: str) -> str:
    return subprocess.run(list(words), cwd=cwd, check=True, capture_output=True,
                          text=True).stdout


def write_registries(tree: Path, proofs: list[str], scenarios: list[str],
                     requirements: list[str], decisions: str = "### D01: one\n") -> None:
    (tree / "planning").mkdir(parents=True, exist_ok=True)
    (tree / "tests/scenarios").mkdir(parents=True, exist_ok=True)
    (tree / "planning/proofs.json").write_text(json.dumps(
        {"proofs": [{"id": one} for one in proofs]}, indent=2) + "\n")
    (tree / "planning/requirements.json").write_text(json.dumps(
        {"requirements": [{"id": one} for one in requirements]}, indent=2) + "\n")
    (tree / "tests/scenarios/catalog.json").write_text(json.dumps(
        {"scenarios": [{"id": one} for one in scenarios]}, indent=2) + "\n")
    (tree / "planning/decisions.md").write_text(decisions)


class Repo:
    def __init__(self, base: Path):
        self.main = base / "fn"
        self.main.mkdir()
        run(self.main, "git", "init", "-q", "-b", "dev")
        run(self.main, "git", "config", "user.email", "t@t")
        run(self.main, "git", "config", "user.name", "t")
        run(self.main, "git", "config", "commit.gpgsign", "false")
        write_registries(self.main, ["PRF-001", "PRF-002"], ["SCN-001"], ["STO-001"])
        (self.main / "notes.md").write_text("PKT-010 is old.\n")
        run(self.main, "git", "add", "-A")
        run(self.main, "git", "commit", "-q", "-m", "base")
        (self.main / "build/coordinator").mkdir(parents=True)
        self.ledger = self.main / "build/coordinator/id-claims.jsonl"

    def lane(self, name: str) -> Path:
        tree = self.main / "build/lanes" / name
        run(self.main, "git", "worktree", "add", "-q", str(tree), "-b", f"lane/{name}", "dev")
        return tree

    def commit(self, tree: Path, message: str) -> None:
        run(tree, "git", "add", "-A")
        run(tree, "git", "commit", "-q", "-m", message)


class ScanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Repo(Path(self.tmp.name).resolve())
        env = {k: v for k, v in os.environ.items()
               if k not in ("FN_ID_CLAIMS", "FN_ID_CLAIMS_SSH", "FN_LANE")}
        patcher = mock.patch.dict(os.environ, env, clear=True)
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_every_source_counts_and_the_largest_names_where_it_was_seen(self):
        other = self.repo.lane("other")
        write_registries(other, ["PRF-001", "PRF-002", "PRF-007"], ["SCN-001"], ["STO-001"])
        self.repo.commit(other, "a committed row on a lane branch")
        dirty = self.repo.lane("dirty")
        write_registries(dirty, ["PRF-001", "PRF-002"], ["SCN-001", "SCN-004"], ["STO-001"],
                         "### D01: one\n### D05: new\n")
        (dirty / "LANEDUMP.md").write_text("took PKT-044 for the thing\n")
        mine = self.repo.lane("mine")
        taken, kinds = next_id.scan_all(days=1, root=mine)
        self.assertIn("STO", kinds)
        self.assertEqual(taken.largest("PRF"), (7, "branch lane/other"))
        self.assertEqual(taken.largest("SCN"), (4, "worktree dirty (uncommitted)"))
        self.assertEqual(taken.largest("D"), (5, "worktree dirty (uncommitted)"))
        self.assertEqual(taken.largest("PKT"), (44, "dirty/LANEDUMP.md"))
        self.assertEqual(taken.largest("STO"), (1, "this tree"))
        local, _ = next_id.scan_all(days=1, local=True, root=mine)
        self.assertEqual(local.largest("PRF"), (2, "this tree"))

    def test_claims_are_atomic_and_count_as_taken(self):
        mine = self.repo.lane("mine")
        self.assertEqual(next_id.ledger_path(mine), self.repo.ledger)
        # Four processes at once, as four lanes would: each runs a copy of
        # the tool from the lane tree, so it scans that tree.
        (mine / "tools").mkdir()
        (mine / "tools/next_id.py").write_text((ROOT / "tools/next_id.py").read_text())
        claims = [subprocess.Popen([sys.executable, str(mine / "tools/next_id.py"), "claim",
                                    "PRF", "--lane", f"lane{index}", "--note", f"t {index}"],
                                   cwd=mine, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True) for index in range(4)]
        answers = [(one.wait(timeout=120), one.stdout.read().split()) for one in claims]
        self.assertTrue(all(code == 0 for code, _ in answers), answers)
        ids = sorted(ident for _, got in answers for ident in got)
        self.assertEqual(ids, ["PRF-003", "PRF-004", "PRF-005", "PRF-006"])
        with mock.patch.object(next_id, "ROOT", mine):
            out = io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
                next_id.main(["claim", "PKT", "--lane", "mine", "--note", "two", "--count", "2"])
            self.assertEqual(out.getvalue().split(), ["PKT-011", "PKT-012"])
            rows = next_id.read_ledger(self.repo.ledger)
            self.assertEqual(len(rows), 6)
            self.assertEqual({row["source"] for row in rows}, {"claim"})
            taken, _ = next_id.scan_all(days=1, root=mine)
            self.assertEqual(taken.largest("PRF")[0], 6)

    def test_a_claim_needs_a_lane_and_a_note_and_a_known_kind(self):
        mine = self.repo.lane("mine")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(next_id.main(["claim", "XYZ", "--lane", "m", "--note", "n"]), 2)
            self.assertEqual(next_id.main(["claim", "PRF", "--lane", "m", "--note", " "]), 2)
        self.assertIn("unknown kind XYZ", err.getvalue())
        self.assertEqual(next_id.default_lane(mine), "mine")

    def test_an_unknown_subcommand_is_a_loud_usage_error_not_the_listing(self):
        mine = self.repo.lane("mine")
        with mock.patch.object(next_id, "ROOT", mine), \
                mock.patch.object(next_id, "show") as listing, \
                contextlib.redirect_stdout(io.StringIO()) as out, \
                contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as stop:
                next_id.main(["clam", "PRF", "--lane", "m", "--note", "n"])
        self.assertEqual(stop.exception.code, 2)
        listing.assert_not_called()
        self.assertEqual(out.getvalue(), "")
        self.assertIn("invalid choice: 'clam'", err.getvalue())
        self.assertIn("may predate", err.getvalue())

    def test_with_no_ledger_a_box_is_told_the_laptop_command(self):
        with tempfile.TemporaryDirectory() as bare:
            with mock.patch.object(next_id, "ROOT", Path(bare)), \
                    contextlib.redirect_stderr(io.StringIO()) as err:
                code = next_id.main(["claim", "PRF", "--lane", "boxlane", "--note", "x"])
        self.assertEqual(code, 2)
        self.assertIn("Claim from the laptop", err.getvalue())
        self.assertIn("next_id.py claim PRF --lane boxlane --note x", err.getvalue())
        self.assertIn("FN_ID_CLAIMS_SSH", err.getvalue())

    def test_check_names_collisions_and_unclaimed_ids(self):
        mine = self.repo.lane("mine")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            next_id.main(["claim", "PRF", "--lane", "someone", "--note", "theirs"])  # 003
            next_id.main(["claim", "SCN", "--lane", "mine", "--note", "ours"])  # 002
        write_registries(mine, ["PRF-001", "PRF-002", "PRF-003"], ["SCN-001", "SCN-002"],
                         ["STO-001", "STO-002"])
        (mine / "notes.md").write_text("PKT-010 is old; PKT-020 is new here.\n")
        with mock.patch.object(next_id, "ROOT", mine):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = next_id.main(["check", "--base", "dev", "--lane", "mine"])
        text = out.getvalue()
        self.assertEqual(code, 1, text)
        self.assertIn("COLLISION PRF-003: claimed by someone", text)
        self.assertIn("ok        SCN-002: claimed by mine", text)
        self.assertIn("UNCLAIMED STO-002", text)
        self.assertIn("UNCLAIMED PKT-020", text)
        self.assertNotIn("PKT-010", text)

    def test_check_counts_a_predecessors_claims_as_this_lanes(self):
        # item 70: obstructions-8 works in the worktree obstructions-2 on
        # lane/obstructions-2 and claims under its own name; obstructions-7
        # claimed before it.  Neither is a collision; another lane's is.
        mine = self.repo.lane("line-2")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            next_id.main(["claim", "PRF", "--lane", "line-7", "--note", "predecessor"])  # 003
            next_id.main(["claim", "PRF", "--lane", "line-8", "--note", "successor"])  # 004
            next_id.main(["claim", "PRF", "--lane", "other-8", "--note", "theirs"])  # 005
        write_registries(mine, ["PRF-001", "PRF-002", "PRF-003", "PRF-004", "PRF-005"], ["SCN-001"],
                         ["STO-001"])
        env = {k: v for k, v in os.environ.items() if k != "FN_LANE"}
        with mock.patch.object(next_id, "ROOT", mine), mock.patch.dict(os.environ, env,
                                                                       clear=True):
            self.assertEqual(next_id.our_lanes(None, mine), {"line-2"})
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = next_id.main(["check", "--base", "dev"])
            text = out.getvalue()
            self.assertEqual(code, 1, text)
            self.assertIn("ok        PRF-003: claimed by line-7 (predecessor) -- this lane's line",
                          text)
            self.assertIn("ok        PRF-004: claimed by line-8", text)
            self.assertIn("COLLISION PRF-005: claimed by other-8", text)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                next_id.main(["check", "--base", "dev", "--exact-lane", "--lane", "line-8"])
            self.assertIn("COLLISION PRF-003: claimed by line-7", out.getvalue())
            self.assertIn("ok        PRF-004: claimed by line-8", out.getvalue())

    def test_the_merge_driver_names_an_unclaimed_row_and_a_collisions_claimant(self):
        mine = self.repo.lane("mine")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            next_id.main(["claim", "PRF", "--lane", "winner", "--note", "the real one"])
        base = {"proofs": [{"id": "PRF-001"}]}
        ours = {"proofs": [{"id": "PRF-001"}, {"id": "PRF-003", "s": "a"}]}
        theirs = {"proofs": [{"id": "PRF-001"}, {"id": "PRF-003", "s": "b"},
                             {"id": "PRF-009", "s": "c"}]}
        merged, conflicts = merge_registry.merge_documents(base, ours, theirs,
                                                           "planning/proofs.json")
        cwd = os.getcwd()
        os.chdir(mine)
        try:
            notes = merge_registry.claim_notes(base, merged, ours, theirs, conflicts)
        finally:
            os.chdir(cwd)
        self.assertIn("CLAIMED PRF-003 by winner (the real one): the other side renumbers",
                      notes)
        self.assertTrue(any(note.startswith("UNCLAIMED PRF-009 (theirs)") for note in notes),
                        notes)
        self.assertFalse(any("UNCLAIMED PRF-003" in note for note in notes))

    def test_backfill_records_what_was_taken_since_and_skips_the_claimed(self):
        other = self.repo.lane("other")
        write_registries(other, ["PRF-001", "PRF-002", "PRF-003"], ["SCN-001"], ["STO-001"])
        self.repo.commit(other, "PRF-003 on a lane")
        mine = self.repo.lane("mine")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            next_id.main(["claim", "SCN", "--lane", "mine", "--note", "claimed"])
            code = next_id.main(["backfill", "--since", "2000-01-01T00:00:00Z", "--base", "dev"])
        self.assertEqual(code, 2)  # no dev commit before 2000
        import datetime
        tomorrow = (datetime.datetime.now(datetime.timezone.utc)
                    + datetime.timedelta(days=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
        with mock.patch.object(next_id, "ROOT", mine), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            code = next_id.main(["backfill", "--since", tomorrow, "--base", "dev"])
        self.assertEqual(code, 0, out.getvalue())
        rows = {row["id"]: row for row in next_id.read_ledger(self.repo.ledger)}
        self.assertEqual(rows["PRF-003"]["source"], "backfill")
        self.assertEqual(rows["PRF-003"]["lane"], "other")
        self.assertEqual(rows["SCN-002"]["source"], "claim")
        self.assertNotIn("PRF-002", rows)


if __name__ == "__main__":
    unittest.main()
