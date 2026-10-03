"""tools/green_check.py: a book is green only at the digest it carries NOW.

On 2026-09-21 four books sat red on `dev` for a day -- `stx-evidence-records`,
`checkpoint-compaction`, `hybrid-store`, `feed-connection` -- each committed by
a lane that never certified it, while every reader took `git log` for
certification.  The archived manifests had already recorded those failures at
exactly the digests the tree carried.  These tests pin the four answers the
instrument has to keep apart, because collapsing any two of them is how that
day happened: green at this digest, RED at this digest, green only at an older
digest, and never asked at all.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import green_check  # noqa: E402


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def book(root: Path, name: str, body: str) -> str:
    """Write `<name>.lisp` with `body` and answer its sha256."""
    path = root / f"{name}.lisp"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return digest(body)


def manifest(root: Path, run_id: str, *, status: str,
             passed: dict[str, str] = {}, failed: dict[str, str] = {},
             host: str = "testbox", after: dict[str, str] | None = None,
             closure: dict[str, str] | None = None) -> None:
    """One archived manifest, with the fields the pass rule actually reads.

    The synthetic run ids below are spelled out, which is safe only here:
    `tools/evidence_manifests.py cited_run_ids` excludes `tests/test_*.py`,
    because a run id in a unit test is a fixture and not a claim about a
    certification.  Anywhere else in the tree it would fail `make check`.


    `passed` and `failed` map a book to the source digest that run recorded
    for it.  A passing book gets the run's own fresh success marker, a
    certificate digest and exit 0, which is `certs.certified_books`' rule;
    a failing book gets a verdict and a reason and no certificate.
    """
    requested = sorted({**passed, **failed})
    markers = {name: f"FN_CERTIFY_SUCCESS {run_id} {name}" for name in requested}
    body = {
        "run_id": run_id,
        "status": status,
        "archived_from": f"{host}:/tmp/{run_id}",
        "requested_books": requested,
        "expected_success_markers": [markers[name] for name in requested],
        "observed_success_markers": [markers[name] for name in passed],
        "book_results": {name: ("passed" if name in passed else "failed")
                         for name in requested},
        "book_failures": {name: ["no certificate on disk"] for name in failed},
        "source_digests_sha256": {
            **{f"{name}.lisp": found for name, found in (closure or {}).items()},
            **{f"{name}.lisp": found for name, found in {**passed, **failed}.items()}},
        "certificate_digests_sha256": {name: digest(f"cert {run_id} {name}")
                                       for name in passed},
        "acl2_exit_codes": {name: 0 for name in requested},
    }
    if after is not None:
        body["source_digests_sha256_after"] = {f"{name}.lisp": found
                                               for name, found in after.items()}
    archive = root / "planning" / "evidence" / "manifests"
    archive.mkdir(parents=True, exist_ok=True)
    (archive / f"{run_id}.json").write_text(json.dumps(body), encoding="utf-8")


class SyntheticTreeTests(unittest.TestCase):
    """Four books, one per answer, over manifests written by hand."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        root = Path(cls.directory.name).resolve()
        cls.root = root
        # `green` certified at the bytes it still has.  `red` certified once
        # and then failed at the bytes it has now.  `stale` certified at bytes
        # it no longer has and nobody has run it since.  `unasked` is a root
        # no manifest ever requested.
        current = {
            "books/green": book(root, "books/green", '(in-package "ACL2") ; green'),
            "books/red": book(root, "books/red", '(in-package "ACL2") ; red'),
            "books/stale": book(root, "books/stale", '(in-package "ACL2") ; stale'),
            "books/unasked": book(root, "books/unasked", '(in-package "ACL2")'),
        }
        cls.current = current
        old = digest("something else entirely")
        manifest(root, "certify-20260901T010000Z-1", status="passed",
                 passed={"books/green": current["books/green"],
                         "books/red": current["books/red"],
                         "books/stale": old})
        manifest(root, "certify-20260902T020000Z-2", status="failed",
                 failed={"books/red": current["books/red"]}, host="hbox")
        cls.report = green_check.audit(root, roots=sorted(current))
        cls.verdicts = {name: entry["verdict"]
                        for name, entry in cls.report["books_by_verdict"].items()}

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_green_is_green_only_at_the_digest_the_tree_carries(self):
        self.assertEqual(self.verdicts["books/green"], "green")
        entry = self.report["books_by_verdict"]["books/green"]
        self.assertEqual(entry["certified_at_digest"], "certify-20260901T010000Z-1")
        self.assertEqual(entry["digest_sha256"], self.current["books/green"])
        self.assertIn("certified 2026-09-01T01:00Z", entry["note"])

    def test_a_failure_newer_than_the_green_makes_the_book_red(self):
        """The 2026-09-21 defect exactly: a green run, then a failing run at
        the same bytes, and nothing after it."""
        self.assertEqual(self.verdicts["books/red"], "red")
        entry = self.report["books_by_verdict"]["books/red"]
        self.assertEqual(entry["failed_at_digest"], "certify-20260902T020000Z-2")
        self.assertIn("FAILED 2026-09-02T02:00Z", entry["note"])
        self.assertIn("hbox", entry["note"])

    def test_a_green_at_an_older_digest_is_not_a_green(self):
        self.assertEqual(self.verdicts["books/stale"], "never")
        entry = self.report["books_by_verdict"]["books/stale"]
        self.assertIsNone(entry["certified_at_digest"])
        self.assertEqual(entry["last_green_any_digest"],
                         "certify-20260901T010000Z-1")
        self.assertIn("NEVER at this digest", entry["note"])
        self.assertIn("at an older digest", entry["note"])

    def test_a_book_no_manifest_requested_is_unmeasured_not_clean(self):
        self.assertEqual(self.verdicts["books/unasked"], "absent")
        entry = self.report["books_by_verdict"]["books/unasked"]
        self.assertIsNone(entry["last_green_any_digest"])

    def test_the_four_answers_partition_the_closure(self):
        counts = self.report["counts"]
        self.assertEqual(sum(counts.values()), len(self.current))
        self.assertEqual(counts, {"green": 1, "red": 1, "never": 1, "absent": 1})

    def test_the_table_puts_the_red_book_first(self):
        rows = green_check.table(self.report)
        self.assertIn("books/red", rows[1])
        self.assertEqual([row.split()[0] for row in rows[1:]],
                         ["red", "never", "absent", "green"])

    def test_the_worklist_is_everything_but_the_greens(self):
        self.assertEqual(green_check.worklist(self.report),
                         ["books/red", "books/stale", "books/unasked"])

    def test_the_summary_is_three_lines(self):
        lines = green_check.summary(self.report)
        self.assertEqual(len(lines), 3)
        self.assertTrue(all(line.startswith("green-check: ") for line in lines))
        self.assertIn("1 RED at digest", lines[0])


class GreenWinsWhenItIsNewerTests(unittest.TestCase):
    """A repaired book is green again; a red older than the green is history."""

    def test_a_later_green_at_the_same_digest_clears_the_red(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            found = book(root, "books/fixed", '(in-package "ACL2") ; fixed')
            manifest(root, "certify-20260901T010000Z-1", status="failed",
                     failed={"books/fixed": found})
            manifest(root, "certify-20260903T030000Z-3", status="passed",
                     passed={"books/fixed": found})
            report = green_check.audit(root, roots=["books/fixed"])
            entry = report["books_by_verdict"]["books/fixed"]
            self.assertEqual(entry["verdict"], "green")
            # The red is still recorded; it is simply no longer the answer.
            self.assertEqual(entry["failed_at_digest"], "certify-20260901T010000Z-1")

    def test_a_source_that_moved_during_the_run_vouches_for_nothing(self):
        """`certs.verified`'s rule, kept here: a book whose `_after` digest
        disagrees with its `_before` digest was edited mid-certification."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            found = book(root, "books/moved", '(in-package "ACL2") ; moved')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/moved": found},
                     after={"books/moved": digest("edited mid-run")})
            report = green_check.audit(root, roots=["books/moved"])
            self.assertEqual(
                report["books_by_verdict"]["books/moved"]["verdict"], "never")


class DependencyDriftTests(unittest.TestCase):
    """A green at one file's bytes over a changed dependency is not a pair."""

    def test_a_moved_dependency_is_reported_on_the_green(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dependency = book(root, "books/dep", '(in-package "ACL2")')
            top = book(root, "books/top",
                       '(in-package "ACL2")\n(include-book "dep")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top, "books/dep": dependency})
            report = green_check.audit(root, roots=["books/top"])
            self.assertEqual(report["books_by_verdict"]["books/top"]["verdict"],
                             "green")
            self.assertEqual(
                report["books_by_verdict"]["books/top"]["deps_moved_since"], [])
            # Edit only the dependency: `top`'s own bytes are still certified
            # and its certificate is no longer about this source set.
            book(root, "books/dep", '(in-package "ACL2") ; changed')
            report = green_check.audit(root, roots=["books/top"])
            entry = report["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "green")
            self.assertEqual(entry["deps_moved_since"], ["books/dep.lisp"])
            self.assertIn("1 deps moved since", entry["note"])

    def test_older_matching_closure_pass_survives_newer_incompatible_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dep = book(root, "books/dep", '(in-package "ACL2")')
            top = book(root, "books/top",
                       '(in-package "ACL2")\n(include-book "dep")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"books/dep": dep})
            manifest(root, "certify-20260902T020000Z-2", status="passed",
                     passed={"books/top": top},
                     closure={"books/dep": digest("old dependency")})
            entry = green_check.audit(root, roots=["books/top"])["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "green")
            self.assertEqual(entry["certified_at_digest"], "certify-20260901T010000Z-1")
            self.assertEqual(entry["deps_moved_since"], [])

    def test_newer_failure_for_different_closure_does_not_poison_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dep = book(root, "books/dep", '(in-package "ACL2")')
            top = book(root, "books/top",
                       '(in-package "ACL2")\n(include-book "dep")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"books/dep": dep})
            manifest(root, "certify-20260902T020000Z-2", status="failed",
                     failed={"books/top": top},
                     closure={"books/dep": digest("old dependency")})
            entry = green_check.audit(root, roots=["books/top"])["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "green")
            self.assertIsNone(entry["failed_at_digest"])

    def test_newer_failure_for_exact_closure_overrides_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dep = book(root, "books/dep", '(in-package "ACL2")')
            top = book(root, "books/top",
                       '(in-package "ACL2")\n(include-book "dep")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"books/dep": dep})
            manifest(root, "certify-20260902T020000Z-2", status="failed",
                     failed={"books/top": top}, closure={"books/dep": dep})
            entry = green_check.audit(root, roots=["books/top"])["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "red")
            self.assertEqual(entry["failed_at_digest"], "certify-20260902T020000Z-2")

    def test_missing_failure_closure_digests_remain_conservative(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            dep = book(root, "books/dep", '(in-package "ACL2")')
            top = book(root, "books/top",
                       '(in-package "ACL2")\n(include-book "dep")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"books/dep": dep})
            manifest(root, "certify-20260902T020000Z-2", status="failed",
                     failed={"books/top": top})
            entry = green_check.audit(root, roots=["books/top"])["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "red")


class AttributionTests(unittest.TestCase):
    """Which book a failing run blames, from whichever field it carries."""

    def test_success_markers_attribute_a_failure_with_no_per_book_verdicts(self):
        """The oldest manifests predate `book_results`.  A requested book whose
        expected marker was never observed did not certify in that run."""
        body = {
            "run_id": "certify-20260901T010000Z-1",
            "status": "failed",
            "requested_books": ["books/a", "books/b"],
            "expected_success_markers": ["marker-a", "marker-b"],
            "observed_success_markers": ["marker-a"],
        }
        self.assertEqual(green_check.failed_books(body), {"books/b"})

    def test_a_run_that_attributes_nothing_is_counted_not_guessed(self):
        body = {"run_id": "certify-20260901T010000Z-1", "status": "failed",
                "requested_books": ["books/a", "books/b"]}
        self.assertEqual(green_check.failed_books(body), set())


def index(root: Path, *run_ids: str) -> None:
    """File these synthetic manifests in the committed index, so they read
    as archived (committed) evidence rather than local drafts."""
    import evidence_store  # noqa: E402  (tools/ is on sys.path above)
    entries = dict(evidence_store.read_index(root))
    for run_id in run_ids:
        rel = f"planning/evidence/manifests/{run_id}.json"
        data = (root / rel).read_bytes()
        entries[rel] = (hashlib.sha256(data).hexdigest(), len(data))
    evidence_store.write_index(root, entries)


def localize(root: Path, run_id: str) -> None:
    """Move a synthetic manifest to this worktree's unarchived build/acl2."""
    source = root / "planning" / "evidence" / "manifests" / f"{run_id}.json"
    target = root / "build" / "acl2" / run_id / "manifest.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    source.rename(target)


class ReleaseGateTests(unittest.TestCase):
    """S009 (sweep 2026-10-03): `--strict` and `--profile --strict` are the
    release cut's check (tools/cut_release.sh gate 05, packaging/
    release-tarball.sh step 1) and must mean what planning/release-v6.6.0.md
    says: every book green at its current digest AND closure in a committed
    manifest.  They counted only `red`, so a book nobody certified (absent,
    never), a green whose dependency moved (stale) and a green backed only by
    an unfiled local run (unarchived) all passed.  Each case below is one bad
    input the gate must refuse, plus the all-good tree it must accept, so the
    gate is shown able to pass as well as to fail."""

    def tree(self, root: Path) -> dict[str, str]:
        found = {
            "books/dep": book(root, "books/dep", '(in-package "ACL2")'),
            "books/top": book(root, "books/top",
                              '(in-package "ACL2")\n(include-book "dep")\n'),
        }
        manifest(root, "certify-20260901T010000Z-1", status="passed",
                 passed=found)
        return found

    @staticmethod
    def standings(rows: list[dict]) -> dict[str, str]:
        return {row["book"]: row["verdict"] for row in rows}

    def test_all_green_and_archived_passes_both_gates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.tree(root)
            index(root, "certify-20260901T010000Z-1")
            report = green_check.audit(root, roots=["books/top"])
            rows = green_check.strict_rows(report)
            self.assertEqual(self.standings(rows),
                             {"books/dep": "green", "books/top": "green"})
            answer = green_check.profile_gate(report, "synthetic", root=root,
                                              roots=["books/top"])
            self.assertEqual(answer["not_green"], [])
            self.assertEqual(answer["books"], 2)

    def test_a_book_nobody_certified_fails_strict_and_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.tree(root)
            index(root, "certify-20260901T010000Z-1")
            book(root, "books/new", '(in-package "ACL2") ; never certified')
            report = green_check.audit(root, roots=["books/top", "books/new"])
            self.assertEqual(report["counts"]["red"], 0)  # the old gate's input
            self.assertEqual(self.standings(green_check.strict_rows(report))["books/new"],
                             "absent")
            answer = green_check.profile_gate(report, "synthetic", root=root,
                                              roots=["books/top", "books/new"])
            self.assertEqual(answer["not_green"], ["books/new"])
            self.assertIn("absent=1", green_check.profile_lines(answer)[0])

    def test_a_green_whose_dependency_moved_is_stale_in_the_release_gates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            found = self.tree(root)
            # dep is recertified alone at new bytes; top's run is at old dep.
            changed = book(root, "books/dep", '(in-package "ACL2") ; moved')
            manifest(root, "certify-20260902T010000Z-2", status="passed",
                     passed={"books/dep": changed})
            index(root, "certify-20260901T010000Z-1", "certify-20260902T010000Z-2")
            report = green_check.audit(root, roots=["books/top"])
            entry = report["books_by_verdict"]["books/top"]
            self.assertEqual(entry["verdict"], "green")       # the audit's word
            self.assertEqual(entry["digest_sha256"], found["books/top"])
            self.assertEqual(self.standings(green_check.strict_rows(report)),
                             {"books/dep": "green", "books/top": "stale"})
            answer = green_check.profile_gate(report, "synthetic", root=root,
                                              roots=["books/top"])
            self.assertEqual(answer["not_green"], ["books/top"])
            self.assertEqual(self.standings(answer["rows"])["books/top"], "stale")

    def test_a_green_only_in_an_unfiled_local_run_is_unarchived(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.tree(root)  # written, never indexed: a local draft
            report = green_check.audit(root, roots=["books/top"])
            self.assertEqual(report["books_by_verdict"]["books/top"]["verdict"], "green")
            answer = green_check.profile_gate(report, "synthetic", root=root,
                                              roots=["books/top"])
            self.assertEqual(self.standings(answer["rows"]),
                             {"books/dep": "unarchived", "books/top": "unarchived"})
            self.assertTrue(all(row["verdict"] == "unarchived"
                                for row in green_check.strict_rows(report)))

    def test_merge_gate_uses_the_same_standing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.tree(root)
            report = green_check.audit(root, roots=["books/top"])
            answer = green_check.gate(report, ["books/dep"],
                                      green_check.dependents(root, report, ["books/dep"]))
            self.assertEqual(answer["not_green"], ["books/dep", "books/top"])


class ArchivedGreenAnswersTests(unittest.TestCase):
    """S127: committed output (planning/proofs.json's status, generated from
    `green_at_these_bytes`) must not depend on this worktree's build/acl2."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name).resolve()
        self.found = book(self.root, "books/solo", '(in-package "ACL2") ; solo')
        manifest(self.root, "certify-20260901T010000Z-1", status="passed",
                 passed={"books/solo": self.found})
        index(self.root, "certify-20260901T010000Z-1")

    def tearDown(self):
        self.directory.cleanup()

    def test_a_newer_local_green_does_not_hide_the_archived_one(self):
        manifest(self.root, "certify-20260905T010000Z-5", status="passed",
                 passed={"books/solo": self.found})
        localize(self.root, "certify-20260905T010000Z-5")
        entry = green_check.audit(self.root, roots=["books/solo"])["books_by_verdict"]["books/solo"]
        self.assertEqual(entry["certified_at_digest"], "certify-20260901T010000Z-1")
        self.assertTrue(entry["certified_archived"])
        self.assertEqual(entry["green_local_unarchived"], "certify-20260905T010000Z-5")
        self.assertTrue(green_check.green_at_these_bytes(entry))

    def test_committed_only_audit_ignores_a_local_red(self):
        manifest(self.root, "certify-20260905T010000Z-5", status="failed",
                 failed={"books/solo": self.found})
        localize(self.root, "certify-20260905T010000Z-5")
        here = green_check.audit(self.root, roots=["books/solo"])["books_by_verdict"]["books/solo"]
        self.assertEqual(here["verdict"], "red")  # this tree's own view keeps it
        committed = green_check.audit(self.root, roots=["books/solo"],
                                      include_local=False)["books_by_verdict"]["books/solo"]
        self.assertEqual(committed["verdict"], "green")
        self.assertTrue(green_check.green_at_these_bytes(committed))


class RealManifestsTests(unittest.TestCase):
    """Over this tree's own archive: it runs, and every book gets one answer."""

    @classmethod
    def setUpClass(cls):
        cls.report = green_check.audit()

    def test_every_book_in_the_closure_gets_exactly_one_answer(self):
        counts = self.report["counts"]
        self.assertEqual(sum(counts.values()), self.report["books"])
        self.assertEqual(self.report["books"],
                         len(self.report["books_by_verdict"]))
        self.assertGreater(self.report["books"], self.report["roots"] // 2)

    def test_it_read_the_committed_archive(self):
        self.assertGreater(self.report["manifests_archived"], 100)
        self.assertLessEqual(self.report["manifests_archived"],
                             self.report["manifests"])

    def test_the_command_line_runs_and_says_which_books_are_owed(self):
        finished = subprocess.run(
            [sys.executable, "tools/green_check.py", "--summary"],
            cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(finished.returncode, 0, finished.stderr)
        self.assertEqual(len(finished.stdout.strip().splitlines()), 3)
        self.assertIn("RED at digest", finished.stdout)

    def test_strict_exits_one_exactly_when_a_book_is_not_green_at_these_bytes(self):
        finished = subprocess.run(
            [sys.executable, "tools/green_check.py", "--summary", "--strict"],
            cwd=ROOT, capture_output=True, text=True)
        rows = green_check.strict_rows(self.report)
        self.assertEqual(finished.returncode,
                         1 if any(row["verdict"] != "green" for row in rows) else 0,
                         finished.stdout + finished.stderr)

    def test_json_is_one_object_a_reader_can_load(self):
        finished = subprocess.run(
            [sys.executable, "tools/green_check.py", "--json"],
            cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(finished.returncode, 0, finished.stderr)
        loaded = json.loads(finished.stdout)
        self.assertEqual(loaded["schema"], "fn-green-check-v1")
        self.assertEqual(sum(loaded["counts"].values()), loaded["books"])


class MergeGateTests(unittest.TestCase):
    """--changed-since: a changed book merges with everything that includes it.

    Finding F4 of planning/review-2026-09-22-proof-engineering.md: on
    2026-09-21 behaviour landed under invariant books nobody recertified.  The
    gate reads the branch's changed books, the audited books whose closure
    reaches one, and each verdict at the bytes a merge would carry.
    """

    def tree(self, root: Path) -> dict:
        dep = book(root, "books/dep", '(in-package "ACL2")')
        top = book(root, "books/top", '(in-package "ACL2")\n(include-book "dep")\n')
        aside = book(root, "books/aside", '(in-package "ACL2") ; unrelated')
        manifest(root, "certify-20260901T010000Z-1", status="passed",
                 passed={"books/top": top, "books/dep": dep, "books/aside": aside})
        index(root, "certify-20260901T010000Z-1")
        return green_check.audit(root, roots=["books/top", "books/aside"])

    def test_a_changed_book_names_the_books_that_include_it_and_nothing_else(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            report = self.tree(root)
            deps = green_check.dependents(root, report, ["books/dep"])
            self.assertEqual(deps, {"books/top": ["books/dep"]})

    def test_host_include_is_a_dependency_not_an_uncertifiable_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            book(root, "books/dep", '(in-package "ACL2")')
            book(root, "host/helper", '(in-package "ACL2")\n'
                 '(include-book "../books/dep")\n')
            book(root, "books/top", '(in-package "ACL2")\n'
                 '(include-book "../host/helper")\n')
            report = green_check.audit(root, roots=["books/top"])
            self.assertIn("host/helper", report["books_by_verdict"])
            self.assertEqual(green_check.dependents(root, report, ["books/dep"]),
                             {"books/top": ["books/dep"]})

    def test_the_gate_is_green_only_when_every_row_is_green(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            report = self.tree(root)
            answer = green_check.gate(report, ["books/dep"],
                                      green_check.dependents(root, report, ["books/dep"]))
            self.assertEqual(answer["not_green"], [])
            # Now the dependency's bytes move and nobody certifies: the changed
            # book reads `never`, its dependent stays green at its own bytes
            # (the audit's rule), but the merge gate rejects its stale closure.
            book(root, "books/dep", '(in-package "ACL2") ; edited')
            report = green_check.audit(root, roots=["books/top", "books/aside"])
            answer = green_check.gate(report, ["books/dep"],
                                      green_check.dependents(root, report, ["books/dep"]))
            self.assertEqual(answer["not_green"], ["books/dep", "books/top"])
            roles = {row["book"]: row["role"] for row in answer["rows"]}
            self.assertEqual(roles, {"books/dep": "changed", "books/top": "dependent"})
            self.assertNotIn("books/aside", roles)

    def test_recertifying_only_dependency_does_not_qualify_its_consumer(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.tree(root)
            changed = book(root, "books/dep", '(in-package "ACL2") ; new contract')
            manifest(root, "certify-20260902T010000Z-2", status="passed",
                     passed={"books/dep": changed})
            index(root, "certify-20260902T010000Z-2")
            report = green_check.audit(root, roots=["books/top", "books/aside"])
            answer = green_check.gate(report, ["books/dep"],
                                     green_check.dependents(root, report, ["books/dep"]))
            self.assertEqual(answer["not_green"], ["books/top"])
            top_row = next(row for row in answer["rows"] if row["book"] == "books/top")
            self.assertEqual(top_row["verdict"], "stale")
            self.assertEqual(top_row["deps_moved_since"], ["books/dep.lisp"])
            self.assertTrue(any("stale" in line and "books/dep.lisp" in line
                                for line in green_check.gate_lines(answer)))
            top_digest = report["books_by_verdict"]["books/top"]["digest_sha256"]
            manifest(root, "certify-20260903T010000Z-3", status="passed",
                     passed={"books/dep": changed, "books/top": top_digest})
            index(root, "certify-20260903T010000Z-3")
            report = green_check.audit(root, roots=["books/top", "books/aside"])
            answer = green_check.gate(report, ["books/dep"],
                                     green_check.dependents(root, report, ["books/dep"]))
            self.assertEqual(answer["not_green"], [])

    def test_a_changed_book_no_root_reaches_is_unaudited_and_not_green(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            report = self.tree(root)
            answer = green_check.gate(report, ["tests/acl2/orphan-tests"], {})
            self.assertEqual(answer["rows"][0]["verdict"], "unaudited")
            self.assertEqual(answer["not_green"], ["tests/acl2/orphan-tests"])

    def test_changed_books_reads_the_working_tree_against_the_merge_base(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            git = lambda *words: subprocess.run(  # noqa: E731
                ["git", *words], cwd=root, check=True, capture_output=True, text=True)
            git("init", "-q", "-b", "main")
            git("config", "user.email", "t@example.invalid")
            git("config", "user.name", "t")
            # This temporary history tests diff selection, not the user's
            # signing agent or repository hooks.
            git("config", "commit.gpgsign", "false")
            hooks = root / "empty-hooks"
            hooks.mkdir()
            git("config", "core.hooksPath", str(hooks))
            book(root, "books/dep", '(in-package "ACL2")')
            book(root, "tests/acl2/dep-tests", '(in-package "ACL2")')
            (root / "notes.md").write_text("x")
            git("add", "-A")
            git("commit", "-q", "-m", "base")
            git("checkout", "-q", "-b", "lane")
            book(root, "books/dep", '(in-package "ACL2") ; committed on the lane')
            git("commit", "-q", "-am", "lane edit")
            book(root, "tests/acl2/dep-tests", '(in-package "ACL2") ; uncommitted')
            (root / "notes.md").write_text("prose does not count")
            self.assertEqual(green_check.changed_books(root, "main"),
                             ["books/dep", "tests/acl2/dep-tests"])

    def test_a_host_include_edit_and_an_untracked_book_reach_the_gate(self):
        """S056: a lane that edits only host/page-read-host.lisp (which books
        include), or creates a book without `git add`, used to see
        "no book or test book differs" and exit 0 under --strict."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            git = lambda *words: subprocess.run(  # noqa: E731
                ["git", *words], cwd=root, check=True, capture_output=True, text=True)
            git("init", "-q", "-b", "main")
            git("config", "user.email", "t@example.invalid")
            git("config", "user.name", "t")
            git("config", "commit.gpgsign", "false")
            hooks = root / "empty-hooks"
            hooks.mkdir()
            git("config", "core.hooksPath", str(hooks))
            helper = book(root, "host/helper", '(in-package "ACL2")')
            top = book(root, "books/top", '(in-package "ACL2")\n'
                       '(include-book "../host/helper")\n')
            manifest(root, "certify-20260901T010000Z-1", status="passed",
                     passed={"books/top": top}, closure={"host/helper": helper})
            index(root, "certify-20260901T010000Z-1")
            git("add", "-A")
            git("commit", "-q", "-m", "base")
            git("checkout", "-q", "-b", "lane")
            book(root, "host/helper", '(in-package "ACL2") ; host edit')
            book(root, "books/fresh", '(in-package "ACL2") ; never added')
            changed = green_check.changed_books(root, "main")
            self.assertEqual(changed, ["books/fresh", "host/helper"])
            report = green_check.audit(root, roots=["books/top", "books/fresh"])
            answer = green_check.gate(report, green_check.certifiable(changed),
                                      green_check.dependents(root, report, changed))
            verdicts = {row["book"]: row["verdict"] for row in answer["rows"]}
            self.assertEqual(verdicts, {"books/fresh": "absent", "books/top": "stale"})
            self.assertEqual(answer["not_green"], ["books/fresh", "books/top"])

    def test_the_gate_lines_say_the_counts_and_every_row(self):
        answer = green_check.gate(
            {"books_by_verdict": {"books/a": {"verdict": "green",
                                              "certified_archived": True},
                                  "books/b": {"verdict": "red"}}},
            ["books/a"], {"books/b": ["books/a"]})
        lines = green_check.gate_lines(answer)
        self.assertIn("1 changed books, 1 books include one; 1 not green", lines[0])
        self.assertTrue(any("red" in line and "books/b" in line and "<- books/a" in line
                            for line in lines[1:]))

    def test_the_command_line_gate_runs_on_this_tree(self):
        result = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "green_check.py"),
             "--changed-since", "HEAD"],
            capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith("green-gate:"), result.stdout)


if __name__ == "__main__":
    unittest.main()
