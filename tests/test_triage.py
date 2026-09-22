"""tools/triage.py: every independent red in one closure, and nothing published.

The reds under test are real.  `tests/fixtures/triage/` holds three
unmodified per-book logs from persvati runs of 2026-09-22
(`books--bp-ingress` and `books--owner` are whole; `books--checkpoint...tail`
is the last 110 lines of a 1909-line log, which is where its failure is), and
they are the reason the classifier cannot be written against a single phrase:
ACL2 wraps "There is no certificate on file" at its pretty-printer margin, so
`bp-ingress` breaks it after "There is" and `owner` after "no certificate".
The same classifier over the two archived runs the review cites agrees with
what the freeze lanes found by hand and then some: 2 independent of 53
failures in `certify-20260922T121645Z-3620455`, and in
`certify-20260922T075332Z-1349583` the two books the lane named plus three
test books whose own errors were buried under 90 cascades.  (Spelling run ids
is safe only here: `tools/evidence_manifests.py` excludes `tests/test_*.py`
from its citation sweep, because a run id in a unit test is a fixture.)

The farm is faked the way `tests/test_farm.py` fakes it, through the module
seam `farm.RUN`, so these tests read the exact commands a triage round would
issue.  Two of them are the whole point of the tool's discipline: every runner
invocation carries `--no-publish`, and nothing a triage run produces is
rsynced or published anywhere.
"""

from __future__ import annotations

import contextlib
import hashlib
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
FIXTURES = Path(__file__).resolve().parent / "fixtures" / "triage"
sys.path.insert(0, str(ROOT / "tools"))

import farm  # noqa: E402
import triage  # noqa: E402


def fixture(name: str) -> str:
    return (FIXTURES / name).read_text(encoding="utf-8", errors="replace")


# --------------------------------------------------------------------------
# reading one book's log
# --------------------------------------------------------------------------


class ClassificationTests(unittest.TestCase):
    """Cascade, timeout and independent, told apart on real ACL2 output."""

    def test_a_cascade_wrapped_after_there_is(self):
        finding = triage.classify("books/bp-ingress",
                                  fixture("books--bp-ingress.certify.log"),
                                  0, 1, 0.59, [])
        self.assertEqual(finding.kind, "cascade")
        self.assertEqual(finding.blocked_by, ["books/store-node-invariants"])
        self.assertIsNone(finding.first_error)

    def test_a_cascade_wrapped_after_no_certificate(self):
        log = fixture("books--owner.certify.log")
        # The wrap is in a different place in each of the two logs, which is
        # why the phrase is matched on whitespace-collapsed text.
        self.assertIn("There is\nno certificate on file", fixture(
            "books--bp-ingress.certify.log"))
        self.assertIn("There is no certificate\non file", log)
        finding = triage.classify("books/owner", log, 0, 1, 0.01, [])
        self.assertEqual(finding.kind, "cascade")
        self.assertEqual(finding.blocked_by, ["books/store-observed"])

    def test_an_independent_red_keeps_its_error_and_its_checkpoint(self):
        finding = triage.classify(
            "books/checkpoint", fixture("books--checkpoint.certify.log.tail"),
            0, 2, 103.0, ["assuming books/store-node-traces at ..."])
        self.assertEqual(finding.kind, "independent")
        self.assertIn("ACL2 Error [Failure]", finding.first_error)
        self.assertIn("FN-CHECKPOINT-RESTORE-REJECTS-FRONTIER-REUSE",
                      finding.first_error)
        self.assertIn("Key checkpoint", finding.checkpoint)
        self.assertIn("Subgoal", finding.checkpoint)
        self.assertEqual(finding.round, 2)
        self.assertEqual(finding.assumptions,
                         ["assuming books/store-node-traces at ..."])

    def test_the_failure_restatement_is_not_a_second_error(self):
        """`[Failure] ... See :DOC failure` repeats a form already reported.

        It is the block that made every cascade look independent: ACL2
        restates the include-book failure without the sentence that says
        why, so the restatement has to inherit the earlier block's verdict.
        """
        errors = triage.acl2_errors(fixture("books--owner.certify.log"))
        self.assertEqual([error.restatement for error in errors],
                         [False, True, False])
        self.assertEqual([error.news for error in errors],
                         [False, False, False])
        self.assertTrue(errors[-1].wrapper)

    def test_a_timeout_is_read_from_the_exit_code_not_the_log(self):
        finding = triage.classify("books/feed-connection-invariants", "",
                                  "timed out after 300 seconds", 1, 300.4, [])
        self.assertEqual(finding.kind, "timeout")
        self.assertIsNone(finding.first_error)

    def test_a_failure_with_no_error_at_all_is_not_smoothed_over(self):
        finding = triage.classify("books/quiet", "nothing happened\n", 0, 1,
                                  1.0, [])
        self.assertEqual(finding.kind, "unexplained")

    def test_the_checkpoint_is_cut_and_says_so(self):
        log = ("*** Key checkpoint before reverting to proof by induction: ***"
               "\n\nSubgoal 3'\n" + "".join(f"(LINE {n})\n" for n in range(60)))
        cut = triage.key_checkpoint(log, limit=5)
        self.assertIn("Subgoal 3'", cut)
        self.assertIn("more lines", cut)
        self.assertEqual(len(cut.splitlines()), 7)

    def test_an_absolute_box_path_names_a_repository_book(self):
        self.assertEqual(
            triage.repository_book(
                "/home/ember/fn-gates/w31-treewide/books/store-node.lisp"),
            "books/store-node")
        self.assertEqual(
            triage.repository_book("/tank/fn/x/tests/acl2/owner-tests.lisp"),
            "tests/acl2/owner-tests")


# --------------------------------------------------------------------------
# the last source that ever certified
# --------------------------------------------------------------------------


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def git(root: Path, *arguments: str) -> None:
    subprocess.run(["git", "-C", str(root), *arguments], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def write_manifest(root: Path, run_id: str, *, passed: dict[str, str],
                   failed: dict[str, str] = {}) -> None:
    """One archived manifest with the fields the pass rule reads."""
    requested = sorted({**passed, **failed})
    markers = {name: f"FN_CERTIFY_SUCCESS {run_id} {name}" for name in requested}
    body = {
        "run_id": run_id,
        "status": "passed" if not failed else "failed",
        "archived_from": f"testbox:/tmp/{run_id}",
        "requested_books": requested,
        "expected_success_markers": [markers[name] for name in requested],
        "observed_success_markers": [markers[name] for name in passed],
        "book_results": {name: ("passed" if name in passed else "failed")
                         for name in requested},
        "book_failures": {name: ["no certificate on disk"] for name in failed},
        "source_digests_sha256": {f"{name}.lisp": found for name, found
                                  in {**passed, **failed}.items()},
        "certificate_digests_sha256": {name: digest(f"cert {run_id} {name}")
                                       for name in passed},
        "acl2_exit_codes": {name: 0 for name in requested},
    }
    archive = root / "planning" / "evidence" / "manifests"
    archive.mkdir(parents=True, exist_ok=True)
    (archive / f"{run_id}.json").write_text(json.dumps(body), encoding="utf-8")


OLD_B = '(in-package "ACL2")\n(include-book "a")\n(defthm b-old t)\n'
NEW_B = '(in-package "ACL2")\n(include-book "a")\n(defthm b-new nil)\n'


def synthetic_tree(root: Path) -> None:
    """Three books, a git history for the middle one, and two manifests.

    `books/b` was green yesterday at `OLD_B` and carries `NEW_B` now, which
    is the only shape a substitution can act on.  `books/a` and `books/c`
    are green and never-green at their current bytes respectively.
    """
    books = root / "books"
    books.mkdir(parents=True, exist_ok=True)
    (books / "a.lisp").write_text('(in-package "ACL2")\n(defthm a t)\n')
    (books / "b.lisp").write_text(OLD_B)
    (books / "c.lisp").write_text('(in-package "ACL2")\n(include-book "b")\n')
    git(root, "init", "-q", "-b", "main")
    git(root, "config", "user.email", "lane@example.invalid")
    git(root, "config", "user.name", "lane")
    git(root, "add", "books")
    git(root, "commit", "-q", "-m", "the green b")
    (books / "b.lisp").write_text(NEW_B)
    git(root, "add", "books/b.lisp")
    git(root, "commit", "-q", "-m", "widen b under its invariants")
    write_manifest(root, "certify-20260921T090000Z-1",
                   passed={"books/a": digest((books / "a.lisp").read_text()),
                           "books/b": digest(OLD_B),
                           "books/c": digest((books / "c.lisp").read_text())})
    write_manifest(root, "certify-20260922T090000Z-2",
                   passed={"books/a": digest((books / "a.lisp").read_text())},
                   failed={"books/b": digest(NEW_B),
                           "books/c": digest((books / "c.lisp").read_text())})


class LastGreenSourceTests(unittest.TestCase):
    """Which bytes to substitute, and the three reasons there are none."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name).resolve()
        synthetic_tree(self.root)
        self.audit = triage.green_check.audit(
            self.root, ["books/c", "books/b", "books/a"])
        self.runs = {run.run_id: run
                     for run, _ in triage.green_check.manifests(self.root)}

    def tearDown(self):
        self.directory.cleanup()

    def test_it_finds_the_commit_whose_bytes_are_the_green_digest(self):
        answer = triage.substitution_for(self.root, self.audit, self.runs,
                                         "books/b", digest(NEW_B))
        self.assertNotIsInstance(answer, str)
        substitution, blob = answer
        self.assertEqual(blob.decode(), OLD_B)
        self.assertEqual(substitution.digest, digest(OLD_B))
        self.assertEqual(substitution.subject, "the green b")
        self.assertIn("last green digest", substitution.sentence())
        self.assertIn(substitution.revision[:12], substitution.sentence())

    def test_a_book_green_at_the_digest_it_carries_cannot_be_substituted(self):
        """Its failure is dependency drift, and saying so is the finding."""
        answer = triage.substitution_for(self.root, self.audit, self.runs,
                                         "books/c", self.audit[
                                             "books_by_verdict"]["books/c"][
                                             "digest_sha256"])
        self.assertIsInstance(answer, str)
        self.assertIn("digest it already carries", answer)

    def test_a_book_with_no_green_anywhere_cannot_be_substituted(self):
        answer = triage.substitution_for(self.root, self.audit, self.runs,
                                         "books/nowhere", "0" * 64)
        self.assertIsInstance(answer, str)
        self.assertIn("never green", answer)

    def test_a_green_digest_no_commit_holds_is_reported_as_such(self):
        self.runs["certify-20260921T090000Z-1"].sources["books/b.lisp"] = "f" * 64
        answer = triage.substitution_for(self.root, self.audit, self.runs,
                                         "books/b", digest(NEW_B))
        self.assertIsInstance(answer, str)
        self.assertIn("no commit in this repository", answer)


# --------------------------------------------------------------------------
# a whole triage, over a faked box
# --------------------------------------------------------------------------


CASCADE = """
ACL2 Error in ( INCLUDE-BOOK "b" ...):  There is
no certificate on file for
"{remote}/books/b.lisp".
See :DOC uncertified-books.

ACL2 Error [Failure] in ( INCLUDE-BOOK "b" ...):
See :DOC failure.

ACL2 Error [Failure] in (CERTIFY-BOOK "books/c" ...):  See
:DOC failure.
"""

OWN = """
*** Key checkpoint before reverting to proof by induction: ***

Subgoal 2.1'
(IMPLIES (FN-{name}-P X) (EQUAL X X))

ACL2 Error [Failure] in ( DEFTHM FN-{name}-HOLDS
...):  See :DOC failure.

ACL2 Error [Failure] in (CERTIFY-BOOK "books/{book}" ...):  See
:DOC failure.
"""

INSTALLED = ("artifact-set NONE origin NONE source NONE toolchain NONE; "
             "installed 0, kept 0, missing 3, removed 3\n")


class FakeBox:
    """A box that runs scripted rounds: one manifest and one log set each.

    Every command the tool issues is recorded, which is how the two
    prohibitions are checked -- no `--no-publish`-less runner, and no rsync
    or publish that would move a certificate anywhere.
    """

    def __init__(self, rounds: list[dict]) -> None:
        self.rounds = rounds
        self.started = 0
        self.commands: list[list[str]] = []

    @property
    def evidence(self) -> str:
        return f"build/acl2/certify-2026092{self.started}T000000Z-{self.started}"

    def __call__(self, command, **kwargs):
        self.commands.append(list(command))
        output = ""
        if command[0] == "ssh":
            script = command[-1]
            if script == "echo $HOME":
                output = "/home/ember\n"
            elif "tools/certs.py" in script:
                output = INSTALLED
            elif "nohup sh -c" in script:
                self.started += 1
                output = "FN_FARM_STARTED x 1\n"
            elif "STATUS" in script:
                output = "STATUS 1\nMARKERS 1\nTAIL done\n"
            elif script.startswith("cat "):
                output = f"Certification evidence: {self.evidence}\n"
        elif command[0] == "rsync" and command[-2].startswith("persvati:"):
            self.deliver(Path(command[-1]))
        return subprocess.CompletedProcess(command, 0, stdout=output, stderr="")

    def deliver(self, into: Path) -> None:
        """Write the round's manifest and per-book logs where rsync would."""
        into.mkdir(parents=True, exist_ok=True)
        scripted = self.rounds[self.started - 1]
        (into / "manifest.json").write_text(json.dumps(scripted["manifest"]))
        for book, log in scripted["logs"].items():
            (into / (book.replace("/", "--") + ".certify.log")).write_text(log)

    def scripts(self) -> list[str]:
        return [command[-1] for command in self.commands if command[0] == "ssh"]

    def runner_scripts(self) -> list[str]:
        return [script for script in self.scripts() if "nohup sh -c" in script]


def manifest_for(results: dict[str, str], walls: dict[str, float],
                 codes: dict[str, object] | None = None) -> dict:
    return {"book_results": results, "book_wall_seconds": walls,
            "acl2_exit_codes": codes or {book: 0 for book in results},
            "certify_wall_seconds": sum(walls.values()), "timeout_seconds": 300}


class WholeTriageTests(unittest.TestCase):
    """Two rounds over a three-book closure, with nothing published."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name).resolve()
        synthetic_tree(cls.root)
        cls.remote = "/home/ember/fn-gates/w32-triage"
        rounds = [
            {"manifest": manifest_for(
                {"books/a": "passed", "books/b": "failed", "books/c": "failed"},
                {"books/a": 1.0, "books/b": 12.5, "books/c": 0.1}),
             "logs": {"books/b": OWN.format(name="B", book="b"),
                      "books/c": CASCADE.format(remote=cls.remote)}},
            {"manifest": manifest_for(
                {"books/a": "passed", "books/b": "passed", "books/c": "failed"},
                {"books/a": 1.0, "books/b": 0.4, "books/c": 31.0}),
             "logs": {"books/c": OWN.format(name="C", book="c")}},
        ]
        cls.box = FakeBox(rounds)
        with mock.patch.object(farm, "RUN", cls.box), \
                mock.patch.object(farm, "SLEEP", lambda seconds: None), \
                mock.patch.dict(os.environ,
                                {"FN_CERT_CACHE": str(cls.root / "cache")}), \
                contextlib.redirect_stderr(io.StringIO()), \
                contextlib.redirect_stdout(io.StringIO()):
            cls.report = triage.triage(
                "persvati", ["books/c"], root=cls.root,
                remote_root=cls.remote, acl2="/opt/acl2", cache="/home/x/cache",
                budget_seconds=300, rounds=4, jobs=6, poll_seconds=0)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_two_rounds_answer_a_two_deep_chain(self):
        self.assertEqual(len(self.report["rounds"]), 2)
        self.assertEqual(self.report["rounds"][0]["kinds"],
                         {"independent": 1, "timeout": 0, "unexplained": 0,
                          "cascade": 1})
        self.assertEqual(self.report["rounds"][1]["kinds"]["independent"], 1)

    def test_every_independent_red_is_reported_with_its_round(self):
        found = {one["book"]: one for one in self.report["findings"]}
        self.assertEqual(sorted(found), ["books/b", "books/c"])
        self.assertEqual(found["books/b"]["round"], 1)
        self.assertEqual(found["books/c"]["round"], 2)
        self.assertIn("FN-C-HOLDS", found["books/c"]["first_error"])
        self.assertIn("Subgoal 2.1'", found["books/c"]["key_checkpoint"])

    def test_the_assumption_stack_names_the_substituted_book(self):
        found = {one["book"]: one for one in self.report["findings"]}
        self.assertEqual(found["books/b"]["assuming"], [])
        self.assertEqual(len(found["books/c"]["assuming"]), 1)
        self.assertIn("assuming books/b at its last green digest",
                      found["books/c"]["assuming"][0])
        self.assertEqual([one["book"] for one in self.report["substitutions"]],
                         ["books/b"])

    def test_the_substitution_goes_to_the_box_and_not_to_the_worktree(self):
        sent = [command for command in self.box.commands
                if command[0] == "rsync"
                and command[-1].endswith("/books/b.lisp")]
        self.assertEqual(len(sent), 1, sent)
        self.assertEqual(sent[0][-1], f"persvati:{self.remote}/books/b.lisp")
        self.assertEqual(Path(sent[0][-2]).read_text(), OLD_B)
        # The worktree still carries what it carried.
        self.assertEqual((self.root / "books" / "b.lisp").read_text(), NEW_B)

    def test_every_runner_invocation_carries_no_publish(self):
        scripts = self.box.runner_scripts()
        self.assertEqual(len(scripts), 2)
        for script in scripts:
            self.assertIn("--no-publish", script)
            self.assertIn("--closure", script)
            self.assertFalse(farm.publishes(script))

    def test_no_certificate_and_no_manifest_leaves_the_box(self):
        for command in self.box.commands:
            if command[0] == "rsync":
                self.assertNotIn("--include=*.cert", command)
                self.assertNotIn("--include=*.port", command)
        publishing = [script for script in self.box.scripts()
                      if "certs.py" in script and "publish" in script]
        self.assertEqual(publishing, [])
        self.assertFalse((self.root / "build" / "acl2").exists())
        archive = self.root / "planning" / "evidence" / "manifests"
        self.assertEqual(sorted(path.name for path in archive.glob("*.json")),
                         ["certify-20260921T090000Z-1.json",
                          "certify-20260922T090000Z-2.json"])

    def test_the_report_says_what_it_is_not(self):
        document = triage.markdown(self.report)
        self.assertIn("not evidence of certification", document)
        self.assertIn("assuming books/b at its last green digest", document)
        self.assertIn("## Independent reds (2)", document)
        self.assertIn("Key checkpoint", document)
        # A certify run id in the report would read as a certification claim
        # and would fail `tools/evidence_manifests.py check` when committed.
        self.assertNotIn(self.box.evidence.split("/")[-1], document)

    def test_the_report_is_written_where_it_says_it_is(self):
        with contextlib.redirect_stdout(io.StringIO()):
            document, data = triage.write_report(self.report)
        self.assertTrue(document.is_file() and data.is_file())
        self.assertEqual(json.loads(data.read_text())["schema"], "fn-triage-v1")
        self.assertTrue(str(document).startswith(
            str(self.root / triage.OUT_REL)))


class NeverPublishTests(unittest.TestCase):
    """The guard that stands between a triage run and the box's cache."""

    def test_farm_reads_the_publication_off_the_command_line(self):
        common = dict(host="persvati", root=Path("/tmp/x"), identifier="run-1",
                      books=["books/a"], jobs=4, timeout_seconds=300,
                      affected_by=[])
        self.assertTrue(farm.publishes(farm.remote_script(**common)))
        self.assertFalse(farm.publishes(
            farm.remote_script(**common, no_publish=True)))

    def test_submit_refuses_to_start_a_run_that_would_publish(self):
        """The check is on the script, not on the argument that asked for it."""
        box = FakeBox([])
        with mock.patch.object(farm, "RUN", box), \
                mock.patch.object(farm, "remote_script",
                                  lambda *a, **k: "python3 certify_books.py"), \
                contextlib.redirect_stderr(io.StringIO()), \
                tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(farm.FarmError) as refused:
                farm.submit("persvati", Path(directory), ["books/a"], 4, 300,
                            [], no_publish=True)
        self.assertIn("would publish anyway", str(refused.exception))
        self.assertEqual(box.runner_scripts(), [])


if __name__ == "__main__":
    unittest.main()
