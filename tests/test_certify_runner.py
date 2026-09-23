"""Regression checks for evidence that must fail closed."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock

from tests.test_certs import TEST_COMPATIBILITY

SPEC = importlib.util.spec_from_file_location(
    "certify_books", Path(__file__).resolve().parents[1] / "tools" / "certify_books.py"
)
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


FAKE_ACL2 = r"""#!/bin/sh
# Stands in for the ACL2 executable.  It reads the runner's driver on stdin,
# echoes the driver's own success marker, and records when each certification
# started and finished so a test can check the schedule the runner chose.
driver=$(cat)
case "$driver" in
  *FN_ACL2_VERSION*)
    echo "This is SBCL 2.6.8 (fake harness)"
    echo "ACL2 !>FN_ACL2_VERSION 8.7"
    exit 0 ;;
esac
book=$(printf '%s\n' "$driver" | sed -n 's/.*(certify-book "\([^"]*\)".*/\1/p' | head -1)
marker=$(printf '%s\n' "$driver" | grep -oE '(FN_CERTIFY_SUCCESS|FN_PCERT_WAVE (CREATE|CONVERT)) [0-9a-f]+ [0-9a-f]+' | head -1)
# Which provisional wave, if any, this invocation is.  Create skips proofs,
# Convert does them and writes no certificate, Complete writes the
# certificate and refuses while an included book has none.
wave=$(printf '%s\n' "$driver" | sed -n 's/.*:pcert :\([a-z]*\).*/\1/p' | head -1)
printf 'start %s%s\n' "$book" "${wave:+ $wave}" >> "$FAKE_EVENTS"
sleep "${FAKE_DELAY:-0.2}"
case " ${FAKE_FAIL:-} " in
  *" $book "*)
    printf 'end %s%s\n' "$book" "${wave:+ $wave}" >> "$FAKE_EVENTS"
    echo "ACL2 Error in ( CERTIFY-BOOK ...):  the fake harness refused this book."
    exit 1 ;;
esac
if [ "$wave" = convert ]; then
  case " ${FAKE_CONVERT_FAIL:-} " in
    *" $book "*)
      printf 'end %s %s\n' "$book" "$wave" >> "$FAKE_EVENTS"
      echo "ACL2 Error [Failure] in ( DEFTHM FAKE-HOLDS ...):  See :DOC failure."
      exit 0 ;;
  esac
fi
if [ "$wave" = complete ]; then
  dir=$(dirname "$book")
  for inc in $(sed -n 's/^(include-book "\([^"]*\)").*/\1/p' "$book.lisp"); do
    if [ ! -f "$dir/$inc.cert" ]; then
      printf 'end %s %s\n' "$book" "$wave" >> "$FAKE_EVENTS"
      # ACL2 wraps this sentence at its pretty-printer margin; the wrap is
      # part of what the triage classifier has to survive.
      echo "ACL2 Error in ( INCLUDE-BOOK \"$inc\" ...):  There is"
      echo "no certificate on file for"
      echo "\"$PWD/$dir/$inc.lisp\"."
      exit 0
    fi
  done
fi
# Real ACL2's shape when certify-book fails: the inner ld returns, the marker
# form is never reached, no certificate is written -- and the driver's (quit)
# still exits 0.
case " ${FAKE_QUIET_FAIL:-} " in
  *" $book "*)
    printf 'end %s%s\n' "$book" "${wave:+ $wave}" >> "$FAKE_EVENTS"
    echo "ACL2 Error in ( CERTIFY-BOOK ...):  assertion failed."
    exit 0 ;;
esac
if [ "$wave" = create ] || [ "$wave" = convert ]; then
  printf 'end %s %s\n' "$book" "$wave" >> "$FAKE_EVENTS"
  echo "ACL2 !>$marker"
  exit 0
fi
# A certificate shaped like ACL2's, so the cache hook has something to judge.
cat > "$book.cert" <<CERT
(IN-PACKAGE "ACL2")
"ACL2 Version 8.7"
:BEGIN-PORTCULLIS-CMDS
:END-PORTCULLIS-CMDS
:EXPANSION-ALIST
NIL
CERT
printf '(in-package "ACL2")\n' > "$book.port"
# `<certified book>:<book to edit>`: a source that changes while the run is
# still going, which is what the cache must never file a pair against.
case "${FAKE_EDIT_AFTER:-}" in
  "$book:"*) printf '; edited mid-run\n' >> "${FAKE_EDIT_AFTER#*:}.lisp" ;;
esac
printf 'end %s%s\n' "$book" "${wave:+ $wave}" >> "$FAKE_EVENTS"
echo "ACL2 !>$marker"
exit 0
"""


class FakeRepository:
    """A throwaway repository plus a fake ACL2, driving the real runner."""

    def __init__(self, directory: str, books: dict[str, list[str]]) -> None:
        self.root = Path(directory).resolve()
        (self.root / "books").mkdir()
        for book, includes in books.items():
            body = "".join(f'(include-book "{name}")\n' for name in includes)
            (self.root / f"{book}.lisp").write_text('(in-package "ACL2")\n' + body)
        runtime = self.root / "fake-sbcl.sh"
        runtime.write_text(FAKE_ACL2)
        runtime.chmod(runtime.stat().st_mode | stat.S_IXUSR)
        core = self.root / "fake-saved-acl2.core"
        core.write_bytes(b"fake ACL2 saved core\n")
        self.acl2 = self.root / "fake-acl2.sh"
        self.acl2.write_text(
            '#!/bin/sh\nexec "{}" --core "{}" "$@"\n'.format(runtime, core))
        self.acl2.chmod(self.acl2.stat().st_mode | stat.S_IXUSR)
        self.events = self.root / "events.log"
        self.cache = self.root / "cert-cache"
        # Archived manifests the scheduler reads walls from; empty unless a
        # test writes one, so no real run's timings reach a unit test.
        self.history = self.root / "planning" / "evidence" / "manifests"
        self.runs = 0

    def archive_walls(self, walls: dict[str, float]) -> None:
        self.history.mkdir(parents=True, exist_ok=True)
        (self.history / "certify-20260101T000000Z-1.json").write_text(
            json.dumps({"book_wall_seconds": walls}))

    def certify(self, books: list[str], jobs: int, fail: str = "",
                slots: int = 16, extra: list[str] | None = None,
                quiet_fail: str = "", edit_after: str = "",
                convert_fail: str = "") -> tuple[int, dict]:
        extra = extra or []
        self.runs += 1
        self.events.write_text("")
        build = self.root / "build" / f"acl2-{self.runs}"
        environment = {
            "FN_ACL2": str(self.acl2),
            "FAKE_EVENTS": str(self.events),
            "FAKE_FAIL": fail,
            "FAKE_QUIET_FAIL": quiet_fail,
            "FAKE_CONVERT_FAIL": convert_fail,
            "FAKE_EDIT_AFTER": edit_after,
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            # A private slot pool and a private certificate cache: a unit test
            # must not contend with this machine's real ACL2 runs or publish
            # fake certificates into the developer's cache.
            "FN_ACL2_SLOTS": str(slots),
            "FN_ACL2_SLOT_DIR": str(self.root / "slots"),
            "FN_CERT_CACHE": str(self.cache),
        }
        argv = ["certify_books.py", "--jobs", str(jobs), *extra, *books]
        with mock.patch.object(runner, "ROOT", self.root), \
                mock.patch.object(runner.ledger, "ROOT", self.root), \
                mock.patch.object(runner, "BUILD_ROOT", build), \
                mock.patch.object(runner, "WALL_HISTORY", self.history), \
                mock.patch.dict(os.environ, environment, clear=True), \
                mock.patch.object(runner.sys, "argv", argv), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            code = runner.main()
        run_dir = next(build.iterdir())
        return code, json.loads((run_dir / "manifest.json").read_text())

    def write_makefile(self, roots: list[str]) -> None:
        body = " \\\n  ".join(roots)
        (self.root / "Makefile").write_text(
            f"ACL2_BOOKS ?= {body}\n\ncertify:\n\techo $(ACL2_BOOKS)\n")

    def dry_run(self, books: list[str], affected: list[str],
                extra: list[str] | None = None) -> tuple[int, list[str]]:
        argv = ["certify_books.py", "--dry-run", *(extra or [])]
        for target in affected:
            argv.extend(["--affected-by", target])
        argv.extend(books)
        buffer = io.StringIO()
        with mock.patch.object(runner, "ROOT", self.root), \
                mock.patch.object(runner.ledger, "ROOT", self.root), \
                mock.patch.object(runner, "BUILD_ROOT", self.root / "build" / "dry"), \
                mock.patch.dict(os.environ, {"PATH": os.environ.get("PATH", "/bin")},
                                clear=True), \
                mock.patch.object(runner.sys, "argv", argv), \
                contextlib.redirect_stdout(buffer), \
                contextlib.redirect_stderr(io.StringIO()):
            code = runner.main()
        return code, buffer.getvalue().split()

    def cached_books(self) -> list[str]:
        if not self.cache.is_dir():
            return []
        return sorted(json.loads(meta.read_text())["book"]
                      for meta in self.cache.rglob("meta.json"))

    def event_log(self) -> list[str]:
        return self.events.read_text().split()

    def index(self, event: str, book: str, wave: str = "") -> int:
        log = self.events.read_text().splitlines()
        return log.index(f"{event} {book}" + (f" {wave}" if wave else ""))

    def waves(self) -> list[tuple[str, str, str]]:
        """Every recorded event as (start|end, book, wave)."""
        return [tuple(line.split()) for line in
                self.events.read_text().splitlines() if line]

    def peak_concurrency(self) -> int:
        live = peak = 0
        for line in self.events.read_text().splitlines():
            live += 1 if line.startswith("start ") else -1
            peak = max(peak, live)
        return peak


class ParallelScheduleTests(unittest.TestCase):
    """The schedule may reorder work; it may not weaken the evidence."""

    LAYERED = {
        "books/base": [],
        "books/mid": ["base"],
        "books/leaf-a": ["mid"],
        "books/leaf-b": ["mid"],
        "books/leaf-c": ["mid"],
        "books/free-a": [],
        "books/free-b": [],
    }
    ORDER = ["books/base", "books/mid", "books/leaf-a", "books/leaf-b",
             "books/leaf-c", "books/free-a", "books/free-b"]
    EDGES = [("books/mid", "books/base"), ("books/leaf-a", "books/mid"),
             ("books/leaf-b", "books/mid"), ("books/leaf-c", "books/mid")]

    def test_dependencies_finish_before_dependents_start_under_four_jobs(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            code, manifest = repository.certify(self.ORDER, jobs=4)
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            for child, parent in self.EDGES:
                self.assertGreater(repository.index("start", child),
                                   repository.index("end", parent),
                                   f"{child} started before {parent} was certified")
            self.assertGreater(repository.peak_concurrency(), 1,
                               "independent books did not run concurrently")
            self.assertLessEqual(repository.peak_concurrency(), 4)

    def test_dependency_through_an_unrequested_book_still_orders_the_run(self):
        # books/mid is not requested, so books/leaf-a depends on books/base
        # only through it.  The edge must survive the intermediate.
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            requested = ["books/leaf-a", "books/free-a", "books/base"]
            code, manifest = repository.certify(requested, jobs=4)
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            self.assertGreater(repository.index("start", "books/leaf-a"),
                               repository.index("end", "books/base"))
            self.assertNotIn("start books/mid", repository.events.read_text())

    def test_include_book_cycle_is_refused_before_any_acl2_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, {"books/x": ["y"], "books/y": ["x"]})
            code, manifest = repository.certify(["books/x", "books/y"], jobs=4)
            self.assertEqual(code, 2)
            self.assertEqual(manifest["status"], "failed")
            self.assertIn("cycle", manifest["failure"])
            self.assertEqual(repository.event_log(), [])

    def test_a_failing_book_fails_the_parallel_run(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            code, manifest = repository.certify(self.ORDER, jobs=4, fail="books/leaf-b")
            self.assertEqual(code, 1)
            self.assertEqual(manifest["status"], "failed")
            self.assertEqual(manifest["acl2_exit_codes"]["books/leaf-b"], 1)
            self.assertIn("ACL2 Error", manifest["failure_markers"])
            self.assertNotIn("books/leaf-b", manifest["certificate_digests_sha256"])
            self.assertNotEqual(manifest["observed_success_markers"],
                                manifest["expected_success_markers"])

    def test_a_book_that_fails_while_acl2_exits_zero_is_recorded_failed(self):
        # The shape of the 2026-09-20 farm run: `tests/acl2/tcpcl-tests` failed
        # at a golden vector in 0.2 s, and because the driver's `(quit)` exits 0
        # the manifest's only per-book result field said 0 for it.
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            code, manifest = repository.certify(self.ORDER, jobs=4,
                                                quiet_fail="books/leaf-b")
            self.assertEqual(code, 1)
            self.assertEqual(manifest["status"], "failed")
            self.assertEqual(manifest["acl2_exit_codes"]["books/leaf-b"], 0)
            self.assertEqual(manifest["book_results"]["books/leaf-b"], "failed")
            self.assertIn("books/leaf-b", manifest["failure"])
            self.assertIn("no fresh success marker in this book's log",
                          manifest["book_failures"]["books/leaf-b"])
            for book in self.ORDER:
                if book != "books/leaf-b":
                    self.assertEqual(manifest["book_results"][book], "passed", book)
                    self.assertNotIn(book, manifest["book_failures"])
            # And the cache gate agrees: the failed root contributes no pair.
            certified = runner.certs.certified_books(
                [{**manifest, "evidence": str(repository.root / "build" / "acl2" / "run")}])
            self.assertNotIn("books/leaf-b", certified)
            self.assertIn("books/leaf-a", certified)

    def test_manifest_records_jobs_start_order_and_per_book_wall_time(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            _, manifest = repository.certify(self.ORDER, jobs=4)
            self.assertEqual((manifest["jobs"], manifest["jobs_effective"]), (4, 4))
            self.assertCountEqual(manifest["start_order"], self.ORDER)
            self.assertCountEqual(manifest["book_wall_seconds"], self.ORDER)
            for book in self.ORDER:
                self.assertGreater(manifest["book_wall_seconds"][book], 0)
            self.assertGreater(manifest["certify_wall_seconds"], 0)

    def test_the_run_names_itself_and_is_filed_where_a_reader_can_open_it(self):
        """The run directory is under `build/`, which no reader ever sees.

        Every certification claim in this tree cited such a directory and
        none of them resolved (316 cited run ids at dev 5698648). The
        manifest carries the claim, so it is also written to
        `planning/evidence/manifests/<run-id>.json`, and it now says which
        run, which box and which revision it was, none of which a reader
        could recover from the file alone before.
        """
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            _, manifest = repository.certify(self.ORDER, jobs=4)
            run_id = manifest["run_id"]
            filed = (repository.root / "planning" / "evidence" / "manifests"
                     / f"{run_id}.json")
            self.assertTrue(filed.is_file(), "the manifest was not archived")
            kept = json.loads(filed.read_text())
        self.assertTrue(run_id.startswith("certify-"))
        self.assertEqual(kept["run_id"], run_id)
        self.assertEqual(kept["requested_books"], manifest["requested_books"])
        self.assertEqual(kept["certificate_digests_sha256"],
                         manifest["certificate_digests_sha256"])
        self.assertTrue(kept["hostname"])
        self.assertIn("git_revision", kept)
        self.assertTrue(kept["started_utc"] <= kept["finished_utc"])
        # The copy says where the log it does not carry was left.
        self.assertTrue(kept["archived_from"].endswith(run_id))

    def test_one_job_keeps_the_requested_order_and_the_same_manifest_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.LAYERED)
            sequential_code, sequential = repository.certify(self.ORDER, jobs=1)
            self.assertEqual((sequential_code, sequential["status"]), (0, "passed"))
            self.assertEqual(sequential["start_order"], self.ORDER)
            self.assertEqual(sequential["jobs_effective"], 1)
            self.assertEqual(repository.peak_concurrency(), 1)
            _, parallel = repository.certify(self.ORDER, jobs=4)
            self.assertEqual(sorted(sequential), sorted(parallel))
            for field in ("requested_books", "source_digests_sha256",
                          "source_digests_sha256_after", "certificate_digests_sha256",
                          "acl2_exit_codes", "local_source_audit", "status"):
                self.assertEqual(sequential[field], parallel[field], field)
            # Each run has its own nonce, so compare the book component of the
            # markers: both runs must show every book once, in requested order.
            for manifest in (sequential, parallel):
                self.assertEqual(manifest["observed_success_markers"],
                                 manifest["expected_success_markers"])
                self.assertEqual([marker.split()[-1] for marker in manifest["observed_success_markers"]],
                                 [runner.success_token(book, "n").split()[-1] for book in self.ORDER])


class ProvisionalCertificationTests(unittest.TestCase):
    """`--pcert`: the proofs stop being a chain, and one run names every red.

    A closure run stops at the first failing book, so it reports one layer of
    independent reds and nothing about the books above.  Under provisional
    certification only Create is dependency-ordered; Convert takes a
    sub-book's `.pcert0` in place of a certificate, so every book's proofs
    run in one wave and a book above the failure comes back *proved* with no
    certificate rather than unknown.  Measured on a real 63-book fn closure
    on persvati on 2026-09-22, that was four independent reds instead of one.
    """

    CHAIN = {"books/base": [], "books/mid": ["base"], "books/leaf": ["mid"]}
    ORDER = ["books/base", "books/mid", "books/leaf"]

    def run_chain(self, **extra):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        repository = FakeRepository(directory.name, self.CHAIN)
        code, manifest = repository.certify(
            self.ORDER, jobs=3, extra=["--pcert", "--no-publish"], **extra)
        return repository, code, manifest

    def test_a_convert_failure_leaves_the_books_above_it_proved(self):
        repository, code, manifest = self.run_chain(convert_fail="books/mid")
        self.assertEqual(code, 1)
        self.assertTrue(manifest["pcert"])
        self.assertEqual(manifest["pcert_reached"],
                         {"books/base": "complete", "books/mid": "create",
                          "books/leaf": "convert"})
        self.assertEqual(manifest["book_results"],
                         {"books/base": "passed", "books/mid": "failed",
                          "books/leaf": "failed"})
        self.assertEqual(sorted(manifest["pcert_wall_seconds"]),
                         ["complete", "convert", "create"])

    def test_create_respects_dependencies_and_convert_does_not(self):
        repository, _, _ = self.run_chain(convert_fail="books/mid")
        for child, parent in (("books/mid", "books/base"),
                              ("books/leaf", "books/mid")):
            self.assertGreater(repository.index("start", child, "create"),
                               repository.index("end", parent, "create"),
                               f"{child} was Created before {parent} finished")
        converts = [event for event in repository.waves() if event[2] == "convert"]
        live = peak = 0
        for kind, _, _ in converts:
            live += 1 if kind == "start" else -1
            peak = max(peak, live)
        self.assertGreater(peak, 1, "the Convert wave did not run in parallel")

    def test_the_run_keeps_one_log_and_one_verdict_per_book(self):
        repository, _, manifest = self.run_chain(convert_fail="books/mid")
        run_dir = next((repository.root / "build").glob("acl2-*/certify-*"))
        for book in self.ORDER:
            flat = book.replace("/", "--")
            self.assertTrue((run_dir / f"{flat}.certify.log").is_file())
            for wave in runner.PCERT_ORDER:
                self.assertTrue(
                    (run_dir / f"{flat}.pcert-{wave}.certify.log").is_file()
                    or wave != "create")
        combined = (run_dir / "books--leaf.certify.log").read_text()
        self.assertIn("FN_PCERT_WAVE CONVERT books/leaf", combined)
        # The cascade sentence ACL2 wraps, as the Complete wave prints it.
        self.assertIn("There is\nno certificate on file", combined)
        self.assertEqual(len(runner.success_markers(
            combined, manifest["expected_success_markers"][0].split()[1])), 0)

    def test_a_clean_chain_certifies_and_the_token_still_means_certified(self):
        repository, code, manifest = self.run_chain()
        self.assertEqual((code, manifest["status"]), (0, "passed"))
        self.assertEqual(set(manifest["pcert_reached"].values()), {"complete"})
        self.assertEqual(manifest["observed_success_markers"],
                         manifest["expected_success_markers"])
        for book in self.ORDER:
            self.assertTrue((repository.root / f"{book}.cert").is_file())


class AffectedByTests(unittest.TestCase):
    """Certify what a change can have invalidated, and nothing else."""

    def test_dry_run_lists_the_affected_roots_in_requested_order(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            code, listed = repository.dry_run(ParallelScheduleTests.ORDER,
                                              ["books/mid.lisp"])
            self.assertEqual(code, 0)
            self.assertEqual(listed, ["books/mid", "books/leaf-a",
                                      "books/leaf-b", "books/leaf-c"])
            self.assertEqual(repository.dry_run(ParallelScheduleTests.ORDER,
                                                ["books/free-a"])[1],
                             ["books/free-a"])
            # Two targets select the union, still in requested order.
            self.assertEqual(repository.dry_run(ParallelScheduleTests.ORDER,
                                                ["books/free-b", "books/leaf-a"])[1],
                             ["books/leaf-a", "books/free-b"])

    def test_a_deep_change_selects_every_root_above_it(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            self.assertEqual(repository.dry_run(ParallelScheduleTests.ORDER,
                                                ["books/base"])[1],
                             ["books/base", "books/mid", "books/leaf-a",
                              "books/leaf-b", "books/leaf-c"])

    def test_only_the_affected_books_are_certified(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            code, manifest = repository.certify(
                ParallelScheduleTests.ORDER, jobs=4,
                extra=["--affected-by", "books/leaf-a.lisp"])
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            self.assertEqual(manifest["requested_books"], ["books/leaf-a"])
            self.assertEqual(manifest["affected_by"], ["books/leaf-a.lisp"])
            self.assertEqual(manifest["requested_before_filter"],
                             ParallelScheduleTests.ORDER)
            self.assertEqual(repository.event_log(),
                             ["start", "books/leaf-a", "end", "books/leaf-a"])

    def test_an_unknown_affected_book_is_refused_rather_than_selecting_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            with self.assertRaises(SystemExit) as refused:
                repository.dry_run(ParallelScheduleTests.ORDER, ["books/typo"])
            self.assertEqual(refused.exception.code, 2)


class MakefileRootsTests(unittest.TestCase):
    """One list of roots, and the Makefile owns it."""

    def test_the_default_roots_are_the_makefile_roots(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            repository.write_makefile(ParallelScheduleTests.ORDER)
            with mock.patch.object(runner.ledger, "ROOT", repository.root):
                self.assertEqual(runner.default_books(),
                                 ParallelScheduleTests.ORDER)

    def test_affected_by_with_no_roots_named_searches_every_makefile_root(self):
        # The defect this closes: the runner carried its own list of roots,
        # which held 71 of the Makefile's 216, so `--affected-by` over the
        # default set silently answered a question about a third of the tree.
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            repository.write_makefile(ParallelScheduleTests.ORDER)
            code, listed = repository.dry_run([], ["books/base"])
            self.assertEqual(code, 0)
            self.assertEqual(listed, ["books/base", "books/mid", "books/leaf-a",
                                      "books/leaf-b", "books/leaf-c"])
            stale = ["books/base", "books/mid", "books/leaf-a"]
            self.assertEqual(repository.dry_run(stale, ["books/base"])[1], stale,
                             "a named subset still bounds the search")


class ClosureTests(unittest.TestCase):
    """`--closure`: a run that assumes the box holds no certificate at all."""

    def test_closure_adds_the_dependencies_in_dependency_order(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            code, listed = repository.dry_run(["books/leaf-c", "books/leaf-a"],
                                              [], extra=["--closure"])
            self.assertEqual(code, 0)
            self.assertEqual(listed, ["books/base", "books/mid", "books/leaf-c",
                                      "books/leaf-a"])

    def test_closure_certifies_the_dependencies_and_the_manifest_says_so(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            repository.write_makefile(ParallelScheduleTests.ORDER)
            code, manifest = repository.certify(
                [], jobs=4,
                extra=["--closure", "--affected-by", "books/leaf-a.lisp"])
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            # requested_books is the list actually certified, dependencies
            # first; leaf-a is the only affected root and it needs two.
            self.assertEqual(manifest["requested_books"],
                             ["books/base", "books/mid", "books/leaf-a"])
            self.assertTrue(manifest["closure"])
            self.assertEqual(manifest["requested_before_filter"],
                             ParallelScheduleTests.ORDER)
            self.assertEqual(sorted(set(repository.event_log())),
                             ["books/base", "books/leaf-a", "books/mid",
                              "end", "start"])


class CriticalPathScheduleTests(unittest.TestCase):
    """Ready books start longest-remaining-chain first, by archived walls.

    The DAG is three small independent books listed first and a chain of
    three large ones listed last, the shape of the seam run on 2026-09-23:
    requested order spends the first slots on the small books while the
    chain that bounds the run waits.
    """

    BOOKS = {
        "books/free-a": [], "books/free-b": [], "books/free-c": [],
        "books/chain-1": [], "books/chain-2": ["chain-1"],
        "books/chain-3": ["chain-2"],
    }
    ORDER = ["books/free-a", "books/free-b", "books/free-c",
             "books/chain-1", "books/chain-2", "books/chain-3"]
    WALLS = {"books/free-a": 1.0, "books/free-b": 1.0, "books/free-c": 1.0,
             "books/chain-1": 10.0, "books/chain-2": 10.0, "books/chain-3": 10.0}
    GRAPH = {"books/free-a": set(), "books/free-b": set(), "books/free-c": set(),
             "books/chain-1": set(), "books/chain-2": {"books/chain-1"},
             "books/chain-3": {"books/chain-2"}}

    def test_priority_is_own_wall_plus_the_longest_chain_above(self):
        priority = runner.critical_path_priority(self.ORDER, self.GRAPH, self.WALLS)
        self.assertEqual(priority["books/chain-1"], 30.0)
        self.assertEqual(priority["books/chain-2"], 20.0)
        self.assertEqual(priority["books/chain-3"], 10.0)
        self.assertEqual(priority["books/free-a"], 1.0)

    def test_the_chain_starts_first_and_dependencies_still_hold(self):
        started: list[str] = []
        priority = runner.critical_path_priority(self.ORDER, self.GRAPH, self.WALLS)
        runner.run_schedule(self.ORDER, self.GRAPH, 1, started.append, priority)
        self.assertEqual(started, ["books/chain-1", "books/chain-2",
                                   "books/chain-3", "books/free-a",
                                   "books/free-b", "books/free-c"])
        started.clear()
        runner.run_schedule(self.ORDER, self.GRAPH, 1, started.append)
        self.assertEqual(started, self.ORDER, "no priority keeps requested order")

    def test_the_runner_orders_by_archived_walls_and_says_so(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.BOOKS)
            repository.archive_walls(self.WALLS)
            code, manifest = repository.certify(self.ORDER, jobs=2)
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            # chain-1 takes a first slot (requested order would start it
            # third); chain-2 is not ready yet, so the other slot goes to the
            # first small book.  The two start concurrently, so their
            # recorded order is a race and only the pair is checked.
            self.assertCountEqual(manifest["start_order"][:2],
                                  ["books/chain-1", "books/free-a"])
            self.assertGreater(repository.index("start", "books/chain-2"),
                               repository.index("end", "books/chain-1"))
            self.assertEqual(manifest["schedule"],
                             {"policy": "critical-path-first",
                              "books_with_archived_wall": 6,
                              "predicted_critical_path_seconds": 30.0})

    def test_one_job_keeps_requested_order_whatever_the_walls(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, self.BOOKS)
            repository.archive_walls(self.WALLS)
            _, manifest = repository.certify(self.ORDER, jobs=1)
            self.assertEqual(manifest["start_order"], self.ORDER)
            self.assertEqual(manifest["schedule"], {"policy": "requested-order"})

    def test_a_list_schedule_of_the_seam_shape_is_shorter(self):
        # run_schedule's policy on a virtual clock at two jobs: whenever a
        # slot is free, start the first ready book in queue order.  Requested
        # order finishes at 31 s (the chain starts at 1 s, behind two small
        # books); the chain first finishes at 30 s, its own length, which no
        # order can beat.
        def makespan(priority):
            queue = list(self.ORDER)
            if priority is not None:
                queue.sort(key=lambda book: -priority[book])
            running: dict[str, float] = {}
            done: set[str] = set()
            clock = 0.0
            while queue or running:
                for book in list(queue):
                    if len(running) < 2 and self.GRAPH[book] <= done:
                        queue.remove(book)
                        running[book] = clock + self.WALLS[book]
                clock = min(running.values())
                for book in [b for b, end in running.items() if end == clock]:
                    del running[book]
                    done.add(book)
            return clock
        priority = runner.critical_path_priority(self.ORDER, self.GRAPH, self.WALLS)
        self.assertEqual(makespan(None), 31.0)
        self.assertEqual(makespan(priority), 30.0)


class SlotTests(unittest.TestCase):
    """The machine-wide ACL2 cap, with a fake ACL2 that sleeps."""

    def test_one_slot_serializes_four_jobs_and_the_waits_are_recorded(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            code, manifest = repository.certify(ParallelScheduleTests.ORDER,
                                                jobs=4, slots=1)
            self.assertEqual((code, manifest["status"]), (0, "passed"))
            self.assertEqual(repository.peak_concurrency(), 1)
            self.assertEqual(manifest["acl2_slots"], 1)
            self.assertCountEqual(list(manifest["slot_wait_seconds"]),
                                  ["version-probe"] + ParallelScheduleTests.ORDER)
            self.assertGreater(max(manifest["slot_wait_seconds"].values()), 0,
                               "no book ever waited for the single slot")

    def test_slots_above_the_job_count_do_not_constrain_the_schedule(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER,
                                             jobs=4, slots=16)
            self.assertGreater(repository.peak_concurrency(), 1)
            self.assertEqual(manifest["acl2_slots"], 16)


class CachePublishTests(unittest.TestCase):
    """The cache follows each BOOK's verdict, never the whole run's."""

    def test_a_passing_run_publishes_every_certificate_to_the_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2)
            cache = manifest["cert_cache"]
            # Each book is published as it finishes, so by the time the
            # end-of-run sweep looks, every pair is already filed.
            self.assertEqual(cache["per_book_published"],
                             len(ParallelScheduleTests.ORDER))
            self.assertEqual(cache["published"] + cache["already_cached"],
                             len(ParallelScheduleTests.ORDER))
            self.assertEqual(cache["not_published"], [])
            self.assertEqual(repository.cached_books(),
                             sorted(ParallelScheduleTests.ORDER))

    def test_immediate_publish_carries_toolchain_identity_before_final_sweep(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, {"books/base": []})
            cert = repository.root / "books/base.cert"
            cert.write_text('(IN-PACKAGE "ACL2")\n:BEGIN-PORTCULLIS-CMDS\n'
                            ':END-PORTCULLIS-CMDS\n')
            nonce = "1" * 32
            output = "ACL2 !>" + runner.success_token("books/base", nonce) + "\n"
            source_digests = {
                "books/base.lisp": runner.digest(repository.root / "books/base.lisp")}
            toolchain = {
                "acl2_version": "ACL2 Version 8.7",
                "acl2_executable_sha256": "a" * 64,
                "acl2_compatibility": TEST_COMPATIBILITY,
                "acl2_toolchain_identity": runner.certs.stable_identity(
                    TEST_COMPATIBILITY),
                "acl2_toolchain": {"status": "qualified", "fixture": True},
                "environment": {"ACL2_BOOK_HASH_ALISTP": "NIL"},
                "runner_sha256": "b" * 64,
                "reader_sha256": "c" * 64,
            }
            with mock.patch.object(runner, "ROOT", repository.root), \
                    mock.patch.object(runner.ledger, "ROOT", repository.root), \
                    mock.patch.dict(os.environ,
                                    {"FN_CERT_CACHE": str(repository.cache)}):
                event = runner.publish_pair(
                    "books/base", "passed", repository.root / "run", nonce,
                    source_digests, output, 0, toolchain)
            self.assertTrue(event["published"])
            meta = json.loads(next(repository.cache.rglob("meta.json")).read_text())
            self.assertEqual(meta["toolchain"], TEST_COMPATIBILITY)
            self.assertEqual(meta["certification_provenance"]["runner_sha256"],
                             "b" * 64)

    def test_no_publish_leaves_the_cache_untouched(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2,
                                             extra=["--no-publish"])
            self.assertEqual(manifest["status"], "passed")
            self.assertNotIn("cert_cache", manifest)
            self.assertEqual(repository.cached_books(), [])

    def test_a_failing_run_publishes_the_books_that_passed(self):
        """The defect this replaces: a failed run cached nothing at all.

        Measured on persvati 2026-09-20, `run-20260920T203028Z-d411`
        certified 21 of 22 books, exited 1, and left 0 entries in the box
        cache; the next submit into the same root reported
        `installed 0, kept 0, uncached 267`.  A wide run on this tree exits
        non-zero whenever any root carries an open theorem, so under the old
        rule no lane ever seeded the box.
        """
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2,
                                             fail="books/leaf-b")
            self.assertEqual(manifest["status"], "failed")
            passed = sorted(book for book, verdict
                            in manifest["book_results"].items()
                            if verdict == "passed")
            self.assertIn("books/base", passed)
            self.assertNotIn("books/leaf-b", passed)
            self.assertEqual(repository.cached_books(), passed)
            events = {event["book"]: event
                      for event in manifest["cert_cache"]["per_book"]}
            self.assertTrue(events["books/base"]["published"])
            self.assertFalse(events["books/leaf-b"]["published"])
            self.assertEqual(events["books/leaf-b"]["why"],
                             "this book did not pass")

    def test_a_book_whose_closure_changed_mid_run_is_not_published(self):
        """A pair is filed under its closure; an edited closure is a poison key."""
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(
                ["books/base", "books/mid"], jobs=1,
                edit_after="books/base:books/base")
            events = {event["book"]: event
                      for event in manifest["cert_cache"]["per_book"]}
            self.assertFalse(events["books/mid"]["published"])
            self.assertIn("closure changed since certification",
                          events["books/mid"]["why"])
            self.assertNotIn("books/mid", repository.cached_books())


class CertificationEvidenceTests(unittest.TestCase):
    def test_markers_reject_echo_spoof_and_previous_run(self):
        marker = runner.success_token("books/example", "current")
        output = '\n'.join([
            f'(cw "{marker}~%")',
            runner.success_token("books/example", "previous"),
            f'arbitrary prefix {marker}',
            f'ACL2 !>>{marker} extra',
            f'ACL2 !>>{marker}',
        ])
        self.assertEqual(runner.success_markers(output, "current"),
                         [marker])

    def test_source_audit_distinguishes_comments_and_escaped_symbols(self):
        source = '''; (skip-proofs ...)
        #| (defaxiom x) #| nested |# (defttag x) |#
        (defconst *help* "skip-proofs \\" defaxiom")
        (ACL2::|SKIP-PROOFS| (defthm unsound nil))
        (defaxiom unsound2 nil)
        '''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "source.lisp").write_text(source)
            with mock.patch.object(runner, "ROOT", root):
                self.assertEqual(runner.audit_sources({"source.lisp": "unused"}),
                                 {"source.lisp": ["defaxiom", "skip-proofs"]})

    def test_dependency_closure_excludes_unrelated_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "books").mkdir()
            (root / "books/root.lisp").write_text('(include-book "dep")\n')
            (root / "books/dep.lisp").write_text('(in-package "ACL2")\n')
            with mock.patch.object(runner, "ROOT", root):
                before = runner.collect_book_sources(["books/root"])
                (root / "books/unrelated.lisp").write_text('(defun work () nil)')
                self.assertEqual(before, runner.collect_book_sources(["books/root"]))
                (root / "books/dep.lisp").write_text('(in-package "ACL2")\n; changed')
                self.assertNotEqual(before, runner.collect_book_sources(["books/root"]))

    def test_system_book_reference_is_not_resolved_as_local(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.lisp"
            source.write_text('(include-book "ihs/quotient-remainder-lemmas" :dir :system)')
            self.assertEqual(runner.local_include_books("source", source), [])


if __name__ == "__main__":
    unittest.main()
