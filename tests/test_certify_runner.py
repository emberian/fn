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
marker=$(printf '%s\n' "$driver" | grep -o 'FN_CERTIFY_SUCCESS [0-9a-f]* [0-9a-f]*' | head -1)
printf 'start %s\n' "$book" >> "$FAKE_EVENTS"
sleep "${FAKE_DELAY:-0.2}"
case " ${FAKE_FAIL:-} " in
  *" $book "*)
    printf 'end %s\n' "$book" >> "$FAKE_EVENTS"
    echo "ACL2 Error in ( CERTIFY-BOOK ...):  the fake harness refused this book."
    exit 1 ;;
esac
# Real ACL2's shape when certify-book fails: the inner ld returns, the marker
# form is never reached, no certificate is written -- and the driver's (quit)
# still exits 0.
case " ${FAKE_QUIET_FAIL:-} " in
  *" $book "*)
    printf 'end %s\n' "$book" >> "$FAKE_EVENTS"
    echo "ACL2 Error in ( CERTIFY-BOOK ...):  assertion failed."
    exit 0 ;;
esac
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
printf 'end %s\n' "$book" >> "$FAKE_EVENTS"
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
        self.acl2 = self.root / "fake-acl2.sh"
        self.acl2.write_text(FAKE_ACL2)
        self.acl2.chmod(self.acl2.stat().st_mode | stat.S_IXUSR)
        self.events = self.root / "events.log"
        self.cache = self.root / "cert-cache"
        self.runs = 0

    def certify(self, books: list[str], jobs: int, fail: str = "",
                slots: int = 16, extra: list[str] | None = None,
                quiet_fail: str = "") -> tuple[int, dict]:
        extra = extra or []
        self.runs += 1
        self.events.write_text("")
        build = self.root / "build" / f"acl2-{self.runs}"
        environment = {
            "FN_ACL2": str(self.acl2),
            "FAKE_EVENTS": str(self.events),
            "FAKE_FAIL": fail,
            "FAKE_QUIET_FAIL": quiet_fail,
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

    def index(self, event: str, book: str) -> int:
        log = self.events.read_text().splitlines()
        return log.index(f"{event} {book}")

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
    """A successful root publishes its pair; a failed one publishes nothing."""

    def test_a_passing_run_publishes_every_certificate_to_the_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2)
            self.assertEqual(manifest["cert_cache"]["published"],
                             len(ParallelScheduleTests.ORDER))
            self.assertEqual(manifest["cert_cache"]["not_published"], [])
            self.assertEqual(repository.cached_books(),
                             sorted(ParallelScheduleTests.ORDER))

    def test_no_publish_leaves_the_cache_untouched(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2,
                                             extra=["--no-publish"])
            self.assertEqual(manifest["status"], "passed")
            self.assertNotIn("cert_cache", manifest)
            self.assertEqual(repository.cached_books(), [])

    def test_a_failing_run_publishes_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = FakeRepository(directory, ParallelScheduleTests.LAYERED)
            _, manifest = repository.certify(ParallelScheduleTests.ORDER, jobs=2,
                                             fail="books/leaf-b")
            self.assertEqual(manifest["status"], "failed")
            self.assertEqual(repository.cached_books(), [])


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
