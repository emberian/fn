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
: > "$book.cert"
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
        self.runs = 0

    def certify(self, books: list[str], jobs: int, fail: str = "") -> tuple[int, dict]:
        self.runs += 1
        self.events.write_text("")
        build = self.root / "build" / f"acl2-{self.runs}"
        environment = {
            "FN_ACL2": str(self.acl2),
            "FAKE_EVENTS": str(self.events),
            "FAKE_FAIL": fail,
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        }
        argv = ["certify_books.py", "--jobs", str(jobs), *books]
        with mock.patch.object(runner, "ROOT", self.root), \
                mock.patch.object(runner, "BUILD_ROOT", build), \
                mock.patch.dict(os.environ, environment, clear=True), \
                mock.patch.object(runner.sys, "argv", argv), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            code = runner.main()
        run_dir = next(build.iterdir())
        return code, json.loads((run_dir / "manifest.json").read_text())

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
