#!/usr/bin/env python3
"""Certify fn's local ACL2 books and retain machine-readable run evidence.

This runner deliberately requires a real ACL2 executable.  In particular, an
ACL2 process exiting zero is insufficient evidence: each requested book must
emit the success marker from the successful branch of `certify-book`, and the
log must not contain an ACL2 certification/error marker.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import secrets
import shutil
import subprocess
import sys
import threading
import time
from typing import Any

# The runner and `tools/ledger.py` read books with one s-expression reader, so
# the dependency graph that schedules certification and the generated ledger
# cannot disagree about what a book includes.  `tools/` is not a package.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import acl2_slots  # noqa: E402
import certs  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parent.parent
READER = Path(ledger.__file__).resolve()
BUILD_ROOT = ROOT / "build" / "acl2"
SUCCESS_PREFIX = "FN_CERTIFY_SUCCESS "
FAILURE_MARKERS = (
    "CERTIFICATION FAILED",
    "ACL2 Error",
    "HARD ACL2 ERROR",
)
BOOK_NAME = re.compile(r"(?:books|tests/acl2)/(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+$")
FORBIDDEN_FACILITIES = {"skip-proofs", "defaxiom", "defttag", "set-raw-mode", "include-raw"}


def default_books() -> list[str]:
    """The roots `make certify` builds, read from the Makefile.

    There is one list of roots and the Makefile owns it.  A second copy here
    went stale: on 2026-09-20 it held 71 of the Makefile's 216 roots, so a
    `--affected-by` run silently searched a third of the tree.
    """
    return ledger.makefile_roots()


def source_symbols(source: str) -> list[str]:
    """Conservative lexical audit, not an ACL2 parser or macro-expansion proof.

    Ignore comments and strings, including nested block comments and escaped
    string characters. Retain escaped symbol spellings so vertical bars cannot
    trivially hide a forbidden facility. Local source review remains necessary;
    ACL2, its installed system books, and the executable are trusted inputs.
    """
    tokens: list[str] = []
    current: list[str] = []
    i = 0
    block = 0
    string = False
    quoted_symbol = False
    while i < len(source):
        c = source[i]
        pair = source[i:i + 2]
        if block:
            if pair == "#|":
                block += 1
                i += 2
            elif pair == "|#":
                block -= 1
                i += 2
            else:
                i += 1
            continue
        if string:
            if c == "\\":
                i += 2
            else:
                string = c != '"'
                i += 1
            continue
        if c == "\\":
            if i + 1 < len(source):
                current.append(source[i + 1])
            i += 2
            continue
        if c == "|":
            quoted_symbol = not quoted_symbol
            i += 1
            continue
        if quoted_symbol:
            current.append(c)
            i += 1
            continue
        if pair == "#|" or c == ";" or c == '"' or c.isspace() or c in "()'`,":
            if current:
                tokens.append("".join(current).lower())
                current = []
            if pair == "#|":
                block = 1
                i += 2
            elif c == ";":
                newline = source.find("\n", i)
                i = len(source) if newline < 0 else newline + 1
            else:
                string = c == '"'
                i += 1
        else:
            current.append(c)
            i += 1
    if current:
        tokens.append("".join(current).lower())
    return tokens


def audit_sources(sources: dict[str, str]) -> dict[str, list[str]]:
    findings: dict[str, list[str]] = {}
    for relative in sources:
        symbols = source_symbols((ROOT / relative).read_text(encoding="utf-8"))
        found = sorted({symbol.rsplit(":", 1)[-1] for symbol in symbols} & FORBIDDEN_FACILITIES)
        if found:
            findings[relative] = found
    return findings


def success_token(book: str, nonce: str) -> str:
    # Fixed width stays below ACL2's pretty-printer margin even for long paths.
    # Full requested paths and source digests remain in the manifest.
    return SUCCESS_PREFIX + nonce + " " + hashlib.sha256(book.encode()).hexdigest()[:12]


def success_markers(output: str, nonce: str) -> list[str]:
    # Only a whole marker line, optionally following the actual ACL2 prompt,
    # counts. Text echoed from a form, old logs, and unrelated runs cannot pass.
    pattern = re.compile(
        r"^(?:ACL2 [^\s]*>)?" + re.escape(SUCCESS_PREFIX + nonce + " ")
        + r"([a-f0-9]{12})$"
    )
    return [SUCCESS_PREFIX + nonce + " " + match.group(1)
            for line in output.splitlines() if (match := pattern.fullmatch(line))]


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def resolve_executable(value: str) -> Path | None:
    candidate = Path(value).expanduser()
    if os.sep in value:
        return candidate.resolve() if candidate.is_file() else None
    found = shutil.which(value)
    return Path(found).resolve() if found else None


def book_source(book: str) -> Path:
    source = (ROOT / f"{book}.lisp").resolve()
    if not source.is_relative_to(ROOT) or not source.is_file():
        raise ValueError(f"missing requested source book: {book}.lisp")
    return source


def local_include_books(book: str, source: Path) -> list[str]:
    """Repository-relative books this book includes, in source order.

    `ledger.analyze_book` separates a bare `(include-book "x")`, which is local
    and must be pinned, from an `:dir`-qualified one, which selects an ACL2
    system/project book outside the local source closure.  Nothing is interned,
    evaluated, or macro-expanded, so reading a book cannot run a book.
    """
    analysis = ledger.analyze_book(source, f"{book}.lisp")
    if analysis.read_error:
        raise ValueError(f"unreadable book source: {book}.lisp: {analysis.read_error}")
    dependencies: list[str] = []
    for reference in analysis.includes:
        dependency_source = (source.parent / reference).with_suffix(".lisp").resolve()
        if not dependency_source.is_relative_to(ROOT):
            raise ValueError(f"local include-book escapes the repository: {reference} in {book}.lisp")
        if not dependency_source.is_file():
            raise ValueError(f"missing local include-book: {reference} in {book}.lisp")
        dependencies.append(dependency_source.relative_to(ROOT).with_suffix("").as_posix())
    return dependencies


def local_closure(roots: list[str]) -> dict[str, list[str]]:
    """Every book reachable from `roots` through local include-book, with edges.

    Raises on a source that is missing, unreadable, or that includes a local
    book which does not resolve inside the repository.
    """
    pending = list(roots)
    closure: dict[str, list[str]] = {}
    while pending:
        book = pending.pop()
        if book in closure:
            continue
        closure[book] = local_include_books(book, book_source(book))
        pending.extend(closure[book])
    return closure


def collect_book_sources(roots: list[str]) -> dict[str, str]:
    closure = local_closure(roots)
    return {f"{book}.lisp": digest(book_source(book)) for book in sorted(closure)}


def cycle_through(closure: dict[str, list[str]]) -> list[str] | None:
    """A local include-book cycle as a path, or None.  ACL2 cannot certify one."""
    state: dict[str, int] = {}
    for start in sorted(closure):
        if state.get(start):
            continue
        # Iterative depth-first search: 1 marks a book on the current path.
        stack: list[tuple[str, list[str]]] = [(start, list(closure[start]))]
        state[start] = 1
        path = [start]
        while stack:
            book, rest = stack[-1]
            if not rest:
                state[book] = 2
                stack.pop()
                path.pop()
                continue
            dependency = rest.pop()
            if state.get(dependency) == 1:
                return path[path.index(dependency):] + [dependency]
            if state.get(dependency) == 2:
                continue
            state[dependency] = 1
            path.append(dependency)
            stack.append((dependency, list(closure[dependency])))
    return None


def dependency_graph(books: list[str]) -> dict[str, set[str]]:
    """For each requested book, the requested books that must certify first.

    An include-book of an unrequested book is not an edge: that book is not
    being written during this run, so its certificate is already whatever it
    is.  Its own local includes are still followed, so a requested book reached
    only through unrequested intermediates is still an edge.  Reaching a
    requested book ends that search: whatever is below it is ordered before it.
    """
    closure = local_closure(books)
    cycle = cycle_through(closure)
    if cycle is not None:
        raise ValueError("local include-book cycle: " + " -> ".join(cycle))
    requested = set(books)
    graph: dict[str, set[str]] = {}
    for book in books:
        predecessors: set[str] = set()
        seen: set[str] = set()
        stack = list(closure[book])
        while stack:
            dependency = stack.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            if dependency in requested:
                predecessors.add(dependency)
            else:
                stack.extend(closure[dependency])
        predecessors.discard(book)
        graph[book] = predecessors
    return graph


def normalize_book(value: str) -> str:
    """A `--affected-by` argument as a repository-relative book name."""
    path = Path(value)
    if path.is_absolute():
        resolved = path.resolve()
        if not resolved.is_relative_to(ROOT):
            raise ValueError(f"path is outside the repository: {value}")
        path = resolved.relative_to(ROOT)
    text = path.as_posix()
    name = text[:-len(".lisp")] if text.endswith(".lisp") else text
    book_source(name)  # a typo must not silently select nothing
    return name


def affected_roots(books: list[str], targets: list[str]) -> list[str]:
    """The requested books that are, or transitively include, a named book.

    Order is the requested order, which is the Makefile order under `make
    certify`, so a filtered run certifies in the same sequence as a full one.
    This searches the roots it is given and nothing else, so the candidate set
    matters: with no roots named, that is every Makefile root, because
    `--affected-by` over a subset answers a smaller question than it looks
    like it is answering.  A book's own dependencies are not selected here; a
    book whose content did not change has a valid content-hashed certificate
    already, and `--closure` is for the run that cannot assume one.
    """
    names = {normalize_book(target) for target in targets}
    closure = local_closure(books)
    selected: list[str] = []
    for book in books:
        reached = {book}
        stack = list(closure[book])
        while stack:
            dependency = stack.pop()
            if dependency in reached:
                continue
            reached.add(dependency)
            stack.extend(closure[dependency])
        if reached & names:
            selected.append(book)
    return selected


def with_dependencies(books: list[str]) -> list[str]:
    """`books` and everything they locally include, dependencies first.

    A farm box need not hold a certificate for anything: its cache can be
    empty, or hold pairs made in a worktree whose absolute paths make them
    unusable here.  Certifying the whole local closure in this order is what
    makes such a run self-contained, at the cost of the books a valid
    certificate would have covered.
    """
    closure = local_closure(books)
    cycle = cycle_through(closure)
    if cycle is not None:
        raise ValueError("local include-book cycle: " + " -> ".join(cycle))
    ordered: list[str] = []
    placed: set[str] = set()
    for root in books:
        stack: list[tuple[str, list[str]]] = [(root, list(closure[root]))]
        while stack:
            book, rest = stack[-1]
            if book in placed:
                stack.pop()
                continue
            if rest:
                dependency = rest.pop()
                if dependency not in placed:
                    stack.append((dependency, list(closure[dependency])))
                continue
            placed.add(book)
            ordered.append(book)
            stack.pop()
    return ordered


def make_driver(book: str, nonce: str) -> str:
    # `certify-book` must run at the top level of an ACL2 ld.  On an error,
    # the inner ld returns before it reaches the marker; this catches ACL2
    # failures even when the surrounding process eventually exits zero.
    return f'''(ld '((certify-book "{book}" 0 t)
      (value-triple (cw "~%{success_token(book, nonce)}~%")))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def acl2_version_driver() -> str:
    return '''(ld '((value-triple (cw "FN_ACL2_VERSION ~s0~%" (@ acl2-version))))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''


def run_acl2(
    executable: Path, driver: str, timeout_seconds: int
) -> subprocess.CompletedProcess[bytes]:
    environment = os.environ.copy()
    # A user customization can alter the ACL2 world before certification.  Do
    # not allow such ambient state into project evidence.
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"  # content-hashed certificates: relocatable across worktrees and hosts
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    return subprocess.run(
        [str(executable)],
        cwd=ROOT,
        input=driver.encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env=environment,
        check=False,
        timeout=timeout_seconds,
    )


def run_schedule(
    books: list[str],
    graph: dict[str, set[str]],
    jobs: int,
    certify: Any,
) -> None:
    """Certify `books`, starting one only once every requested dependency's
    ACL2 process has exited.  At most `jobs` ACL2 processes exist at a time.

    Why independent books do not race: each invocation writes only artifacts
    named for the book it certifies -- `<book>.cert`, `<book>.port`, the
    compiled file, and `<book>@expansion.lsp` -- and the requested list is
    rejected if it repeats a book, so no two processes write the same path.
    Two books that both include the same certified dependency only *read* that
    dependency's certificate and compiled file; the scheduler already waited
    for the process that wrote them to exit, so nothing is writing those files
    while they are read, and concurrent readers do not race.

    A dependency that failed still releases its dependents, because the
    sequential runner also ran every requested book regardless of an earlier
    failure and keeping that preserves its diagnostics.  The dependents then
    fail too: the pass rule is one fresh marker and one certificate for every
    requested book, so no failure here can be reported as a pass.

    Ready books start in requested order, which is a topological order for the
    project roots, so `--jobs 1` starts books in exactly the requested order.
    """
    waiting = {book: set(graph[book]) for book in books}
    queue = list(books)
    futures: dict[concurrent.futures.Future, str] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while queue or futures:
            while queue and len(futures) < jobs:
                ready = next((book for book in queue if not waiting[book]), None)
                if ready is None:
                    break
                queue.remove(ready)
                futures[pool.submit(certify, ready)] = ready
            if not futures:
                # Unreachable once `dependency_graph` has refused cycles.  Fail
                # loudly rather than quietly certifying a truncated batch.
                raise ValueError(
                    "certification schedule stalled with books unstarted: " + ", ".join(queue)
                )
            done, _ = concurrent.futures.wait(
                list(futures), return_when=concurrent.futures.FIRST_COMPLETED
            )
            for future in done:
                finished = futures.pop(future)
                future.result()
                for pending in waiting.values():
                    pending.discard(finished)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def timeout_output(error: subprocess.TimeoutExpired) -> bytes:
    output = error.stdout or b""
    return output if isinstance(output, bytes) else output.encode("utf-8", errors="replace")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "books",
        nargs="*",
        help=(
            "repository-relative ACL2 book names without .lisp "
            "(default: every root the Makefile's ACL2_BOOKS names)"
        ),
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=int(os.environ.get("FN_ACL2_TIMEOUT_SECONDS", "600")),
        help="per-ACL2-invocation timeout in seconds (default: 600, or FN_ACL2_TIMEOUT_SECONDS)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=int(os.environ.get("FN_CERTIFY_JOBS", "1")),
        help=(
            "maximum concurrent ACL2 processes (default: 1, or FN_CERTIFY_JOBS). "
            "Books still certify in local include-book dependency order"
        ),
    )
    parser.add_argument(
        "--affected-by",
        action="append",
        default=[],
        metavar="BOOK",
        help=(
            "certify only the requested books that are, or transitively "
            "include, this book (repeatable; .lisp optional)"
        ),
    )
    parser.add_argument(
        "--closure",
        action="store_true",
        help=(
            "also certify everything the selected roots locally include, in "
            "dependency order, so the run needs no certificate to exist first"
        ),
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print the books this invocation would certify and exit",
    )
    parser.add_argument(
        "--no-publish",
        action="store_true",
        help="do not publish the resulting certificates to the local cache",
    )
    args = parser.parse_args()
    if not args.books:
        try:
            args.books = default_books()
        except (OSError, ValueError) as error:
            parser.error(f"cannot read the Makefile's ACL2_BOOKS: {error}")

    invalid = [book for book in args.books if not BOOK_NAME.fullmatch(book)]
    if invalid:
        parser.error(
            "book names must be repository-relative paths below books/ or tests/acl2/ "
            "without .lisp: " + ", ".join(invalid)
        )
    repeated = sorted({book for book in args.books if args.books.count(book) > 1})
    if repeated:
        # Two ACL2 processes certifying one book would write the same .cert.
        parser.error("each book may be requested once: " + ", ".join(repeated))
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if args.jobs <= 0:
        parser.error("--jobs must be positive")
    requested_before_filter = list(args.books)
    if args.affected_by:
        try:
            args.books = affected_roots(args.books, args.affected_by)
        except ValueError as error:
            parser.error(str(error))
    if args.closure and args.books:
        try:
            args.books = with_dependencies(args.books)
        except ValueError as error:
            parser.error(str(error))
    if args.dry_run:
        for book in args.books:
            print(book)
        return 0
    if not args.books:
        print("No requested book is affected by: " + ", ".join(args.affected_by))
        return 0
    effective_jobs = max(1, min(args.jobs, len(args.books)))

    configured = os.environ.get("FN_ACL2", "acl2")
    acl2 = resolve_executable(configured)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = BUILD_ROOT / f"certify-{stamp}-{os.getpid()}"
    run_dir.mkdir(parents=True, exist_ok=False)

    manifest: dict[str, Any] = {
        "command": [configured],
        "environment": {"ACL2_CUSTOMIZATION": "NONE", "ACL2_BOOK_HASH_ALISTP": "NIL", "ACL2_SYSTEM_BOOKS": None},
        "platform": platform.platform(),
        "python": platform.python_version(),
        "requested_books": args.books,
        "affected_by": list(args.affected_by),
        "closure": bool(args.closure),
        "requested_before_filter": requested_before_filter,
        "acl2_slots": acl2_slots.slot_count(),
        "timeout_seconds": args.timeout_seconds,
        "jobs": args.jobs,
        "jobs_effective": effective_jobs,
        "runner_sha256": digest(Path(__file__).resolve()),
        "reader_sha256": digest(READER),
        "status": "failed",
    }

    if acl2 is None or not os.access(acl2, os.X_OK):
        manifest["failure"] = (
            "ACL2 executable is unavailable. Install the pinned project toolchain "
            "or set FN_ACL2 to an executable ACL2 path."
        )
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 2

    try:
        source_digests = collect_book_sources(args.books)
        schedule = dependency_graph(args.books)
    except ValueError as error:
        manifest["acl2_executable"] = str(acl2)
        manifest["acl2_executable_sha256"] = digest(acl2)
        manifest["failure"] = str(error)
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 2
    manifest["source_digests_sha256"] = source_digests
    manifest["local_source_audit"] = {
        "method": "conservative lexical symbol scan plus human batch review; not macro expansion",
        "forbidden_facilities": sorted(FORBIDDEN_FACILITIES),
        "findings": audit_sources(source_digests),
        "scope": "local source closure only; installed ACL2/system books remain trusted",
    }
    if manifest["local_source_audit"]["findings"]:
        manifest["failure"] = "Local proof source uses a forbidden proof/trust facility."
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1

    manifest["acl2_executable"] = str(acl2)
    manifest["acl2_executable_sha256"] = digest(acl2)
    slot_wait_seconds: dict[str, float] = {}
    try:
        # Every ACL2 this runner starts, the version probe included, holds one
        # machine-wide slot for its lifetime.  Waiting here is correct: an
        # over-subscribed box swaps instead of certifying.
        with acl2_slots.slot("certify version probe") as held:
            slot_wait_seconds["version-probe"] = held.seconds
            version_result = run_acl2(acl2, acl2_version_driver(), args.timeout_seconds)
    except subprocess.TimeoutExpired as error:
        (run_dir / "version.log").write_bytes(timeout_output(error))
        manifest["failure"] = f"ACL2 version probe timed out after {args.timeout_seconds} seconds."
        write_json(run_dir / "manifest.json", manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1
    version_log = version_result.stdout.decode("utf-8", errors="replace")
    (run_dir / "version.log").write_text(version_log, encoding="utf-8")
    version_lines = [
        line.split("FN_ACL2_VERSION ", 1)[1]
        for line in version_log.splitlines()
        if "FN_ACL2_VERSION " in line
    ]
    manifest["acl2_version"] = version_lines[-1] if version_lines else None
    host_lisp_lines = [line.strip() for line in version_log.splitlines() if line.startswith("This is ")]
    manifest["host_lisp_banner"] = host_lisp_lines[0] if host_lisp_lines else None
    manifest["acl2_version_probe_exit_code"] = version_result.returncode

    driver_digests: dict[str, str] = {}
    drivers: dict[str, str] = {}
    nonce = secrets.token_hex(16)
    for book in args.books:
        driver = make_driver(book, nonce)
        driver_path = run_dir / (book.replace("/", "--") + ".certify.lsp")
        driver_path.write_text(driver, encoding="utf-8")
        driver_digests[book] = digest(driver_path)
        drivers[book] = driver

    outputs: dict[str, str] = {}
    exit_codes: dict[str, int | str] = {}
    book_wall_seconds: dict[str, float] = {}
    start_order: list[str] = []
    record_lock = threading.Lock()

    def certify(book: str) -> None:
        with acl2_slots.slot(f"certify {book}") as held:
            with record_lock:
                # Started means started, not queued: a book waiting for a slot
                # is not occupying one, and the schedule tests read this order.
                start_order.append(book)
                slot_wait_seconds[book] = held.seconds
            started = time.monotonic()
            try:
                result = run_acl2(acl2, drivers[book], args.timeout_seconds)
                output = result.stdout.decode("utf-8", errors="replace")
                code: int | str = result.returncode
            except subprocess.TimeoutExpired as error:
                output = timeout_output(error).decode("utf-8", errors="replace")
                code = f"timed out after {args.timeout_seconds} seconds"
            elapsed = time.monotonic() - started
        (run_dir / (book.replace("/", "--") + ".certify.log")).write_text(output, encoding="utf-8")
        with record_lock:
            outputs[book] = output
            exit_codes[book] = code
            book_wall_seconds[book] = round(elapsed, 3)

    certify_started = time.monotonic()
    run_schedule(args.books, schedule, effective_jobs, certify)
    certify_wall_seconds = round(time.monotonic() - certify_started, 3)

    # Evidence is assembled in requested order, never completion order, so the
    # combined log, the marker sequence and the exit codes do not depend on how
    # the scheduler interleaved the runs.
    markers: list[str] = []
    for book in args.books:
        markers.extend(success_markers(outputs[book], nonce))
    exit_codes = {book: exit_codes[book] for book in args.books}
    combined_log = "\n".join(outputs[book] for book in args.books)
    (run_dir / "certify.log").write_text(combined_log, encoding="utf-8")
    expected_markers = [success_token(book, nonce) for book in args.books]
    marker_ok = markers == expected_markers
    found_failures = [marker for marker in FAILURE_MARKERS if marker in combined_log]
    certificates = {
        book: digest(ROOT / f"{book}.cert")
        for book in args.books
        if (ROOT / f"{book}.cert").is_file()
    }
    certificates_ok = len(certificates) == len(args.books)
    try:
        source_digests_after = collect_book_sources(args.books)
    except ValueError as error:
        source_digests_after = {"closure-error": str(error)}
    sources_unchanged = source_digests_after == manifest["source_digests_sha256"]
    runner_unchanged = (
        digest(Path(__file__).resolve()) == manifest["runner_sha256"]
        and digest(READER) == manifest["reader_sha256"]
    )
    manifest.update(
        {
            "acl2_exit_codes": exit_codes,
            "book_wall_seconds": book_wall_seconds,
            "certify_wall_seconds": certify_wall_seconds,
            "start_order": start_order,
            "expected_success_markers": expected_markers,
            "observed_success_markers": markers,
            "failure_markers": found_failures,
            "driver_digests_sha256": driver_digests,
            "certificate_digests_sha256": certificates,
            "source_digests_sha256_after": source_digests_after,
            "runner_unchanged": runner_unchanged,
            "slot_wait_seconds": {key: round(value, 3)
                                  for key, value in slot_wait_seconds.items()},
        }
    )
    success = (
        version_result.returncode == 0
        and manifest["acl2_version"] is not None
        and all(code == 0 for code in exit_codes.values())
        and marker_ok
        and certificates_ok
        and sources_unchanged
        and runner_unchanged
        and not found_failures
    )
    if success:
        manifest["status"] = "passed"
        if not args.no_publish:
            # Publish against *this* run's manifest, which is the only thing
            # that ties a certificate to the source it was produced from.  The
            # cache keys on the whole include closure, so a pair is offered
            # back only to a worktree where every dependency also matches.  A
            # cache failure is recorded, never fatal: the certification itself
            # already succeeded.
            try:
                published = certs.publish(
                    ROOT, certs.cache_directory(),
                    [{**manifest, "evidence": str(run_dir)}], args.books,
                    # These certificates name their sub-books by absolute path
                    # inside *this* worktree, so that is where they may be
                    # installed; another live worktree must not take them.
                    origin=str(ROOT.resolve()))
                manifest["cert_cache"] = {
                    "directory": published.cache,
                    "published": published.published,
                    "already_cached": published.already,
                    "not_published": sorted(published.uncached + published.unverified
                                            + published.unreadable),
                }
            except OSError as error:
                manifest["cert_cache"] = {"error": str(error)}
    else:
        manifest["failure"] = "ACL2 did not produce complete clean certification evidence. See certify.log."
    write_json(run_dir / "manifest.json", manifest)

    if not success:
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1

    print("ACL2 certification passed: " + ", ".join(args.books))
    print(f"Certification evidence: {run_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
