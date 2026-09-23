#!/usr/bin/env python3
"""Certify fn's local ACL2 books and retain machine-readable run evidence.

This runner deliberately requires a real ACL2 executable.  In particular, an
ACL2 process exiting zero is insufficient evidence: each requested book must
emit the success marker from the successful branch of `certify-book`, and the
log must not contain an ACL2 certification/error marker.

`--pcert` runs ACL2's provisional certification (`:DOC
provisional-certification`) as three waves instead of one dependency-ordered
pass.  Create skips proofs and writes each book's `.pcert0`; Convert does
every proof, and because ACL2 accepts a sub-book's `.pcert0` there, **the
Converts have no dependencies on each other** and run as one parallel wave;
Complete renames `.pcert1` to `.cert` in dependency order.  What that buys is
not only speed: a normal closure run stops at the first failing book and
every book above it reads "There is no certificate on file", so one run names
one layer of independent reds, while one Convert wave names all of them.
Measured on a 63-book fn closure on persvati on 2026-09-22 with the same ACL2
and 8 jobs: the normal run took 690.8 s and named ONE independent red;
Create 32.9 s + Convert 301.4 s + Complete 2.6 s named FOUR, and the one they
share fails on the same form either way.  The certificates Complete writes
are byte-identical to normally produced ones apart from the absolute paths
they embed, carry no provisional marker, and ACL2 accepts them at
`include-book` (checked on that closure, 47 books).  Two cautions from the
ACL2 documentation: Complete checks sub-books' certificate WRITE DATES and
not their book-hash, and ACL2 itself says that for maximum trust a project's
books are best certified from scratch without it.  So `--pcert` is the
discovery mode; `tools/triage.py` is its report, and a claim about the tree
still comes from an ordinary run.
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
import socket
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
import acl2_toolchain  # noqa: E402
import certs  # noqa: E402
import evidence_manifests  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parent.parent
READER = Path(ledger.__file__).resolve()
BUILD_ROOT = ROOT / "build" / "acl2"
# Archived manifests, read only for the per-book wall times that order a
# parallel schedule (`archived_walls`).  Nothing about a verdict comes from here.
WALL_HISTORY = ROOT / "planning" / "evidence" / "manifests"
SUCCESS_PREFIX = "FN_CERTIFY_SUCCESS "
FAILURE_MARKERS = (
    "CERTIFICATION FAILED",
    "ACL2 Error",
    "HARD ACL2 ERROR",
)
BOOK_NAME = re.compile(r"(?:books|tests/acl2)/(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+$")
# ACL2's provisional certification, in the three waves `:DOC
# provisional-certification` names.  Create skips proofs and writes `.pcert0`;
# Convert does every proof given only its own `.pcert0` and a `.cert`,
# `.pcert0` or `.pcert1` for each included book, so Converts do not depend on
# each other and the whole tree's proofs run in one parallel wave; Complete
# renames `.pcert1` to `.cert` once every included book has a `.cert`.
PCERT_WAVES = {"create": ":create", "convert": ":convert", "complete": ":complete"}
PCERT_ORDER = ("create", "convert", "complete")
WAVE_PREFIX = "FN_PCERT_WAVE "
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


def wave_token(book: str, nonce: str, wave: str) -> str:
    """The marker a Create or Convert wave emits: a wave finished, not a book.

    It is nonce-tagged like the success token, so an old log cannot supply
    one, and it is deliberately NOT the success token: a book whose Convert
    passed has had all its proofs done and still has no certificate.
    """
    return (WAVE_PREFIX + wave.upper() + " " + nonce + " "
            + hashlib.sha256(book.encode()).hexdigest()[:12])


def wave_passed(output: str, book: str, nonce: str, wave: str) -> bool:
    """Did this wave reach its own marker for this book, in this run?"""
    token = wave_token(book, nonce, wave)
    return any(line.strip().endswith(token) for line in output.splitlines())


def success_markers(output: str, nonce: str) -> list[str]:
    # Only a whole marker line, optionally following the actual ACL2 prompt,
    # counts. Text echoed from a form, old logs, and unrelated runs cannot pass.
    pattern = re.compile(
        r"^(?:ACL2 [^\s]*>)?" + re.escape(SUCCESS_PREFIX + nonce + " ")
        + r"([a-f0-9]{12})$"
    )
    return [SUCCESS_PREFIX + nonce + " " + match.group(1)
            for line in output.splitlines() if (match := pattern.fullmatch(line))]


def book_result(book: str, output: str, exit_code: int | str, nonce: str,
                certificate: bool) -> tuple[str, list[str]]:
    """One book's verdict and, when it failed, why.

    An exit code is not a verdict.  The driver ends in `(quit)`, which ACL2
    reaches whether or not the inner `ld` returned on a failed `certify-book`,
    so a book whose certification failed in 0.2 s still exits 0 -- on
    2026-09-20 `tests/acl2/tcpcl-tests` was recorded that way in a farm run's
    manifest, whose only per-book result field was that zero, and was read as
    having passed.  The verdict is this book's own fresh nonce-tagged marker,
    its own log clean of ACL2's failure markers, and a certificate on disk.
    """
    reasons: list[str] = []
    if exit_code != 0:
        reasons.append(f"ACL2 exited {exit_code}")
    if success_markers(output, nonce) != [success_token(book, nonce)]:
        reasons.append("no fresh success marker in this book's log")
    observed = [marker for marker in FAILURE_MARKERS if marker in output]
    if observed:
        reasons.append("failure marker in this book's log: " + ", ".join(observed))
    if not certificate:
        reasons.append("no certificate on disk")
    return ("passed" if not reasons else "failed"), reasons


def publish_pair(book: str, verdict: str, run_dir: Path, nonce: str,
                 recorded_sources: dict[str, str], output: str,
                 exit_code: int | str,
                 toolchain_manifest: dict[str, Any]) -> dict[str, Any]:
    """Cache this book's pair the moment it certifies, not at the end of the run.

    Why here and not once at the end: a wide run on this tree exits non-zero
    while any root carries an open theorem, and until 2026-09-20 the
    end-of-run publish was inside `if success:`, so **a failed run cached
    nothing at all** -- measured: `run-20260920T203028Z-d411` on persvati
    certified 21 of 22 books and left 0 entries in the box cache, and the next
    submit into the same root reported `installed 0, kept 0, uncached 267`.  A
    run that is killed, that times out, or whose `farm.py wait` gives up loses
    the same way.  Publishing per book makes the cache reflect what has
    actually been certified at every moment of the run, for whoever certifies
    next on this box.

    The unit of trust is one book: its own fresh nonce-tagged marker, its own
    clean log, its own certificate, and its own closure unchanged since this
    run read it.  This passes `certs.publish` the whole source map the run
    recorded, and `certs.publish` re-checks the book's source, its
    certificate and every book in the closure it keys on; the decision about
    what a cache entry may be built from stays in one place.
    """
    event: dict[str, Any] = {"book": book, "verdict": verdict}
    if verdict != "passed":
        return event | {"published": False, "why": "this book did not pass"}
    certificate = ROOT / f"{book}.cert"
    if not certificate.is_file():
        return event | {"published": False, "why": "no certificate on disk"}
    partial = {
        "requested_books": [book],
        "expected_success_markers": [success_token(book, nonce)],
        "observed_success_markers": success_markers(output, nonce),
        "book_results": {book: verdict},
        "acl2_exit_codes": {book: exit_code},
        "source_digests_sha256": recorded_sources,
        "source_digests_sha256_after": {
            f"{book}.lisp": digest(book_source(book))},
        "certificate_digests_sha256": {book: digest(certificate)},
        "evidence": str(run_dir),
        # A killed run has no final sweep.  Its already-passing books still
        # need the exact toolchain identity now required by set installation;
        # otherwise the per-book publication promised above is present in the
        # cache but unusable by every coherent selector.
        **{field: toolchain_manifest.get(field) for field in (
            "acl2_version", "acl2_executable_sha256", "environment",
            "acl2_toolchain", "acl2_toolchain_identity",
            "acl2_compatibility", "runner_sha256", "reader_sha256")},
    }
    try:
        report = certs.publish(ROOT, certs.cache_directory(), [partial], [book],
                               origin=str(ROOT.resolve()))
    except OSError as error:
        return event | {"published": False, "why": f"cache write failed: {error}"}
    event["published"] = bool(report.published)
    event["already_cached"] = bool(report.already)
    if not report.published and not report.already:
        event["why"] = "; ".join(report.unverified + report.uncached
                                 + report.unreadable) or "no pair offered"
    return event


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


def make_driver(book: str, nonce: str, wave: str | None = None) -> str:
    """The ld that certifies one book, or runs one provisional-certification wave.

    `certify-book` must run at the top level of an ACL2 ld.  On an error, the
    inner ld returns before it reaches the marker; this catches ACL2 failures
    even when the surrounding process eventually exits zero.

    The nonce-tagged success token means one thing and keeps meaning it: this
    book is certified.  A Create or Convert wave therefore emits its own wave
    marker instead, and only Complete -- the wave that writes the `.cert` --
    emits the token.  So `book_result`'s rule is unchanged under `--pcert`:
    exactly one fresh token, a log with no failure marker, a certificate on
    disk.  See `PCERT_WAVES` for what each wave is.
    """
    if wave is None:
        return f'''(ld '((certify-book "{book}" 0 t)
      (value-triple (cw "~%{success_token(book, nonce)}~%")))
    :ld-error-action :return
    :ld-error-triples t)
(quit)
'''
    marker = (success_token(book, nonce) if wave == "complete"
              else wave_token(book, nonce, wave))
    return f'''(ld '((certify-book "{book}" 0 t :pcert {PCERT_WAVES[wave]})
      (value-triple (cw "~%{marker}~%")))
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


def archived_walls(books: list[str], history: Path | None = None) -> dict[str, float]:
    """Each book's most recently archived wall time, for the books that have one.

    Archived run ids begin with a UTC stamp, so file-name order is time order
    and a later run's measurement replaces an earlier one.  A missing or
    unreadable manifest is skipped: this is a scheduling estimate, and a
    wrong estimate only costs time, never evidence.
    """
    history = WALL_HISTORY if history is None else history
    wanted = set(books)
    measured: dict[str, float] = {}
    for path in sorted(history.glob("certify-*.json")) if history.is_dir() else []:
        try:
            walls = json.loads(path.read_text(encoding="utf-8")).get("book_wall_seconds") or {}
        except (OSError, ValueError, AttributeError):
            continue
        for book, seconds in walls.items():
            if book in wanted and isinstance(seconds, (int, float)) and seconds >= 0:
                measured[book] = float(seconds)
    return measured


def critical_path_priority(books: list[str], graph: dict[str, set[str]],
                           walls: dict[str, float]) -> dict[str, float]:
    """For each book, its own wall plus the longest chain of dependents above it.

    Starting the ready book with the largest value first is the classic
    critical-path list schedule: the chain that bounds the run from below
    starts as early as its dependencies allow instead of waiting behind
    small books that happen to come first in the requested order.  With no
    edges (the Convert wave) it is longest-book-first.
    """
    dependents: dict[str, list[str]] = {book: [] for book in books}
    for book in books:
        for dependency in graph[book]:
            dependents[dependency].append(book)
    level: dict[str, float] = {}
    # Requested order is dependencies-first, so its reverse visits every
    # dependent before the books it includes.
    for book in reversed(topological(books, graph)):
        level[book] = walls.get(book, 1.0) + max(
            (level[dependent] for dependent in dependents[book]), default=0.0)
    return level


def topological(books: list[str], graph: dict[str, set[str]]) -> list[str]:
    """`books` with every book after its requested dependencies, stable."""
    placed: set[str] = set()
    ordered: list[str] = []
    pending = list(books)
    while pending:
        rest = [book for book in pending if not graph[book] <= placed]
        ready = [book for book in pending if graph[book] <= placed]
        if not ready:
            raise ValueError("certification schedule has a cycle: " + ", ".join(rest))
        ordered.extend(ready)
        placed.update(ready)
        pending = rest
    return ordered


def run_schedule(
    books: list[str],
    graph: dict[str, set[str]],
    jobs: int,
    certify: Any,
    priority: dict[str, float] | None = None,
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
    Given `priority`, the ready book with the largest value starts first and
    requested order breaks ties (`critical_path_priority`).
    """
    waiting = {book: set(graph[book]) for book in books}
    queue = list(books)
    if priority is not None:
        # A stable sort, so equal priorities keep requested order; the scan
        # below then takes the first ready book in this order.
        queue.sort(key=lambda book: -priority.get(book, 0.0))
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


def pcert_waves(books: list[str], graph: dict[str, set[str]], jobs: int,
                run_wave: Any, walls: dict[str, float] | None = None) -> dict[str, float]:
    """Create, Convert, Complete, and how long each wave took.

    Create and Complete are dependency-ordered: Create of a book needs its
    sub-books' `.pcert0`, Complete needs their `.cert`.  **Convert has no
    edges at all** -- ACL2 accepts a sub-book's `.pcert0` in place of a
    certificate there -- so every book's proofs run in one wave at `jobs`,
    and one wave reports every independent red in the closure instead of the
    first layer of them.  Measured on a 63-book fn closure on persvati,
    2026-09-22: Create 32.9 s, Convert 301.4 s at 8 jobs (its floor is the
    slowest single proof, 289.4 s), Complete 2.6 s; the same closure
    certified normally took 690.8 s and named one independent red where the
    Convert wave named four.

    A wave that a book did not reach -- because its own previous wave failed
    -- is not run for that book, and `run_wave` is told so.
    """
    walls: dict[str, float] = {}
    for wave in PCERT_ORDER:
        started = time.monotonic()
        if wave == "convert":
            # No edges: the whole tree's proofs at once.
            free = {book: set() for book in books}
            run_schedule(books, free, jobs,
                         lambda book: run_wave(book, "convert"),
                         None if walls is None
                         else critical_path_priority(books, free, walls))
        else:
            run_schedule(books, graph, jobs,
                         lambda book, wave=wave: run_wave(book, wave),
                         None if walls is None
                         else critical_path_priority(books, graph, walls))
        walls[wave] = round(time.monotonic() - started, 3)
    return walls


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def record(run_dir: Path, manifest: dict[str, Any]) -> None:
    """Write the run's manifest and file the durable copy beside it.

    `build/` is ignored, so the run directory this returns to the caller is
    the one a lane cites and the one a worktree removal or a gate reaper
    deletes.  The manifest is the claim and is 4 kB to 200 kB; it goes to
    `planning/evidence/manifests/<run-id>.json`, which is committable.  The
    log stays here, and the archived copy records where here was.
    """
    write_json(run_dir / "manifest.json", manifest)
    evidence_manifests.archive_run(run_dir, ROOT)


def git_facts() -> dict[str, Any]:
    """The revision this run certified, for a reader who has only the manifest.

    The source digests say WHAT was certified; this says where to find it.
    A mirrored remote root may not be a repository at all, and then every
    field is None rather than a failure.
    """
    def ask(*args: str) -> str | None:
        try:
            result = subprocess.run(["git", "-C", str(ROOT), *args],
                                    capture_output=True, text=True, check=False,
                                    timeout=30)
        except (OSError, subprocess.SubprocessError):
            return None
        return result.stdout.strip() if result.returncode == 0 else None

    revision = ask("rev-parse", "HEAD")
    dirty = ask("status", "--porcelain")
    return {
        "git_revision": revision,
        "git_branch": ask("rev-parse", "--abbrev-ref", "HEAD"),
        "git_dirty": None if dirty is None else bool(dirty),
    }


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
    parser.add_argument(
        "--pcert",
        action="store_true",
        help=(
            "certify through ACL2's provisional certification: a Create wave "
            "that skips proofs, one parallel Convert wave that does every "
            "book's proofs, and a Complete wave that writes the certificates. "
            "One run then reports EVERY independent red in the closure rather "
            "than the first layer of them"
        ),
    )
    parser.add_argument(
        "--budget-seconds",
        type=int,
        default=None,
        metavar="SECONDS",
        help=(
            "per-book budget for the --pcert Convert wave, which is where the "
            "proofs are (default: --timeout-seconds). Create and Complete keep "
            "--timeout-seconds; they skip proofs and are seconds each"
        ),
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
    if args.budget_seconds is None:
        args.budget_seconds = args.timeout_seconds
    elif args.budget_seconds <= 0:
        parser.error("--budget-seconds must be positive")
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
        # Identity first: a manifest that has left its directory behind must
        # still say which run it is, on which box, of which revision.
        "run_id": run_dir.name,
        "hostname": socket.gethostname(),
        "tree": str(ROOT),
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        **git_facts(),
        "command": [configured],
        "environment": {"ACL2_CUSTOMIZATION": "NONE", "ACL2_BOOK_HASH_ALISTP": "NIL", "ACL2_SYSTEM_BOOKS": None},
        "platform": platform.platform(),
        "python": platform.python_version(),
        "requested_books": args.books,
        "affected_by": list(args.affected_by),
        "closure": bool(args.closure),
        "pcert": bool(args.pcert),
        "budget_seconds": args.budget_seconds,
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
        record(run_dir, manifest)
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
        record(run_dir, manifest)
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
        record(run_dir, manifest)
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1

    manifest["acl2_executable"] = str(acl2)
    # `acl2_executable_sha256` is retained as launcher audit provenance for old
    # manifests.  It is not a cache compatibility identity: generated ACL2
    # launchers are small shell scripts whose saved core may change in place.
    manifest["acl2_executable_sha256"] = digest(acl2)
    toolchain = acl2_toolchain.fingerprint(acl2)
    manifest["acl2_toolchain"] = toolchain.provenance
    manifest["acl2_toolchain_identity"] = toolchain.identity
    manifest["acl2_compatibility"] = toolchain.compatibility
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
        record(run_dir, manifest)
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
    waves = PCERT_ORDER if args.pcert else (None,)
    for book in args.books:
        flat = book.replace("/", "--")
        for wave in waves:
            driver = make_driver(book, nonce, wave)
            suffix = f".pcert-{wave}" if wave else ""
            driver_path = run_dir / (flat + suffix + ".certify.lsp")
            driver_path.write_text(driver, encoding="utf-8")
            driver_digests[f"{book}{suffix}"] = digest(driver_path)
            drivers[f"{book}{suffix}"] = driver

    outputs: dict[str, str] = {}
    exit_codes: dict[str, int | str] = {}
    book_wall_seconds: dict[str, float] = {}
    start_order: list[str] = []
    record_lock = threading.Lock()
    # One publisher at a time: `certs.publish` reads and renames files in the
    # cache, and two books finishing together must not interleave there.
    publish_lock = threading.Lock()
    cache_events: list[dict[str, Any]] = []

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
        if args.no_publish:
            return
        verdict, _ = book_result(book, output, code, nonce,
                                 (ROOT / f"{book}.cert").is_file())
        with publish_lock:
            cache_events.append(publish_pair(book, verdict, run_dir, nonce,
                                             source_digests, output, code,
                                             manifest))

    # Under `--pcert` a book's evidence is three ACL2 runs, and what the run
    # records for it is their concatenation, each behind a wave line.  The
    # verdict rule is untouched: `book_result` reads that combined log, the
    # first exit code that was not 0, and the certificate on disk.
    wave_outputs: dict[str, dict[str, str]] = {book: {} for book in args.books}
    wave_seconds: dict[str, dict[str, float]] = {book: {} for book in args.books}
    wave_codes: dict[str, dict[str, int | str]] = {book: {} for book in args.books}
    pcert_reached: dict[str, str] = {}

    def run_wave(book: str, wave: str) -> None:
        previous = PCERT_ORDER[PCERT_ORDER.index(wave) - 1] if wave != "create" else None
        if previous is not None and not wave_passed(
                wave_outputs[book].get(previous, ""), book, nonce, previous):
            # Its own previous wave did not finish, so this one has no input.
            # Not running it is the finding, and the combined log says so.
            wave_outputs[book][wave] = (
                f"{WAVE_PREFIX}{wave.upper()} NOT RUN: this book's {previous} "
                f"wave did not finish\n")
            return
        budget = args.budget_seconds if wave == "convert" else args.timeout_seconds
        with acl2_slots.slot(f"pcert {wave} {book}") as held:
            with record_lock:
                start_order.append(f"{book} {wave}")
                slot_wait_seconds[f"{book} {wave}"] = held.seconds
            started = time.monotonic()
            try:
                result = run_acl2(acl2, drivers[f"{book}.pcert-{wave}"], budget)
                output = result.stdout.decode("utf-8", errors="replace")
                code: int | str = result.returncode
            except subprocess.TimeoutExpired as error:
                output = timeout_output(error).decode("utf-8", errors="replace")
                code = f"timed out after {budget} seconds"
            elapsed = time.monotonic() - started
        (run_dir / (book.replace("/", "--") + f".pcert-{wave}.certify.log")
         ).write_text(output, encoding="utf-8")
        with record_lock:
            wave_outputs[book][wave] = output
            wave_codes[book][wave] = code
            wave_seconds[book][wave] = round(elapsed, 3)
            # Complete emits the success token, not a wave token: it is the
            # wave that certifies, so it speaks in the one marker that means
            # certified.
            reached = (success_markers(output, nonce)
                       == [success_token(book, nonce)]
                       if wave == "complete"
                       else wave_passed(output, book, nonce, wave))
            if reached:
                pcert_reached[book] = wave

    def collect_pcert(book: str) -> None:
        """One book's three waves as the one log and one code the rule reads."""
        parts = []
        for wave in PCERT_ORDER:
            parts.append(f"{WAVE_PREFIX}{wave.upper()} {book}")
            parts.append(wave_outputs[book].get(wave, ""))
        output = "\n".join(parts)
        # The same file name a closure run writes, so every reader of a run
        # directory -- `tools/triage.py` included -- finds one log per book
        # whichever mode produced it.  The per-wave logs stay beside it.
        (run_dir / (book.replace("/", "--") + ".certify.log")).write_text(
            output, encoding="utf-8")
        codes = [wave_codes[book].get(wave) for wave in PCERT_ORDER]
        bad = next((code for code in codes if code not in (0, None)), None)
        outputs[book] = output
        exit_codes[book] = 0 if bad is None else bad
        book_wall_seconds[book] = round(
            sum(wave_seconds[book].get(wave, 0.0) for wave in PCERT_ORDER), 3)
        if args.no_publish:
            return
        verdict, _ = book_result(book, output, exit_codes[book], nonce,
                                 (ROOT / f"{book}.cert").is_file())
        with publish_lock:
            cache_events.append(publish_pair(book, verdict, run_dir, nonce,
                                             source_digests, output,
                                             exit_codes[book], manifest))

    # One job keeps requested order exactly; more than one starts the longest
    # remaining chain first, by the archived walls of each book.
    # A book never measured counts one second.
    walls: dict[str, float] | None = None
    priority: dict[str, float] | None = None
    manifest["schedule"] = {"policy": "requested-order"}
    if effective_jobs > 1:
        measured = archived_walls(args.books)
        walls = {book: measured.get(book, 1.0) for book in args.books}
        priority = critical_path_priority(args.books, schedule, walls)
        manifest["schedule"] = {
            "policy": "critical-path-first",
            "books_with_archived_wall": len(measured),
            "predicted_critical_path_seconds": round(max(priority.values()), 3),
        }
    certify_started = time.monotonic()
    if args.pcert:
        pcert_wall_seconds = pcert_waves(args.books, schedule, effective_jobs,
                                         run_wave, walls)
        for book in args.books:
            collect_pcert(book)
    else:
        pcert_wall_seconds = None
        run_schedule(args.books, schedule, effective_jobs, certify, priority)
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
    verdicts = {book: book_result(book, outputs[book], exit_codes[book], nonce,
                                  book in certificates)
                for book in args.books}
    book_results = {book: verdict for book, (verdict, _) in verdicts.items()}
    book_failures = {book: reasons for book, (_, reasons) in verdicts.items() if reasons}
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
            "book_results": book_results,
            "book_failures": book_failures,
            "book_wall_seconds": book_wall_seconds,
            "certify_wall_seconds": certify_wall_seconds,
            "pcert_wall_seconds": pcert_wall_seconds,
            # The last provisional wave each book finished.  A book that
            # reached `convert` has had every one of its proofs done and may
            # still have no certificate, because a book below it has none:
            # that is the distinction a closure run cannot make at all.
            "pcert_reached": dict(pcert_reached) if args.pcert else None,
            "book_wave_seconds": ({book: wave_seconds[book]
                                   for book in args.books}
                                  if args.pcert else None),
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
        and all(verdict == "passed" for verdict in book_results.values())
        and marker_ok
        and certificates_ok
        and sources_unchanged
        and runner_unchanged
        and not found_failures
    )
    if not args.no_publish:
        # The sweep after the per-book publishes, and it runs whatever THIS
        # RUN's verdict was.  A book's pair is trustworthy on that book's own
        # evidence -- its fresh marker, its clean log, its certificate, its
        # unchanged source -- and `certs.publish` re-checks every one of those
        # against this manifest.  The run verdict is a statement about the
        # whole requested batch, and gating the cache on it is what made a
        # failed wide run cache nothing and the next lane re-certify what this
        # one had already proved.  What the sweep still adds over the per-book
        # publishes: a book whose closure was being written when it finished,
        # and a run whose books were certified by an older runner.
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
                "per_book": cache_events,
                "per_book_published": sum(1 for event in cache_events
                                          if event.get("published")),
            }
        except OSError as error:
            manifest["cert_cache"] = {"error": str(error), "per_book": cache_events}
    if success:
        manifest["status"] = "passed"
    else:
        failed = [book for book, verdict in book_results.items() if verdict == "failed"]
        manifest["failure"] = (
            "ACL2 did not produce complete clean certification evidence. See certify.log."
            + (" Books that failed: " + ", ".join(failed) if failed else ""))
    manifest["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    record(run_dir, manifest)

    if not success:
        print(manifest["failure"], file=sys.stderr)
        print(f"Certification evidence: {run_dir.relative_to(ROOT)}", file=sys.stderr)
        return 1

    print("ACL2 certification passed: " + ", ".join(args.books))
    print(f"Certification evidence: {run_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
