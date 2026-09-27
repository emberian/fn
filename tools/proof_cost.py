#!/usr/bin/env python3
"""Report measured ACL2 book cost at the current source and include closure.

This is not a certification or cache-validity check. The default scans
archived and local manifests for measured attempts of each book at its current
include-closure bytes. An installed certificate has no proof time in that run.
`--manifest` keeps the one-run diagnostic and never fails.

Two numbers, two jobs (D26 as amended 2026-09-27, docs/proofs.md "Proof cost"):

- **Prover steps** are the ratchet. ACL2 counts them itself (`Prover steps
  counted:` in the CERTIFY-BOOK summary, tools/acl2_cost.py) and the same bytes
  and toolchain give the same count on any box at any load. A baseline book
  fails when its steps are more than STEP_TOLERANCE over its row's.
- **Wall seconds** decide whether a book is over the ten-second rule at all.
  Load only ever adds seconds (on hbox's and persvati's hybrid cores a loaded
  box moves a 2-job certification onto slow cores: the same bytes measured 6.4
  and 14.9 s), so a book's D26 seconds are the LOWEST passed measurement at
  two jobs or fewer of its current bytes, over every run, host and toolchain.
  At or under the threshold that settles it (it can only be faster quiet). Over
  it, the number is conclusive only when the measurement was quiet (the box's
  one-minute load average at most QUIET_LOAD_FRACTION of its CPUs when the
  book's ACL2 process started and ended; `book_load_average` and `cpu_count`
  in the manifest) or when it exceeds LOAD_FACTOR times the line (more than
  load has been seen to add). Otherwise it prints UNQUIET, a warning naming
  the run and the command for a quiet re-measure, and never fails.

A book not in planning/proof-cost-baseline.json fails when conclusively over
threshold * (1 + NEAR_BAND); between the line and that it prints NEAR (D30).
A baseline row without steps (written before 2026-09-27) is ratcheted by its
seconds, under the same quiet rule, until a measurement supplies steps.
A failed certification measures no cost: it prints FAILED, keeps its baseline
row, and is never IMPROVED. Measurements at more than RATCHET_JOBS jobs print
RECORDED and never ratchet; a manifest without `jobs_effective` is unknown and
skipped with a warning. `--write-baseline` drops improved books, lowers steps
and seconds, never raises either and refuses to add a row unless
`--allow-regression` is given. The baseline only shrinks.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field, replace
from datetime import datetime
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "proof-cost-baseline.json"
TOLERANCE = 0.25
# Prover steps are deterministic for fixed bytes and toolchain, so their band
# only has to absorb a changed include closure's rules, not noise.
STEP_TOLERANCE = 0.10
# A measurement is quiet when the box's one-minute load average stayed at or
# below this fraction of its CPUs over the book's process: with at most a
# quarter of the logical CPUs busy, a 2-job certification keeps performance
# cores on either box.
QUIET_LOAD_FRACTION = 0.25
# Load has been measured to multiply a book's wall by up to 2.6 (hbox load
# 11-22, 17 s against 45 s; persvati 6.4 against 14.9 s).  A figure above this
# multiple of a line is over it whatever the load.
LOAD_FACTOR = 3.0
# A book not in the baseline fails only above threshold * (1 + NEAR_BAND); between
# the threshold and that line it prints NEAR (D30, 2026-09-25).
NEAR_BAND = 0.10
# D26: the ten-second rule is measured at this many concurrent jobs or fewer.
RATCHET_JOBS = 2
SCOPED, WIDE, UNKNOWN = "scoped", "wide", "unknown"
sys.path.insert(0, str(Path(__file__).resolve().parent))
import acl2_cost  # noqa: E402
import certs  # noqa: E402
import green_check  # noqa: E402
import ledger  # noqa: E402



def latest_manifest(root: Path) -> Path | None:
    candidates = (root / "build" / "acl2").glob("certify-*/manifest.json")
    return max(candidates, key=lambda path: path.stat().st_mtime, default=None)


def read_log(log: Path) -> str | None:
    try:
        return log.read_text(encoding="utf-8", errors="replace") if log.is_file() else None
    except OSError:
        return None


def slowest_event(log: Path) -> tuple[str, float] | None:
    text = read_log(log)
    event = acl2_cost.slowest_event(text) if text is not None else None
    return (event.form, event.seconds) if event is not None else None


def event_detail(log: Path, recorded: dict | None = None) -> str:
    """The costliest event by prover steps (and the slowest by time) of a book.

    `recorded` is the manifest's `book_costliest_event` entry, which survives
    archiving; the local log, where it exists, adds the slowest event.
    """
    text = read_log(log)
    parts = []
    heaviest = acl2_cost.costliest_event(text) if text is not None else None
    if heaviest is not None:
        parts.append(f"costliest-event={heaviest.form} {heaviest.steps:,} steps")
    elif isinstance(recorded, dict) and isinstance(recorded.get("steps"), int):
        parts.append(f"costliest-event={recorded.get('form')} {recorded['steps']:,} steps")
    slow = acl2_cost.slowest_event(text) if text is not None else None
    if slow is not None:
        parts.append(f"slowest-event={slow.form} {slow.seconds:.2f}s")
    return "; " + "; ".join(parts) if parts else "; per-event=unavailable"


def number(value) -> float | None:
    if isinstance(value, (int, float)) and not isinstance(value, bool) and value >= 0:
        return float(value)
    return None


def book_load(manifest: dict, book: str) -> float | None:
    """The higher of the load averages at the book's process start and end."""
    pair = (manifest.get("book_load_average") or {}).get(book)
    if not isinstance(pair, list):
        return None
    values = [value for value in map(number, pair) if value is not None]
    return max(values) if values else None


def book_steps(manifest: dict, book: str, log: Path | None = None) -> int | None:
    value = (manifest.get("book_prover_steps") or {}).get(book)
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    text = read_log(log) if log is not None else None
    return acl2_cost.book_steps(text) if text is not None else None


def quietness(load: float | None, cpus: int | None) -> bool | None:
    """True quiet, False loaded, None when the run did not record its load."""
    if load is None or not cpus:
        return None
    return load <= QUIET_LOAD_FRACTION * cpus


def load_words(load: float | None, cpus: int | None) -> str:
    if load is None or not cpus:
        return "load=unrecorded"
    word = "quiet" if quietness(load, cpus) else "loaded"
    return f"load={load:g}/{cpus}cpu ({word})"


def source_scope(manifest: dict, checkout: Path = ROOT) -> str:
    named_tree = manifest.get("tree")
    tree = Path(named_tree) if named_tree else None
    sources = manifest.get("source_digests_sha256") or {}
    if not isinstance(sources, dict) or not sources:
        return "source-closure=current-bytes unavailable"
    # Archived farm manifests keep their original absolute `tree` path, which
    # is often unavailable on the machine reading the archive. Their relative
    # source digests still let us say whether this checkout has those bytes.
    # Keep the scope explicit: that is a checkout comparison, not a statement
    # that this was the tree used by the run.
    if tree is not None and tree.is_dir():
        comparison_root, comparison = tree, "manifest-tree comparison"
    else:
        comparison_root, comparison = checkout, "checkout comparison"
    stale = 0
    for relative, expected in sources.items():
        path = comparison_root / relative
        try:
            matches = path.is_file() and certs.content_hash(path) == expected
        except OSError:
            matches = False
        if not matches:
            stale += 1
    return (f"source-closure={'stale' if stale else 'matches'} "
            f"({stale} of {len(sources)} source digests differ; {comparison})")


def elapsed_seconds(manifest: dict) -> str:
    try:
        first = datetime.fromisoformat(manifest["started_utc"])
        last = datetime.fromisoformat(manifest["finished_utc"])
        return f"{(last - first).total_seconds():.0f}s (timestamp precision)"
    except (KeyError, TypeError, ValueError):
        return "unavailable"


def report(path: Path, threshold: float) -> list[str]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    walls = manifest.get("book_wall_seconds") or {}
    results = manifest.get("book_results") or {}
    installed = manifest.get("installed_books") or {}
    if not isinstance(walls, dict) or not isinstance(results, dict) or not isinstance(installed, dict):
        raise ValueError("manifest timing or provenance fields have the wrong shape")
    measured = {book: float(value) for book, value in walls.items()
                if isinstance(value, (int, float)) and not isinstance(value, bool) and value >= 0}
    waits = manifest.get("slot_wait_seconds") or {}
    wait_total = sum(float(value) for value in waits.values()
                     if isinstance(value, (int, float)) and value >= 0)
    lines = [
        f"manifest={path} status={manifest.get('status', 'unknown')}",
        f"source={manifest.get('git_revision') or 'unknown'} "
        f"toolchain={manifest.get('acl2_toolchain_identity') or 'unknown'} "
        f"host={manifest.get('hostname', 'unknown')} jobs={manifest.get('jobs_effective', 'unknown')}",
        source_scope(manifest),
        ("ratchet: " + {SCOPED: f"eligible (<= {RATCHET_JOBS} jobs)",
                        WIDE: f"recorded only (above {RATCHET_JOBS} jobs; D26)",
                        UNKNOWN: "skipped (manifest has no jobs_effective)"}
         [jobs_band(manifest_jobs(manifest))]),
        f"scope: installed={len(installed)} certified-attempted={len(results)} "
        f"measured-books={len(measured)}",
        f"wall: total={elapsed_seconds(manifest)}; "
        f"certification={manifest.get('certify_wall_seconds', 'unavailable')}s; "
        f"sum-of-book-process-walls={sum(measured.values()):.3f}s; "
        f"sum-of-slot-waits={wait_total:.3f}s; CPU=unavailable",
    ]
    cpus = manifest.get("cpu_count") if isinstance(manifest.get("cpu_count"), int) else None
    for book, seconds in sorted(measured.items(), key=lambda item: (-item[1], item[0])):
        if seconds <= threshold:
            continue
        log = path.parent / (book.replace("/", "--") + ".certify.log")
        detail = event_detail(log, (manifest.get("book_costliest_event") or {}).get(book))
        steps = book_steps(manifest, book, log)
        lines.append(f"WARNING {book}: process-wall={seconds:.3f}s > {threshold:g}s"
                     f" steps={'unknown' if steps is None else f'{steps:,}'}"
                     f" {load_words(book_load(manifest, book), cpus)}"
                     f" verdict={results.get(book, 'unknown')}{detail}")
    if not any(line.startswith("WARNING ") for line in lines):
        lines.append(f"No measured book exceeds {threshold:g}s.")
    return lines


@dataclass(frozen=True)
class Measurement:
    book: str
    seconds: float
    verdict: str
    run_id: str
    host: str
    toolchain: str
    jobs: int | None = None
    steps: int | None = None
    load: float | None = None
    cpus: int | None = None

    @property
    def band(self) -> str:
        return jobs_band(self.jobs)

    @property
    def passed(self) -> bool:
        return self.verdict == "passed"

    @property
    def quiet(self) -> bool | None:
        return quietness(self.load, self.cpus)

    def words(self) -> str:
        steps = "unknown" if self.steps is None else f"{self.steps:,}"
        return (f"steps={steps} {load_words(self.load, self.cpus)} host={self.host} "
                f"jobs={self.jobs} run={self.run_id}")


def manifest_jobs(manifest: dict) -> int | None:
    """The run's certification concurrency, or None when it did not say."""
    value = manifest.get("jobs_effective")
    if isinstance(value, int) and not isinstance(value, bool) and value >= 1:
        return value
    return None


def jobs_band(jobs: int | None) -> str:
    if jobs is None:
        return UNKNOWN
    return SCOPED if jobs <= RATCHET_JOBS else WIDE


def current_books(root: Path) -> set[str]:
    """The current Makefile-root closure, even before the ledger is rewritten."""
    books: set[str] = set()
    for name in ledger.makefile_roots():
        books.update(certs.closure(root, name))
    return books


def history(root: Path, books: set[str], *, toolchain: str | None = None,
            host: str | None = None,
            runs: list[tuple[green_check.Run, dict]] | None = None
            ) -> tuple[dict[tuple[str, str, str, str], Measurement], set[str], int]:
    """Select timed attempts; certs owns current closure hashing/comparison.

    `book_wall_seconds` names work attempted in that run. An installed-only
    row never replaces an earlier measured attempt, and a failed attempt
    retains its failed verdict. Shared dependency bytes are memoized by
    certs.book_facts, and each requested book's closure is built only once.

    One measurement is kept per book, host, toolchain and jobs band
    (SCOPED, WIDE, UNKNOWN), so a newer wide run never hides the scoped
    number the ratchet reads (D26). Every candidate measured the same
    closure bytes, and load only adds seconds, so the kept one is the
    FASTEST passed attempt (the least-loaded); a book with no passed attempt
    keeps its newest failed one, which names it FAILED and is never a cost.
    Steps missing from an older manifest are read from the run's local
    certify log where it still exists.
    """
    runs = green_check.manifests(root) if runs is None else runs
    closures: dict[str, list[str] | None] = {}
    selected: dict[tuple[str, str, str, str], Measurement] = {}
    installed_current: set[str] = set()
    measured_rows = 0

    def listing(book: str) -> list[str] | None:
        if book not in closures:
            try:
                closures[book] = certs.closure_listing(certs.closure(root, book))
            except (certs.UnreadableBook, OSError):
                closures[book] = None
        return closures[book]

    # Each manifest's recorded digests as the `<path>.lisp:<sha256>` entries a
    # closure listing holds: "no drift" is then the listing being a subset,
    # one set operation per (book, manifest) instead of a Python loop over
    # the closure (208,852 closure_drift calls in `make check`).  Same rule
    # as certs.closure_drift: an unrecorded or different digest is drift.
    entries: dict[int, tuple[frozenset | None, frozenset | None]] = {}

    def recorded(manifest: dict) -> tuple[frozenset | None, frozenset | None]:
        remembered = entries.get(id(manifest))
        if remembered is None:
            def entry_set(digests):
                if not isinstance(digests, dict):
                    return None
                return frozenset(f"{path}:{digest}" for path, digest in digests.items())
            remembered = (entry_set(manifest.get("source_digests_sha256") or {}),
                          entry_set(manifest.get("source_digests_sha256_after") or {})
                          if manifest.get("source_digests_sha256_after") else frozenset())
            entries[id(manifest)] = remembered
        return remembered

    def matches(book: str, manifest: dict) -> bool:
        if book not in books:
            return False
        key = listing(book)
        if key is None:
            return False
        sources, after = recorded(manifest)
        return (sources is not None and sources.issuperset(key)
                and (not manifest.get("source_digests_sha256_after")
                     or (after is not None and after.issuperset(key))))

    for run, manifest in runs:
        identity = str(manifest.get("acl2_toolchain_identity") or "unknown")
        machine = run.where
        if (toolchain is not None and identity != toolchain
                or host is not None and machine != host):
            continue
        walls = manifest.get("book_wall_seconds") or {}
        results = manifest.get("book_results") or {}
        installed = manifest.get("installed_books") or {}
        jobs = manifest_jobs(manifest)
        cpus = manifest.get("cpu_count")
        cpus = cpus if isinstance(cpus, int) and not isinstance(cpus, bool) and cpus > 0 else None
        if not all(isinstance(field, dict) for field in (walls, results, installed)):
            continue
        for book in installed:
            if book not in walls and matches(book, manifest):
                installed_current.add(book)
        for book, seconds in walls.items():
            if (book in installed or not isinstance(seconds, (int, float))
                    or isinstance(seconds, bool) or seconds < 0):
                continue
            measured_rows += 1
            if not matches(book, manifest):
                continue
            key = (book, machine, identity, jobs_band(jobs))
            record = Measurement(
                book, float(seconds), str(results.get(book, "unknown")),
                run.run_id, machine, identity, jobs,
                book_steps(manifest, book), book_load(manifest, book), cpus)
            prior = selected.get(key)
            # green_check.manifests is ordered by run-id timestamp; a newer
            # partial run only replaces the books it actually measured, a
            # passed attempt is never replaced by a failed one, and a slower
            # passed attempt of the same bytes never replaces a faster one.
            if (prior is None
                    or (record.passed and not prior.passed)
                    or (record.passed == prior.passed
                        and (not record.passed or record.seconds < prior.seconds))):
                if record.passed and record.steps is None and prior is not None \
                        and prior.passed and prior.steps is not None:
                    record = replace(record, steps=prior.steps)
                selected[key] = record
            elif record.passed and prior.steps is None and record.steps is not None:
                selected[key] = replace(prior, steps=record.steps)
    for key, record in selected.items():
        if record.steps is None and record.passed:
            log = (root / "build/acl2" / record.run_id
                   / (record.book.replace("/", "--") + ".certify.log"))
            steps = book_steps({}, record.book, log)
            if steps is not None:
                selected[key] = replace(record, steps=steps)
    return selected, installed_current, measured_rows


def history_report(root: Path, threshold: float, *, toolchain: str | None = None,
                   host: str | None = None,
                   books: set[str] | None = None,
                   runs: list[tuple[green_check.Run, dict]] | None = None,
                   computed: tuple[dict, set[str], int] | None = None
                   ) -> list[str]:
    books = current_books(root) if books is None else books
    selected, installed, rows = computed or history(
        root, books, toolchain=toolchain, host=host, runs=runs)
    measured_books = {record.book for record in selected.values()}
    missing = books - measured_books
    installed_only = missing & installed
    lines = [
        f"scope: current-root-books={len(books)} measured-rows-considered={rows} "
        f"books-with-matching-measurement={len(measured_books)} "
        f"unmeasured={len(missing)} installed-only={len(installed_only)}; "
        "fastest passed attempt per book/host/toolchain (load only adds time), "
        "current include closure",
        "scope: archived and local measured attempts; elapsed time is per ACL2 "
        "process, never inferred from installed certificates; failed attempts "
        "retain their verdict",
    ]
    if toolchain:
        lines.append(f"filter: toolchain={toolchain}")
    if host:
        lines.append(f"filter: host={host}")
    groups: dict[tuple[str, str, str], list[Measurement]] = {}
    for record in selected.values():
        groups.setdefault((record.host, record.toolchain, record.band),
                          []).append(record)
    slow_count = 0
    recorded: list[str] = []
    for (machine, identity, band), records in sorted(groups.items()):
        lines.append(f"origin: host={machine} toolchain={identity} jobs={band} "
                     f"matching-measured-books={len(records)}")
        for record in sorted(records, key=lambda item: (-item.seconds, item.book)):
            if record.seconds <= threshold:
                continue
            log = (root / "build/acl2" / record.run_id
                   / (record.book.replace("/", "--") + ".certify.log"))
            detail = event_detail(log)
            if band == WIDE:
                recorded.append(
                    f"RECORDED {record.book}: process-wall={record.seconds:.3f}s "
                    f"> {threshold:g}s recorded at {record.jobs} jobs "
                    f"(D26: above {RATCHET_JOBS}, does not ratchet) host={machine} "
                    f"verdict={record.verdict} run={record.run_id}{detail}")
                continue
            slow_count += 1
            lines.append(f"WARNING {record.book}: process-wall={record.seconds:.3f}s "
                         f"> {threshold:g}s jobs={record.jobs or 'unknown'} "
                         f"steps={'unknown' if record.steps is None else f'{record.steps:,}'} "
                         f"{load_words(record.load, record.cpus)} "
                         f"verdict={record.verdict} run={record.run_id}{detail}")
    if not slow_count:
        lines.append(f"No matching measured attempt exceeds {threshold:g}s.")
    lines.extend(recorded)
    unknown_runs = sorted({record.run_id for record in selected.values()
                           if record.band == UNKNOWN})
    if unknown_runs:
        lines.append(f"WARNING jobs unknown: {len(unknown_runs)} manifest(s) without "
                     f"jobs_effective supply current measurements the ratchet skips: "
                     + ", ".join(unknown_runs))
    if missing:
        examples = ", ".join(sorted(missing)[:8])
        lines.append(f"WARNING unmeasured: {len(missing)} current books have no "
                     f"matching timed attempt; installed-only={len(installed_only)}; "
                     f"examples={examples}")
    return lines


def decisive(selected: dict[tuple[str, str, str, str], Measurement]
             ) -> tuple[dict[str, Measurement], dict[str, Measurement]]:
    """Each book's D26 measurement, and the books whose every attempt failed.

    Only runs at RATCHET_JOBS jobs or fewer count (D26); wide and unknown
    measurements are reported by history_report and never ratchet. The D26
    measurement is the fastest passed one over every host and toolchain:
    load only adds seconds, so the lowest is the least-disturbed figure for
    the same bytes. Its steps are the largest any passed attempt counted
    (equal for one toolchain; the higher where toolchains differ).
    """
    best: dict[str, Measurement] = {}
    steps: dict[str, int] = {}
    failed: dict[str, Measurement] = {}
    for record in selected.values():
        if record.band != SCOPED:
            continue
        if not record.passed:
            prior = failed.get(record.book)
            if prior is None or record.run_id > prior.run_id:
                failed[record.book] = record
            continue
        if record.steps is not None:
            steps[record.book] = max(steps.get(record.book, 0), record.steps)
        prior = best.get(record.book)
        if prior is None or record.seconds < prior.seconds:
            best[record.book] = record
    for book, record in best.items():
        if book in steps and record.steps != steps[book]:
            best[book] = replace(record, steps=steps[book])
    return best, {book: record for book, record in failed.items() if book not in best}


def worst(selected: dict[tuple[str, str, str, str], Measurement]
          ) -> dict[str, Measurement]:
    """Compatibility name: the D26 measurement per book (see `decisive`)."""
    return decisive(selected)[0]


def conclusive_over(record: Measurement, line: float) -> bool:
    """Whether `record` shows its book over `line` whatever the box was doing."""
    return record.seconds > line and (record.quiet is True
                                      or record.seconds > line * LOAD_FACTOR)


def load_baseline(path: Path) -> dict[str, dict]:
    if not path.is_file():
        return {}
    value = json.loads(path.read_text(encoding="utf-8"))
    books = value.get("books") if isinstance(value, dict) else None
    if not isinstance(books, dict) or not all(
            isinstance(entry, dict)
            and isinstance(entry.get("seconds"), (int, float))
            and not isinstance(entry.get("seconds"), bool)
            and (entry.get("steps") is None
                 or (isinstance(entry.get("steps"), int)
                     and not isinstance(entry.get("steps"), bool)))
            for entry in books.values()):
        raise ValueError(f"{path}: expected {{\"books\": {{book: "
                         f"{{\"seconds\": n, \"steps\": n, ...}}}}}}")
    return books


@dataclass
class Ratchet:
    failing: list[str]
    improved: list[str]
    kept: list[str]
    proposed: dict[str, dict]
    failed: list[str] = field(default_factory=list)
    unquiet: list[str] = field(default_factory=list)


def entry(record: Measurement) -> dict:
    value = {"seconds": round(record.seconds, 3), "run": record.run_id,
             "host": record.host, "jobs": record.jobs, "verdict": record.verdict}
    if record.steps is not None:
        value["steps"] = record.steps
    if record.load is not None:
        value["load"] = record.load
    if record.cpus is not None:
        value["cpus"] = record.cpus
    return value


def lowered(prior: dict, record: Measurement) -> dict:
    """The row after a measurement that raised nothing: each number the lower."""
    value = dict(prior)
    if record.seconds < float(prior["seconds"]):
        value.update(entry(record))
        value.pop("steps", None)
    if record.steps is not None and (prior.get("steps") is None
                                     or record.steps <= prior["steps"]):
        value["steps"] = record.steps
    elif prior.get("steps") is not None:
        value["steps"] = prior["steps"]
    return value


def ratchet(selected: dict[tuple[str, str, str, str], Measurement], books: set[str],
            baseline: dict[str, dict], threshold: float,
            tolerance: float = TOLERANCE,
            step_tolerance: float = STEP_TOLERANCE) -> Ratchet:
    """Compare each book's D26 measurement and steps with the baseline.

    `proposed` is the baseline `--write-baseline` would write without
    `--allow-regression`: improved books dropped, numbers lowered to the
    current measurement, never raised, nothing added.
    """
    best, failed_only = decisive(selected)
    result = Ratchet([], [], [], {})
    remeasure = (f"re-measure quietly: python3 tools/farm.py submit <box> --jobs 2 "
                 f"<book> while the box's load stays under {QUIET_LOAD_FRACTION:.0%} "
                 "of its CPUs")
    for book, record in sorted(best.items()):
        prior = baseline.get(book)
        if record.seconds <= threshold:
            if prior is not None:
                result.improved.append(
                    f"IMPROVED {book}: best={record.seconds:.3f}s <= {threshold:g}s "
                    f"(baseline {float(prior['seconds']):.3f}s) {record.words()}; "
                    "improved; remove from baseline")
            continue
        if prior is None:
            if record.seconds <= threshold * (1 + NEAR_BAND):
                # D30 (2026-09-25): ten to eleven seconds is a warning band.
                result.kept.append(
                    f"NEAR {book}: best={record.seconds:.3f}s is within "
                    f"{NEAR_BAND:.0%} above {threshold:g}s {record.words()}; "
                    "re-measure under matched load")
            elif conclusive_over(record, threshold * (1 + NEAR_BAND)):
                result.failing.append(
                    f"FAIL {book}: best={record.seconds:.3f}s > {threshold:g}s "
                    f"{record.words()}; not in baseline")
            else:
                result.unquiet.append(
                    f"UNQUIET {book}: best={record.seconds:.3f}s > {threshold:g}s "
                    f"only in measurements not known to be quiet {record.words()}; "
                    f"not a verdict; {remeasure}")
            continue
        prior_steps = prior.get("steps")
        if prior_steps is not None and record.steps is not None:
            limit = prior_steps * (1 + step_tolerance)
            if record.steps > limit:
                result.failing.append(
                    f"FAIL {book}: steps={record.steps:,} > baseline {prior_steps:,} "
                    f"+{step_tolerance:.0%} = {limit:,.0f} (best={record.seconds:.3f}s) "
                    f"{record.words()} (baseline run={prior.get('run', 'unknown')})")
                result.proposed[book] = dict(prior)
            elif record.steps > prior_steps:
                result.kept.append(
                    f"KEPT {book}: steps={record.steps:,} is within "
                    f"{step_tolerance:.0%} of baseline {prior_steps:,}; baseline not raised")
                result.proposed[book] = dict(prior)
            else:
                result.proposed[book] = lowered(prior, record)
            continue
        # A row or a measurement without steps: the seconds ratchet, quiet rule.
        limit = float(prior["seconds"]) * (1 + tolerance)
        if record.seconds > limit and conclusive_over(record, limit):
            result.failing.append(
                f"FAIL {book}: best={record.seconds:.3f}s > baseline "
                f"{float(prior['seconds']):.3f}s +{tolerance:.0%} = {limit:.3f}s "
                f"{record.words()} (baseline run={prior.get('run', 'unknown')}; "
                "no step count on both sides)")
            result.proposed[book] = dict(prior)
        elif record.seconds > limit:
            result.unquiet.append(
                f"UNQUIET {book}: best={record.seconds:.3f}s > baseline "
                f"{float(prior['seconds']):.3f}s +{tolerance:.0%} only in measurements "
                f"not known to be quiet {record.words()}; not a verdict; {remeasure}")
            result.proposed[book] = dict(prior)
        elif record.seconds > float(prior["seconds"]):
            result.kept.append(f"KEPT {book}: best={record.seconds:.3f}s is within "
                               f"{tolerance:.0%} of baseline {float(prior['seconds']):.3f}s; "
                               "baseline not raised")
            value = dict(prior)
            if record.steps is not None and prior_steps is None:
                value["steps"] = record.steps
            result.proposed[book] = value
        else:
            result.proposed[book] = lowered(prior, record)
    for book, record in sorted(failed_only.items()):
        prior = baseline.get(book)
        result.failed.append(
            f"FAILED {book}: every matching attempt at <= {RATCHET_JOBS} jobs failed "
            f"(newest {record.seconds:.3f}s, run={record.run_id} host={record.host}); "
            "a failed certification measures no cost"
            + ("; baseline row kept" if prior is not None else ""))
        if prior is not None:
            result.proposed[book] = dict(prior)
    for book, prior in sorted(baseline.items()):
        if book in best or book in failed_only:
            continue
        if book not in books:
            result.improved.append(f"IMPROVED {book}: no longer a current root-closure "
                                   "book; improved; remove from baseline")
        else:
            # Unmeasured at the current closure: no number to compare, keep it.
            result.proposed[book] = dict(prior)
    return result


def regression_baseline(selected: dict[tuple[str, str, str, str], Measurement],
                        threshold: float) -> dict[str, dict]:
    """Rows for every book conclusively over the threshold (never UNQUIET)."""
    return {book: entry(record)
            for book, record in sorted(decisive(selected)[0].items())
            if conclusive_over(record, threshold)}


def write_baseline(path: Path, entries: dict[str, dict], threshold: float) -> None:
    value = {
        "about": ("Books over the ten-second rule (D26): each row's prover "
                  "steps (the ratchet) and its fastest passed measurement at "
                  f"{RATCHET_JOBS} jobs or fewer over all hosts and toolchains, "
                  "with the load it was taken under. Generated by "
                  "python3 tools/proof_cost.py --write-baseline; only shrinks "
                  "without --allow-regression. See docs/proofs.md."),
        "threshold_seconds": threshold,
        "tolerance": TOLERANCE,
        "step_tolerance": STEP_TOLERANCE,
        "quiet_load_fraction": QUIET_LOAD_FRACTION,
        "load_factor": LOAD_FACTOR,
        "max_jobs": RATCHET_JOBS,
        "books": dict(sorted(entries.items())),
    }
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--manifest", type=Path, help="one certification manifest")
    parser.add_argument("--toolchain", help="exact toolchain identity filter for history mode")
    parser.add_argument("--host", help="host filter for history mode")
    parser.add_argument("--threshold", type=float, default=10.0,
                        help="warn above this per-book process wall, seconds")
    parser.add_argument("--baseline", type=Path, default=BASELINE,
                        help="ratchet baseline (default planning/proof-cost-baseline.json)")
    parser.add_argument("--write-baseline", action="store_true",
                        help="rewrite the baseline: drop improved books, lower numbers; "
                             "refuses to add or raise without --allow-regression")
    parser.add_argument("--allow-regression", action="store_true",
                        help="with --write-baseline: record every current book over the "
                             "threshold at its current worst measurement")
    args = parser.parse_args(argv)
    if args.threshold < 0:
        parser.error("--threshold must be nonnegative")
    if args.allow_regression and not args.write_baseline:
        parser.error("--allow-regression applies only with --write-baseline")
    if args.write_baseline and (args.manifest or args.toolchain or args.host):
        parser.error("--write-baseline reads the whole unfiltered history")
    try:
        if args.manifest:
            if args.toolchain or args.host:
                parser.error("--host/--toolchain apply only to history mode")
            print("\n".join(report(args.manifest, args.threshold)))
            return 0
        books = current_books(ROOT)
        computed = history(ROOT, books, toolchain=args.toolchain, host=args.host)
        lines = history_report(ROOT, args.threshold, toolchain=args.toolchain,
                               host=args.host, books=books, computed=computed)
        print("\n".join(lines))
        if args.toolchain or args.host:
            print("ratchet: not applied to a filtered view")
            return 0
        baseline = load_baseline(args.baseline)
        verdict = ratchet(computed[0], books, baseline, args.threshold)
        unmeasured = len(books - {record.book for record in computed[0].values()})
        for line in (verdict.kept + verdict.unquiet + verdict.improved
                     + verdict.failed + verdict.failing):
            print(line)
        if args.write_baseline:
            if args.allow_regression:
                # Every measured book over the threshold, plus the prior
                # entries the ratchet would keep (unmeasured at the current
                # closure): an allowance adds, it never forgets a defect.
                entries = dict(verdict.proposed)
                entries.update(regression_baseline(computed[0], args.threshold))
            elif verdict.failing:
                print(f"proof_cost: refusing to write {args.baseline}: "
                      f"{len(verdict.failing)} book(s) above would be added or "
                      "raised; rerun with --allow-regression to record them")
                return 1
            else:
                entries = verdict.proposed
            write_baseline(args.baseline, entries, args.threshold)
            print(f"proof_cost: wrote {args.baseline} with {len(entries)} book(s) "
                  f"(was {len(baseline)})")
            return 0
        print(f"ratchet: scope=runs at <= {RATCHET_JOBS} jobs (D26); "
              f"baseline={len(baseline)} books; failing={len(verdict.failing)}; "
              f"improved={len(verdict.improved)}; within-tolerance={len(verdict.kept)}; "
              f"unquiet={len(verdict.unquiet)} (warning only); "
              f"failed-attempts={len(verdict.failed)} (no cost; green_check owns red); "
              f"unmeasured={unmeasured} (warning only); step-tolerance="
              f"{STEP_TOLERANCE:.0%}; seconds-tolerance={TOLERANCE:.0%} (rows without steps)")
        return 1 if verdict.failing else 0
    except (OSError, ValueError, KeyError, certs.UnreadableBook) as error:
        print(f"proof_cost: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
