#!/usr/bin/env python3
"""Report measured ACL2 book cost at the current source and include closure.

This is not a certification or cache-validity check. The default scans
archived and local manifests, retaining the newest matching measurement for
each book, host and toolchain. An installed certificate has no proof time in
that run. `--manifest` keeps the one-run diagnostic and never fails.

The ten-second rule is a ratchet. planning/proof-cost-baseline.json lists every
book whose worst current measurement (over all hosts and toolchains) was above
the threshold when the baseline was written, with that seconds figure, run id
and host. The unfiltered history mode (what `make check` runs) exits 1 when a
measured book is over the threshold and is absent from the baseline, or is
more than 25% over its baseline seconds. A baseline book now under the
threshold is reported "improved; remove from baseline". Unmeasured books stay
warnings. `--write-baseline` rewrites the file from the current measurements:
it drops improved books and lowers numbers, never raises a number, and refuses
to write at all when a book would be added or would exceed its tolerance,
unless `--allow-regression` is given. The baseline only shrinks.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "proof-cost-baseline.json"
TOLERANCE = 0.25
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import green_check  # noqa: E402
import ledger  # noqa: E402

SUMMARY = re.compile(r"(?m)^Summary\s*$")
FORM = re.compile(r"(?m)^Form:\s*(.*)$")
TIME = re.compile(r"(?m)^Time:\s*([0-9]+(?:\.[0-9]+)?) seconds")
WRAPPER = re.compile(r"^\(\s*(?:ENCAPSULATE|PROGN|MAKE-EVENT|CERTIFY-BOOK)\b", re.I)


def latest_manifest(root: Path) -> Path | None:
    candidates = (root / "build" / "acl2").glob("certify-*/manifest.json")
    return max(candidates, key=lambda path: path.stat().st_mtime, default=None)


def slowest_event(log: Path) -> tuple[str, float] | None:
    if not log.is_file():
        return None
    source = log.read_text(encoding="utf-8", errors="replace")
    best: tuple[str, float] | None = None
    starts = [match.start() for match in SUMMARY.finditer(source)]
    for first, last in zip(starts, starts[1:] + [len(source)]):
        block = source[first:last]
        form, duration = FORM.search(block), TIME.search(block)
        if form is None or duration is None:
            continue
        name = form.group(1).strip()
        if WRAPPER.match(name):
            continue
        seconds = float(duration.group(1))
        if best is None or seconds > best[1]:
            best = name, seconds
    return best


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
        f"scope: installed={len(installed)} certified-attempted={len(results)} "
        f"measured-books={len(measured)}",
        f"wall: total={elapsed_seconds(manifest)}; "
        f"certification={manifest.get('certify_wall_seconds', 'unavailable')}s; "
        f"sum-of-book-process-walls={sum(measured.values()):.3f}s; "
        f"sum-of-slot-waits={wait_total:.3f}s; CPU=unavailable",
    ]
    for book, seconds in sorted(measured.items(), key=lambda item: (-item[1], item[0])):
        if seconds <= threshold:
            continue
        event = slowest_event(path.parent / (book.replace("/", "--") + ".certify.log"))
        detail = f"; slowest-event={event[0]} {event[1]:.2f}s" if event else "; per-event=unavailable"
        lines.append(f"WARNING {book}: process-wall={seconds:.3f}s > {threshold:g}s"
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


def current_books(root: Path) -> set[str]:
    """The current Makefile-root closure, even before the ledger is rewritten."""
    books: set[str] = set()
    for name in ledger.makefile_roots():
        books.update(certs.closure(root, name))
    return books


def history(root: Path, books: set[str], *, toolchain: str | None = None,
            host: str | None = None,
            runs: list[tuple[green_check.Run, dict]] | None = None
            ) -> tuple[dict[tuple[str, str, str], Measurement], set[str], int]:
    """Select timed attempts; certs owns current closure hashing/comparison.

    `book_wall_seconds` names work attempted in that run. An installed-only
    row never replaces an earlier measured attempt, and a failed attempt
    retains its failed verdict. Shared dependency bytes are memoized by
    certs.book_facts, and each requested book's closure is built only once.
    """
    runs = green_check.manifests(root) if runs is None else runs
    closures: dict[str, list[str] | None] = {}
    selected: dict[tuple[str, str, str], Measurement] = {}
    installed_current: set[str] = set()
    measured_rows = 0

    def listing(book: str) -> list[str] | None:
        if book not in closures:
            try:
                closures[book] = certs.closure_listing(certs.closure(root, book))
            except (certs.UnreadableBook, OSError):
                closures[book] = None
        return closures[book]

    def matches(book: str, manifest: dict) -> bool:
        if book not in books:
            return False
        key = listing(book)
        sources = manifest.get("source_digests_sha256") or {}
        after = manifest.get("source_digests_sha256_after") or {}
        return (key is not None and isinstance(sources, dict)
                and not certs.closure_drift(key, sources)
                and (not after or (isinstance(after, dict)
                                   and not certs.closure_drift(key, after))))

    for run, manifest in runs:
        identity = str(manifest.get("acl2_toolchain_identity") or "unknown")
        machine = run.where
        if (toolchain is not None and identity != toolchain
                or host is not None and machine != host):
            continue
        walls = manifest.get("book_wall_seconds") or {}
        results = manifest.get("book_results") or {}
        installed = manifest.get("installed_books") or {}
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
            key = (book, machine, identity)
            # green_check.manifests is ordered by run-id timestamp; a newer
            # partial run only replaces the books it actually measured.
            selected[key] = Measurement(
                book, float(seconds), str(results.get(book, "unknown")),
                run.run_id, machine, identity)
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
        "newest per book/host/toolchain, current include closure",
        "scope: archived and local measured attempts; elapsed time is per ACL2 "
        "process, never inferred from installed certificates; failed attempts "
        "retain their verdict",
    ]
    if toolchain:
        lines.append(f"filter: toolchain={toolchain}")
    if host:
        lines.append(f"filter: host={host}")
    groups: dict[tuple[str, str], list[Measurement]] = {}
    for record in selected.values():
        groups.setdefault((record.host, record.toolchain), []).append(record)
    slow_count = 0
    for (machine, identity), records in sorted(groups.items()):
        lines.append(f"origin: host={machine} toolchain={identity} "
                     f"matching-measured-books={len(records)}")
        for record in sorted(records, key=lambda item: (-item.seconds, item.book)):
            if record.seconds <= threshold:
                continue
            slow_count += 1
            log = (root / "build/acl2" / record.run_id
                   / (record.book.replace("/", "--") + ".certify.log"))
            event = slowest_event(log)
            detail = (f"; slowest-event={event[0]} {event[1]:.2f}s"
                      if event else "; per-event=unavailable")
            lines.append(f"WARNING {record.book}: process-wall={record.seconds:.3f}s "
                         f"> {threshold:g}s verdict={record.verdict} "
                         f"run={record.run_id}{detail}")
    if not slow_count:
        lines.append(f"No matching measured attempt exceeds {threshold:g}s.")
    if missing:
        examples = ", ".join(sorted(missing)[:8])
        lines.append(f"WARNING unmeasured: {len(missing)} current books have no "
                     f"matching timed attempt; installed-only={len(installed_only)}; "
                     f"examples={examples}")
    return lines


def worst(selected: dict[tuple[str, str, str], Measurement]
          ) -> dict[str, Measurement]:
    """Each book's slowest current measurement over every host and toolchain."""
    found: dict[str, Measurement] = {}
    for record in selected.values():
        prior = found.get(record.book)
        if prior is None or record.seconds > prior.seconds:
            found[record.book] = record
    return found


def load_baseline(path: Path) -> dict[str, dict]:
    if not path.is_file():
        return {}
    value = json.loads(path.read_text(encoding="utf-8"))
    books = value.get("books") if isinstance(value, dict) else None
    if not isinstance(books, dict) or not all(
            isinstance(entry, dict)
            and isinstance(entry.get("seconds"), (int, float))
            and not isinstance(entry.get("seconds"), bool)
            for entry in books.values()):
        raise ValueError(f"{path}: expected {{\"books\": {{book: {{\"seconds\": n, ...}}}}}}")
    return books


@dataclass
class Ratchet:
    failing: list[str]
    improved: list[str]
    kept: list[str]
    proposed: dict[str, dict]


def ratchet(selected: dict[tuple[str, str, str], Measurement], books: set[str],
            baseline: dict[str, dict], threshold: float,
            tolerance: float = TOLERANCE) -> Ratchet:
    """Compare each book's worst current measurement with the baseline.

    `proposed` is the baseline `--write-baseline` would write without
    `--allow-regression`: improved books dropped, numbers lowered to the
    current measurement, never raised, nothing added.
    """
    slowest = worst(selected)
    failing: list[str] = []
    improved: list[str] = []
    kept: list[str] = []
    proposed: dict[str, dict] = {}
    for book, record in sorted(slowest.items()):
        entry = {"seconds": round(record.seconds, 3), "run": record.run_id,
                 "host": record.host, "verdict": record.verdict}
        prior = baseline.get(book)
        if record.seconds <= threshold:
            if prior is not None:
                improved.append(
                    f"IMPROVED {book}: worst={record.seconds:.3f}s <= {threshold:g}s "
                    f"(baseline {float(prior['seconds']):.3f}s) host={record.host} "
                    f"run={record.run_id}; improved; remove from baseline")
            continue
        if prior is None:
            failing.append(
                f"FAIL {book}: worst={record.seconds:.3f}s > {threshold:g}s "
                f"host={record.host} run={record.run_id}; not in baseline")
            continue
        limit = float(prior["seconds"]) * (1 + tolerance)
        if record.seconds > limit:
            failing.append(
                f"FAIL {book}: worst={record.seconds:.3f}s > baseline "
                f"{float(prior['seconds']):.3f}s +{tolerance:.0%} = {limit:.3f}s "
                f"host={record.host} run={record.run_id} "
                f"(baseline run={prior.get('run', 'unknown')})")
            proposed[book] = dict(prior)
        elif record.seconds > float(prior["seconds"]):
            kept.append(f"KEPT {book}: worst={record.seconds:.3f}s is within "
                        f"{tolerance:.0%} of baseline {float(prior['seconds']):.3f}s; "
                        "baseline not raised")
            proposed[book] = dict(prior)
        else:
            proposed[book] = entry
    for book, prior in sorted(baseline.items()):
        if book in slowest:
            continue
        if book not in books:
            improved.append(f"IMPROVED {book}: no longer a current root-closure book; "
                            "improved; remove from baseline")
        else:
            # Unmeasured at the current closure: no number to compare, keep it.
            proposed[book] = dict(prior)
    return Ratchet(failing, improved, kept, proposed)


def regression_baseline(selected: dict[tuple[str, str, str], Measurement],
                        threshold: float) -> dict[str, dict]:
    return {book: {"seconds": round(record.seconds, 3), "run": record.run_id,
                   "host": record.host, "verdict": record.verdict}
            for book, record in sorted(worst(selected).items())
            if record.seconds > threshold}


def write_baseline(path: Path, entries: dict[str, dict], threshold: float) -> None:
    value = {
        "about": ("Books over the ten-second rule, with their worst current "
                  "measurement over all hosts and toolchains. Generated by "
                  "python3 tools/proof_cost.py --write-baseline; only shrinks "
                  "without --allow-regression. See docs/proofs.md."),
        "threshold_seconds": threshold,
        "tolerance": TOLERANCE,
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
        for line in verdict.kept + verdict.improved + verdict.failing:
            print(line)
        if args.write_baseline:
            if args.allow_regression:
                entries = regression_baseline(computed[0], args.threshold)
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
        print(f"ratchet: baseline={len(baseline)} books; failing={len(verdict.failing)}; "
              f"improved={len(verdict.improved)}; within-tolerance={len(verdict.kept)}; "
              f"unmeasured={unmeasured} (warning only); tolerance={TOLERANCE:.0%}")
        return 1 if verdict.failing else 0
    except (OSError, ValueError, KeyError, certs.UnreadableBook) as error:
        print(f"proof_cost: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
