#!/usr/bin/env python3
"""Report certification wall cost from one manifest and its existing ACL2 logs.

This is a read-only diagnostic, not a certification or cache-validity check.
Installed books have no proof work in this run; missing per-event logs are
reported as unavailable rather than inferred from another source.
"""

from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
SUMMARY = re.compile(r"(?m)^Summary\s*$")
FORM = re.compile(r"(?m)^Form:\s*(.*)$")
TIME = re.compile(r"(?m)^Time:\s*([0-9]+(?:\.[0-9]+)?) seconds")
WRAPPER = re.compile(r"^\(\s*(?:ENCAPSULATE|PROGN|MAKE-EVENT)\b", re.I)


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


def source_scope(manifest: dict) -> str:
    named_tree = manifest.get("tree")
    tree = Path(named_tree) if named_tree else None
    sources = manifest.get("source_digests_sha256") or {}
    if tree is None or not tree.is_dir() or not isinstance(sources, dict) or not sources:
        return "source-closure=current-bytes unavailable"
    stale = 0
    for relative, expected in sources.items():
        path = tree / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            stale += 1
    return (f"source-closure={'stale' if stale else 'matches'} "
            f"({stale} of {len(sources)} source digests differ; manifest scope only)")


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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, help="one certification manifest")
    parser.add_argument("--threshold", type=float, default=10.0,
                        help="warn above this per-book process wall, seconds")
    args = parser.parse_args(argv)
    if args.threshold < 0:
        parser.error("--threshold must be nonnegative")
    path = args.manifest or latest_manifest(ROOT)
    if path is None:
        print("proof_cost: no local certification manifest; cost unavailable")
        return 0
    try:
        print("\n".join(report(path, args.threshold)))
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"proof_cost: {error}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
