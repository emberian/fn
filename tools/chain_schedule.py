#!/usr/bin/env python3
"""The chain-first plan for a certification run: its longest include chain,
and how many ACL2 processes to run so that chain finishes soonest.

    python3 tools/chain_schedule.py fit      # refit the slowdown curves from
                                             # planning/evidence/manifests

`tools/shape_books.py --critical` / `--chain BOOK` print the chain;
`tools/certify_books.py --jobs auto` (the farm's default) plans with this.

WHY.  The architect's measurements (planning/architecture-recommendation-
2026-09-28.md, section 4.2): a recertification's wall time is its longest
include chain, not its summed work over the core count.  Three runs: 509 s
wall against a 466 s chain (persvati, 20 jobs), 656 s against 642 s (hbox,
14 jobs), 385 s against 384 s (persvati, 20 jobs).  And every ACL2 on the box
slows every other: the same book at 20 jobs took 2.4 to 4.4 times its quiet
time (section 5.3), so the chain itself runs at that slowed rate.  Starting
the longest remaining chain first (`bottom_levels`, the classic critical-path
list schedule; the runner has done that since 2026-09-22) is half of it; the
other half is running as many ACL2s as shorten the run and no more.

THE CURVE.  A book's wall grows with the box's load per core L (runnable
processes over logical CPUs) as `s(L) = 1 + slope * max(0, L - knee)`,
fitted per box by `fit` below from every archived manifest's
`book_wall_seconds` and `book_load_average` (the one-minute load when each
book started and ended), each book against its own median at a quiet load.
Both boxes have 24 logical CPUs on 12 (persvati) or 16 (hbox, 8 of them
efficiency cores) physical cores, so contention starts well below 24 jobs.

THE PLAN.  Each book's predicted quiet time is its most recent archived wall
divided by s(L) at the load it ran under (a book with no measurement counts
the median of those that have one).  For each job count j up to the ceiling
the plan simulates the runner's own list schedule on those times scaled by
s((j + background) / cpus), background being the box's load before the run,
and picks the fewest jobs within `TOLERANCE` of the best predicted wall:
fewer ACL2s cost nothing on the chain and leave the box to the next lane.
The prediction is an estimate for ordering and sizing; nothing about a
verdict comes from it, and a wrong one only costs time.
"""
from __future__ import annotations

import argparse
import collections
import dataclasses
import heapq
import json
import math
import os
from pathlib import Path
import socket
import statistics
import sys
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
HISTORY = ROOT / "planning" / "evidence" / "manifests"

# (knee, slope) of s(L) per box, from `python3 tools/chain_schedule.py fit`
# on 2026-09-28 over planning/evidence/manifests at 48a736d5e: persvati
# 42,222 book runs of 1,416 books (reference: each book's median below
# load/core 0.25), mean |log error| 0.22; hbox 10,555 runs of 450 books
# (reference below 0.35: hbox has too few quieter runs), 0.32.  Bucket
# medians behind them: persvati s = 1.03 at L 0.2, 1.84 at 0.5, 2.75 at 1.0;
# hbox 1.00 at 0.3, 1.62 at 0.5, 2.10 at 1.0, about 3 from 1.4 on.
CURVES: dict[str, tuple[float, float]] = {
    "persvati": (0.14, 2.2),
    "hbox": (0.30, 1.7),
}
# An unfitted box gets the steeper curve: it errs toward fewer jobs.
DEFAULT_CURVE = (0.14, 2.2)
# Pick the fewest jobs whose predicted wall is within this of the best.
TOLERANCE = 0.03
# `--jobs auto` never runs more than this many ACL2s (and never more than
# the box's CPUs or ACL2 slots); `--jobs auto:N` sets another ceiling.
DEFAULT_CEILING = 16
# A book's prediction is the median of its last this-many measurements.
RECENT = 5
# A book whose wall is unknown and with no measured book to take a median
# from (a fresh history) counts this many seconds.
UNKNOWN_SECONDS = 5.0


def host_name(host: str | None = None) -> str:
    return (host or socket.gethostname()).split(".")[0]


def curve(host: str | None = None) -> tuple[float, float]:
    return CURVES.get(host_name(host), DEFAULT_CURVE)


def slowdown(load_per_core: float, host: str | None = None) -> float:
    """How many times its quiet wall a book takes at this load per core."""
    knee, slope = curve(host)
    return 1.0 + slope * max(0.0, load_per_core - knee)


@dataclasses.dataclass(frozen=True)
class Walls:
    """Predicted quiet seconds per book, and where they came from."""
    seconds: dict[str, float]
    measured: int
    fill: float


def quiet_walls(books: Iterable[str], history: Path | None = None,
                host: str | None = None) -> Walls:
    """Each book's predicted quiet seconds on HOST (default: this box).

    A measurement is an archived wall divided by the slowdown at the load
    per core it ran under; a book's prediction is the median of its last
    `RECENT` measurements on HOST, or on any box when HOST has none (the
    laptop, a fresh box).  Archived run ids carry a UTC stamp after
    `certify-`, which orders them in time.  A missing or unreadable
    manifest is skipped.
    """
    history = HISTORY if history is None else history
    wanted = set(books)
    here = host_name(host)
    mine: dict[str, list[float]] = collections.defaultdict(list)
    anywhere: dict[str, list[float]] = collections.defaultdict(list)
    paths = sorted(history.glob("*certify-*.json"),
                   key=lambda p: p.name.split("certify-")[-1]) if history.is_dir() else []
    for path in paths:
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if not isinstance(manifest, dict) or manifest.get("pcert"):
            continue
        walls = manifest.get("book_wall_seconds") or {}
        loads = manifest.get("book_load_average") or {}
        cpus = manifest.get("cpu_count")
        box = host_name(str(manifest.get("hostname") or "unknown"))
        if not isinstance(walls, dict):
            continue
        for book, seconds in walls.items():
            if book not in wanted or not isinstance(seconds, (int, float)) or seconds < 0:
                continue
            factor = 1.0
            load = loads.get(book) if isinstance(loads, dict) else None
            if (isinstance(load, list) and len(load) == 2 and None not in load
                    and isinstance(cpus, int) and cpus > 0):
                factor = slowdown((load[0] + load[1]) / 2 / cpus, box)
            anywhere[book].append(float(seconds) / factor)
            if box == here:
                mine[book].append(float(seconds) / factor)
    measured = {book: statistics.median((mine.get(book) or runs)[-RECENT:])
                for book, runs in anywhere.items()}
    fill = statistics.median(measured.values()) if measured else UNKNOWN_SECONDS
    return Walls({book: measured.get(book, fill) for book in wanted},
                 len(measured), fill)


def topological(books: list[str], graph: dict[str, set[str]]) -> list[str]:
    """`books` with every book after its dependencies in `graph`, stable."""
    placed: set[str] = set()
    ordered: list[str] = []
    pending = list(books)
    while pending:
        ready = [book for book in pending if graph[book] <= placed]
        rest = [book for book in pending if not graph[book] <= placed]
        if not ready:
            raise ValueError("certification schedule has a cycle: " + ", ".join(rest))
        ordered.extend(ready)
        placed.update(ready)
        pending = rest
    return ordered


def dependents_of(books: list[str], graph: dict[str, set[str]]) -> dict[str, list[str]]:
    dependents: dict[str, list[str]] = {book: [] for book in books}
    for book in books:
        for dependency in graph[book]:
            dependents[dependency].append(book)
    return dependents


def bottom_levels(books: list[str], graph: dict[str, set[str]],
                  walls: dict[str, float]) -> dict[str, float]:
    """Each book's own wall plus the longest chain of dependents above it."""
    dependents = dependents_of(books, graph)
    level: dict[str, float] = {}
    for book in reversed(topological(books, graph)):
        level[book] = walls.get(book, 1.0) + max(
            (level[dependent] for dependent in dependents[book]), default=0.0)
    return level


def top_levels(books: list[str], graph: dict[str, set[str]],
               walls: dict[str, float]) -> dict[str, float]:
    """Each book's own wall plus the longest chain of dependencies below it."""
    level: dict[str, float] = {}
    for book in topological(books, graph):
        level[book] = walls.get(book, 1.0) + max(
            (level[dependency] for dependency in graph[book]), default=0.0)
    return level


def critical_chain(books: list[str], graph: dict[str, set[str]],
                   walls: dict[str, float], through: str | None = None) -> list[str]:
    """The longest weighted chain, dependencies first; through `through` if named."""
    if not books:
        return []
    below = top_levels(books, graph, walls)
    above = bottom_levels(books, graph, walls)
    dependents = dependents_of(books, graph)
    if through is None:
        through = max(books, key=lambda book: (below[book] + above[book] - walls.get(book, 1.0),
                                               -books.index(book)))
    down: list[str] = []
    book = through
    while graph[book]:
        book = max(sorted(graph[book]), key=lambda b: below[b])
        down.append(book)
    up: list[str] = []
    book = through
    while dependents[book]:
        book = max(sorted(dependents[book]), key=lambda b: above[b])
        up.append(book)
    return list(reversed(down)) + [through] + up


def simulate(books: list[str], graph: dict[str, set[str]], walls: dict[str, float],
             jobs: int, priority: dict[str, float] | None = None) -> float:
    """The wall time of `certify_books.run_schedule`'s list schedule on a
    virtual clock: whenever a slot is free, the ready book with the highest
    priority (the longest remaining chain) starts."""
    if not books:
        return 0.0
    priority = bottom_levels(books, graph, walls) if priority is None else priority
    order = {book: index for index, book in enumerate(books)}
    waiting = {book: len(graph[book]) for book in books}
    dependents = dependents_of(books, graph)
    ready = [(-priority[book], order[book], book) for book in books if not waiting[book]]
    heapq.heapify(ready)
    running: list[tuple[float, int, str]] = []
    clock = 0.0
    while ready or running:
        while ready and len(running) < jobs:
            _, index, book = heapq.heappop(ready)
            heapq.heappush(running, (clock + walls.get(book, 1.0), index, book))
        clock, _, book = heapq.heappop(running)
        for dependent in dependents[book]:
            waiting[dependent] -= 1
            if not waiting[dependent]:
                heapq.heappush(ready, (-priority[dependent], order[dependent], dependent))
    return clock


@dataclasses.dataclass(frozen=True)
class Plan:
    jobs: int
    predicted_seconds: float
    predicted_by_jobs: dict[int, float]
    background_load: float
    cpus: int
    host: str

    def record(self) -> dict[str, object]:
        return {
            "jobs_chosen": self.jobs,
            "predicted_wall_seconds": round(self.predicted_seconds, 1),
            "predicted_wall_by_jobs": {str(j): round(s, 1)
                                       for j, s in sorted(self.predicted_by_jobs.items())},
            "background_load": round(self.background_load, 2),
            "cpus": self.cpus,
            "curve": {"host": self.host, "knee": curve(self.host)[0],
                      "slope": curve(self.host)[1]},
        }


def choose_jobs(books: list[str], graph: dict[str, set[str]], walls: dict[str, float],
                ceiling: int, cpus: int | None = None, background: float = 0.0,
                host: str | None = None) -> Plan:
    """The fewest jobs, up to `ceiling`, within TOLERANCE of the best predicted wall."""
    cpus = cpus or os.cpu_count() or 1
    ceiling = max(1, min(ceiling, len(books) or 1))
    priority = bottom_levels(books, graph, walls)
    predicted: dict[int, float] = {}
    for jobs in range(1, ceiling + 1):
        factor = slowdown((jobs + background) / cpus, host)
        scaled = {book: walls.get(book, 1.0) * factor for book in books}
        predicted[jobs] = simulate(books, graph, scaled, jobs, priority)
    best = min(predicted.values())
    jobs = min(j for j, seconds in predicted.items() if seconds <= best * (1 + TOLERANCE))
    return Plan(jobs, predicted[jobs], predicted, background, cpus, host_name(host))


def parse_jobs(value: str) -> int | tuple[str, int]:
    """`--jobs N` (a fixed count) or `auto` / `auto:N` (planned, at most N)."""
    text = str(value).strip()
    if text == "auto":
        return ("auto", DEFAULT_CEILING)
    if text.startswith("auto:"):
        ceiling = int(text[5:])
        if ceiling <= 0:
            raise ValueError("auto:N needs a positive N")
        return ("auto", ceiling)
    return int(text)


def chain_lines(chain: list[str], walls: dict[str, float], factor: float = 1.0,
                width: int = 100) -> list[str]:
    """The chain top-down, `book(seconds)` joined by arrows, wrapped."""
    words = [f"{book.removeprefix('books/').removeprefix('tests/acl2/')}"
             f"({walls.get(book, 1.0) * factor:.1f})"
             for book in reversed(chain)]
    lines: list[str] = []
    line = ""
    for word in words:
        piece = word if not line else " -> " + word
        if line and len(line) + len(piece) > width:
            lines.append(line + " ->")
            line = word
        else:
            line += piece
    if line:
        lines.append(line)
    return lines


# --- fitting -----------------------------------------------------------------

def observations(history: Path) -> dict[tuple[str, str], list[tuple[float, float]]]:
    """(box, book) -> [(load per core, wall seconds)] over ordinary runs."""
    data: dict[tuple[str, str], list[tuple[float, float]]] = collections.defaultdict(list)
    for path in sorted(history.glob("*certify-*.json")):
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if not isinstance(manifest, dict) or manifest.get("pcert"):
            continue
        cpus = manifest.get("cpu_count")
        loads = manifest.get("book_load_average") or {}
        box = host_name(str(manifest.get("hostname") or "unknown"))
        if not isinstance(cpus, int) or cpus <= 0 or not isinstance(loads, dict):
            continue
        for book, seconds in (manifest.get("book_wall_seconds") or {}).items():
            load = loads.get(book)
            if (not isinstance(load, list) or len(load) != 2 or None in load
                    or not isinstance(seconds, (int, float)) or seconds < 1.0):
                continue
            data[(box, book)].append(((load[0] + load[1]) / 2 / cpus, float(seconds)))
    return data


def fit(history: Path, box: str, quiet_below: float) -> dict[str, float] | None:
    """Grid-search (knee, slope) minimising mean |log(ratio / s(L))| up to L 1.2."""
    points: list[tuple[float, float]] = []
    books = 0
    for (name, _book), runs in observations(history).items():
        if name != box:
            continue
        quiet = [seconds for load, seconds in runs if load < quiet_below]
        if len(quiet) < 2:
            continue
        books += 1
        reference = statistics.median(quiet)
        points.extend((load, seconds / reference) for load, seconds in runs if load <= 1.2)
    if not points:
        return None
    best: tuple[float, float, float] | None = None
    for knee in (k / 100 for k in range(0, 60, 2)):
        for slope in (s / 10 for s in range(2, 50)):
            error = sum(abs(math.log(ratio) - math.log(1 + slope * max(0.0, load - knee)))
                        for load, ratio in points)
            if best is None or error < best[0]:
                best = (error, knee, slope)
    assert best is not None
    return {"box": box, "runs": len(points), "books": books, "quiet_below": quiet_below,
            "knee": round(best[1], 2), "slope": round(best[2], 1),
            "mean_abs_log_error": round(best[0] / len(points), 3)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    fitting = sub.add_parser("fit", help="refit the per-box slowdown curves")
    fitting.add_argument("--history", default=str(HISTORY))
    fitting.add_argument("--box", action="append", default=[])
    fitting.add_argument("--quiet-below", type=float, action="append", default=[],
                         help="per --box: a book's reference is its median below this "
                              "load per core (default 0.25 persvati, 0.35 hbox)")
    arguments = parser.parse_args(argv)
    boxes = arguments.box or ["persvati", "hbox"]
    quiet = arguments.quiet_below or [0.35 if box == "hbox" else 0.25 for box in boxes]
    for box, below in zip(boxes, quiet):
        print(json.dumps(fit(Path(arguments.history), box, below)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
