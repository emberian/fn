#!/usr/bin/env python3
"""Separate checkpoint physical extent stride from journal I/O resource count.

Only named, structurally matched geometry/ownership expressions are changed.
Journal resource indices, byte-work budgets, strings and comments are preserved.
Uses the shared Lisp reader/rewriter; --write is explicit and applies only the
listed checkpoint/boot sources and their concrete geometry controls.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import lisp_rewrite as lr

DEFAULT_PATHS = (
    "books/checkpoint.lisp", "books/checkpoint-geometry.lisp", "books/boot.lisp", "books/executor.lisp",
    "tests/checkpoint-publication-unit.lisp", "tests/checkpoint-geometry-unit.lisp",
)


def rewrite(path: str, text: str) -> tuple[str, int]:
    parsed = lr.parse(text)
    edits: list[tuple[int, int, str]] = []

    def replace(pattern: str, item: int, value: str) -> None:
        for match in lr.match(pattern, parsed):
            node = match.node.items[item]
            edits.append((node.start, node.end, value))

    name = Path(path).name
    if name == "checkpoint.lisp":
        replace("(floor ?unit 3)", 2, "*fn2-storage-extent-units*")
    elif name == "checkpoint-geometry.lisp":
        replace("(defconst *fn2-checkpoint-unit-bytes* 4096)", 2, "*fn2-format-sector-size*")
        replace("(* 3 extents)", 1, "*fn2-storage-extent-units*")
        replace("(* 12288 extents)", 1, "*fn2-storage-extent-bytes*")
        replace("(+ 4096 ?offset)", 1, "*fn2-checkpoint-unit-bytes*")
        replace("(- size 8192)", 2, "(* 2 *fn2-checkpoint-unit-bytes*)")
    elif name == "boot.lisp":
        replace("(fn2-fields-set-value (+ 256 *fn2-format-bootstrap-field-sector-size*) 4096 fn2-fields)", 2,
                "*fn2-format-sector-size*")
        replace("(*fn2-checkpoint-geometry-record-field-sector-bytes* 4096)", 1, "*fn2-format-sector-size*")
        replace("(floor size 4096)", 2, "*fn2-format-sector-size*")
        replace("(fn2-fields-set-value (+ 256 *fn2-format-bootstrap-field-page-size*) 4096 fn2-fields)", 2,
                "*fn2-format-page-size*")
        replace("(*fn2-checkpoint-geometry-record-field-page-bytes* 4096)", 1, "*fn2-format-page-size*")
        replace("(*fn2-checkpoint-geometry-record-field-extent-units* 3)", 1, "*fn2-storage-extent-units*")
    elif name == "executor.lisp":
        replace("(* 12288 ?extents)", 1, "*fn2-storage-extent-bytes*")
        replace("(/ base 12288)", 0, "floor")
        replace("(/ base 12288)", 2, "*fn2-storage-extent-bytes*")
    elif name == "checkpoint-publication-unit.lisp":
        replace("(equal (fn2-checkpoint-bootstrap-unit 1 1) 5)", 2, "18")
        replace("(equal (fn2-checkpoint-anchor-unit 0 1 1) 6)", 2, "19")
        replace("(equal (fn2-checkpoint-anchor-unit 3 1 1) 9)", 2, "22")
        # Only the named positive conjunction changes. A new standalone old-
        # geometry refusal control must remain byte-identical on repeated runs.
        for match in lr.match("(and (fn2-checkpoint-image-sizep (* 4096 12) 1 1) ?*rest)", parsed):
            node = match.node.items[1].items[1].items[2]
            edits.append((node.start, node.end, "25"))
    elif name == "checkpoint-geometry-unit.lisp":
        for match in lr.match("(fn2-boot-geometry-fields (* 4096 12) 1 1 fn2-fields)", parsed):
            node = match.node.items[1].items[2]
            edits.append((node.start, node.end, "25"))
    return lr.write(text, edits), len(edits)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("paths", nargs="*", default=DEFAULT_PATHS)
    args = parser.parse_args()
    total = 0
    for name in args.paths:
        path = Path(name)
        before = path.read_text()
        after, count = rewrite(str(path), before)
        if args.write and count:
            path.write_text(after)
        print(f"{name}: {count} structural edits")
        total += count
    print(f"total: {total} structural edits" + (" applied" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
