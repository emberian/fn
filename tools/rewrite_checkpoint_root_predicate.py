#!/usr/bin/env python3
"""Move checkpoint C consumers to the single B root-provenance body."""
from __future__ import annotations
import argparse
from pathlib import Path
import lisp_rewrite as lr

OLD = "fn2-checkpoint-built-roots-p"
NEW = "fn2-checkpoint-production-roots-p"
PATHS = ("books/checkpoint-build-state.lisp", "books/checkpoint-build.lisp", "books/checkpoint-descriptor.lisp")

def rewrite(path: str, text: str) -> tuple[str, int]:
    count = 0
    if Path(path).name == "checkpoint-build-state.lisp":
        parsed = lr.parse(text)
        removed = lr.match(f"(defun {OLD} ?*body)", parsed, deep=False)
        text = lr.write(text, [(m.start, m.end, "") for m in removed])
        count += len(removed)
        parsed = lr.parse(text)
        if not lr.match('(include-book "checkpoint-production")', parsed, deep=False):
            anchor = lr.match('(include-book "checkpoint-member")', parsed, deep=False)
            if len(anchor) != 1:
                raise ValueError("state book needs its unique existing member include")
            m = anchor[0]
            text = lr.write(text, [(m.start, m.end, text[m.start:m.end] + '\n(include-book "checkpoint-production")')])
            count += 1
    parsed = lr.parse(text)
    heads = [m.node.items[0] for m in lr.match(f"({OLD} ?*args)", parsed)]
    text = lr.write(text, [(n.start, n.end, NEW) for n in heads])
    return text, count + len(heads)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", default=PATHS)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    total = 0
    for name in args.paths:
        path = Path(name)
        changed, count = rewrite(name, path.read_text())
        total += count
        if args.write and count:
            path.write_text(changed)
    print(f"checkpoint root predicate: {total} edits" + (" written" if args.write else " (dry run)"))

if __name__ == "__main__":
    main()
