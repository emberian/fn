#!/usr/bin/env python3
"""Repair the known cold-evidence declaration class using lisp_rewrite.

Each named phase retains boot's already-owned root/rx storage windows: BEGIN
checks both workspaces, later operations bind their exact owner/generations;
reset/copy/check/decode/advance do not release them. This classification is
explicit, not inferred for arbitrary future phases. Unknown evidence phases,
conflicting ownership or absent actual operation bodies are refused.
No Lisp evaluation, macroexpansion or admission is performed.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from pathlib import Path
import lisp_rewrite as lr

EVIDENCE_OPERATIONS = {
    ":checkpoint-evidence-begin": "fn2-boot-checkpoint-evidence-begin",
    ":checkpoint-evidence-target": "fn2-boot-checkpoint-evidence-target",
    ":checkpoint-evidence-load": "fn2-boot-checkpoint-evidence-sector",
    ":checkpoint-evidence-copy": "fn2-boot-checkpoint-evidence-copy",
    ":checkpoint-evidence-check": "fn2-boot-checkpoint-evidence-check",
    ":checkpoint-evidence-record": "fn2-boot-checkpoint-evidence-record",
    ":checkpoint-evidence-next": "fn2-boot-checkpoint-evidence-next",
}


def symbol(node: object) -> str:
    if not isinstance(node, lr.Atom) or isinstance(node, lr.Str):
        raise ValueError("expected a literal declaration symbol")
    return node.text.lower()


def value(form: lr.Lst, key: str) -> lr.Lst:
    found = [form.items[i + 1] for i, node in enumerate(form.items[:-1])
             if isinstance(node, lr.Atom) and not isinstance(node, lr.Str)
             and node.text.lower() == key]
    if len(found) != 1 or not isinstance(found[0], lr.Lst):
        raise ValueError(f"expected exactly one literal {key} list")
    return found[0]


def one(pattern: str, source: str) -> lr.Lst:
    found = list(lr.match(pattern, lr.parse(source), deep=False))
    if len(found) != 1:
        raise ValueError(f"expected one actual {pattern} declaration")
    return found[0].node


def rows(node: lr.Lst) -> dict[str, lr.Lst]:
    result = {}
    for row in node.items:
        if not isinstance(row, lr.Lst) or not row.items:
            raise ValueError("expected literal phase entries")
        phase = symbol(row.items[0])
        if phase in result:
            raise ValueError(f"duplicate phase {phase}")
        result[phase] = row
    return result


def rewrite(kind_source: str, arm_source: str) -> tuple[str, int]:
    kind = one("(defmachine fn2-boot ?*rest)", kind_source)
    states = [symbol(node) for node in value(kind, ":states").items]
    if len(states) != len(set(states)):
        raise ValueError("duplicate boot states")
    actual = rows(value(one("(defmachine-arms fn2-boot :declare ?*rest)", arm_source), ":arms"))
    phases = [phase for phase in states if phase.startswith(":checkpoint-evidence-")]
    if set(phases) != set(EVIDENCE_OPERATIONS):
        raise ValueError("evidence class changed; review concrete custody before rewriting")
    for phase in phases:
        body = actual.get(phase)
        if body is None or len(body.items) < 2 or not list(lr.match(
                f"({EVIDENCE_OPERATIONS[phase]} ?*args)", [body], deep=True)):
            raise ValueError(f"{phase} lacks its actual evidence operation")
    arms_node, holds_node = value(kind, ":arms"), value(kind, ":holds")
    arms, holds = rows(arms_node), rows(holds_node)
    if [phase for phase in states if phase in arms] != list(arms):
        raise ValueError("existing arm declarations are not a state-order subsequence")
    if set(states) - set(arms) - set(phases) or set(arms) - set(states):
        raise ValueError("non-evidence arm mismatch is outside this repair")
    if set(holds) - set(states):
        raise ValueError("ownership names an undeclared phase")
    for phase in phases:
        if phase in holds and [symbol(x) for x in holds[phase].items] != [phase, ":storage-window"]:
            raise ValueError(f"conflicting concrete custody for {phase}")
    edits = []
    count = 0
    for node, existing, hold, indent in ((arms_node, arms, False, 8), (holds_node, holds, True, 9)):
        additions = defaultdict(list)
        for phase in phases:
            if phase in existing:
                continue
            later = next((existing[state].start for state in states[states.index(phase) + 1:]
                          if state in existing), node.end - 1)
            additions[later].append(f"({phase}" + (" :storage-window)" if hold else ")"))
            count += 1
        for at, items in additions.items():
            spacing = "\n" + " " * indent
            start = at
            while start and kind_source[start - 1] in " \t":
                start -= 1
            edits.append((start, at, spacing + spacing.join(items) + spacing))
    return lr.write(kind_source, edits), count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", type=Path, default=Path("books/boot-kind.lisp"))
    parser.add_argument("--arms", type=Path, default=Path("books/boot.lisp"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    before = args.kind.read_text()
    after, count = rewrite(before, args.arms.read_text())
    if args.write and count:
        args.kind.write_text(after)
    print(f"{args.kind}: {count} evidence declaration entries" + (" repaired" if args.write else " (dry run)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
