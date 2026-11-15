#!/usr/bin/env python3
"""Replace fault literals only in recognized commit-harness command positions."""
from pathlib import Path
import sys
from lisp_rewrite import Atom, Lst, match, parse, write

FAULTS = {10: "lying-flush", 11: "tear", 12: "no-space", 14: "fail-slow",
          23: "flush-io", 24: "short-write", 26: "none"}


def constant(node):
    if isinstance(node, Atom) and node.kind == "number" and node.text.isdecimal():
        name = FAULTS.get(int(node.text))
        if name:
            return f"*fn2-fault-{name}*"
    return None


def rewrite(text):
    parsed = parse(text)
    edits = []
    for found in match("'(:auto ?code)", parsed.forms):
        value = constant(found.captures["code"])
        if value:
            edits.append((found.start, found.end, f"(list :auto {value})"))
    for pattern in ("(equal fault ?code)", "(fn2-sim-clock ?tick ?code ?sim)",
                    "(if (member-eq tag ?modes) ?code ?otherwise)"):
        for found in match(pattern, parsed.forms):
            node = found.captures["code"]
            value = constant(node)
            if value:
                edits.append((node.start, node.end, value))
    for found in match("(member-equal fault '?codes)", parsed.forms):
        codes = found.captures["codes"]
        if isinstance(codes, Lst) and codes.items and all(constant(n) for n in codes.items):
            # Replace the quoted list, retaining the membership call verbatim.
            quoted = found.node.items[2]
            value = "(list " + " ".join(constant(n) for n in codes.items) + ")"
            edits.append((quoted.start, quoted.end, value))
    for found in match("(and (natp ?fault) (< ?fault *fn2-fault-none*))", parsed.forms):
        node = found.captures["fault"]
        edits.append((found.start, found.end,
                      "(fn2-sim-real-faultp " + parsed.text[node.start:node.end] + ")"))
    for found in match("(< forced *fn2-fault-none*)", parsed.forms):
        edits.append((found.start, found.end, "(fn2-sim-real-faultp forced)"))
    return write(parsed.text, edits), len(edits)


if __name__ == "__main__":
    for filename in sys.argv[1:]:
        path = Path(filename)
        updated, count = rewrite(path.read_text())
        path.write_text(updated)
        print(f"{path}: {count} structural replacements")
