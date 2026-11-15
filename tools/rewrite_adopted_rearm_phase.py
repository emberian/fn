#!/usr/bin/env python3
"""Share rearm predicates between HELD and the terminal ADOPTED continuation.

Every named public function remains a HELD wrapper.  Only the one internal
body accepts a phase; the only redirected calls are within this family.
"""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
FAMILY = {
    "checkpoint-build-state": {"fn2-checkpoint-build-ownerp": "80904dafcb28a26fa0990f15bbc3c4a316fab9b4020a513793b92476e4932889"},
    "checkpoint-build": {"fn2-checkpoint-build-ready": "f1f49f9836b117e8a0ec34611dee87eb167bcdee620fe0fc225a7898149777ef"},
    "checkpoint-plan": {"fn2-checkpoint-plan-ownerp": "21fbd964f213d9a1e27b55de0338139d66cb6532a16096118daee5279a29c6d1", "fn2-checkpoint-plan-closedp": "1f39b612e84e621332adcb207adf6ae2bfe81090b69e61ca9c4238a9e11f23a2"},
    "checkpoint-master-control": {"fn2-checkpoint-master-ready-children": "15739a0e6eaa96add69bef31c73acf143e066cef8750b486af01d0e086ef4b5a", "fn2-checkpoint-master-release-complete-children": "59a005ce85c9437be005c734c39e5fa70b40e4381e3c2ecdfc75e2cdb49b0cdf"},
    "checkpoint-master-rearm": {"fn2-checkpoint-master-rearm-children": "1f2c870bc19922b56eb43d335d44288d3bcd8170531136920bb6ba6d3bd7d0ce"},
    "event-producer": {"fn2-event-producer-ownerp": "cdad48316d26a8882140431de0228674e315794742474e19beafd01da99e9751", "fn2-event-producer-donep": "5adef318063c95b9939ee08584de24ed37421945e9e7b6d8603268ac5b1e17b1"},
    "event-rearm": {"fn2-event-producer-rearm": "fe8bb5fd49cca8bb7c7a175e3cf53b2976beed0637850d2fd95363c81d5fc7bb"},
    "event-frontier-source": {"fn2-event-frontier-source-p": "ed38645fc762cf2a6493bf81be4be4644fba89fb5387e8a9eb63072397eaf3a2"},
    "event-read-source": {"fn2-event-read-ownerp": "3f2e25024417f60ecbe0f10f6d3c893bfcccb448f9e5e30500887b5427e7f3f7"},
}
NAMES = {name for functions in FAMILY.values() for name in functions}
HELD = "*fn2-csnapshot-phase-held*"


def walk(node):
    yield node
    if isinstance(node, lr.Pre):
        yield from walk(node.node)
    elif isinstance(node, lr.Lst):
        for item in node.items:
            yield from walk(item)


def head(node):
    if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom):
        return node.items[0].low
    return None


def source_function(parsed, name):
    matches = [node for top in parsed.forms for node in walk(top)
               if head(node) == "defun" and len(node.items) > 1
               and isinstance(node.items[1], lr.Atom) and node.items[1].low == name]
    if len(matches) != 1:
        raise AssertionError((name, "expected one defun", len(matches)))
    return matches[0]


def rewrite_file(path: Path, functions: dict[str, str]):
    parsed = lr.parse(path)
    edits = []
    for name, digest in functions.items():
        form = source_function(parsed, name)
        actual = hashlib.sha256(parsed.text[form.start:form.end].encode()).hexdigest()
        if actual != digest:
            raise AssertionError((name, "source function drift", actual))
        if len(form.items) != 5 or head(form.items[3]) != "declare":
            raise AssertionError((name, "unexpected function shape"))
        _, symbol, formals, declaration, body = form.items
        if not isinstance(formals, lr.Lst):
            raise AssertionError((name, "non-list formals"))
        args = [arg.text for arg in formals.items]
        if len(args) != len(set(args)) or "phase" in args:
            raise AssertionError((name, "invalid formals"))
        at_phase = name + "-at-phase"
        edits.extend([(symbol.start, symbol.end, at_phase),
                      (formals.start + 1, formals.start + 1, "phase ")])
        held_count = 0
        for node in walk(body):
            if isinstance(node, lr.Atom) and node.low == HELD:
                edits.append((node.start, node.end, "phase"))
                held_count += 1
            if head(node) in NAMES:
                callee = node.items[0]
                edits.append((node.start, callee.end,
                              "(" + callee.text + "-at-phase phase"))
        if held_count not in (0, 1):
            raise AssertionError((name, "unexpected HELD literals", held_count))
        args_text = parsed.text[formals.start:formals.end]
        decl_text = parsed.text[declaration.start:declaration.end]
        wrapper = ("\n(defun " + name + " " + args_text + "\n " + decl_text +
                   "\n (" + at_phase + " " + HELD +
                   (" " + " ".join(args) if args else "") + "))")
        edits.append((form.end, form.end, wrapper))
    path.write_text(lr.write(parsed.text, edits))


if __name__ == "__main__":
    for stem, functions in FAMILY.items():
        rewrite_file(ROOT / "books" / (stem + ".lisp"), functions)
