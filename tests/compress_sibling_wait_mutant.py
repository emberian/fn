#!/usr/bin/env python3
"""Emit the original actual wait implementation and its unchanged full witness.

Send after the current compression fixture in a retained ACL2 world. The
negative assertion checks that restoring the old fresh-sibling kick fails
while all owner progress/settlement code remains the actual fixture.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms
from ledger import Sym, read_forms


def source_of(value):
    if isinstance(value, Sym):
        return str(value)
    if isinstance(value, list):
        return "(" + " ".join(map(source_of, value)) + ")"
    if isinstance(value, str):
        return json.dumps(value)
    return str(value)


def original_wait_ast(source):
    selected = [f for f in forms(source)
                if f.startswith("(defun fn2-compress-record-stack-wait\n")]
    assert len(selected) == 1, "expected the actual wait implementation"
    fn = read_forms(selected[0])[0]
    body = fn[-1]
    assert body[0] == Sym("let") and len(body[1]) == 1
    binding = body[1][0]
    assert binding[0] == Sym("ownerp") and binding[1][0] == Sym("and")
    clauses = body[2]
    assert clauses[0] == Sym("cond") and len(clauses) == 4
    blocked, owner, fallback = clauses[1:]
    assert blocked[1] == read_forms("(mv 0 nil)")[0]
    assert owner[0][:2] == [Sym("and"), Sym("ownerp")]
    assert fallback[0] == Sym("t")
    # Reverse only the new non-owner rule and inline its factored predicate.
    # This reconstructs the historical IF form without needing Git history.
    condition = [Sym("and"), *binding[1][1:], *owner[0][2:]]
    return [*fn[:-1], [Sym("if"), condition, owner[1], fallback[1]]]


def mutant_forms():
    original = original_wait_ast((ROOT / "books/compress-close.lisp").read_text())
    original[1] = Sym("fn2-compress-record-stack-wait-spinning")
    yield source_of(original)
    selected = [f for f in forms((ROOT / "tests/compress-record-unit.lisp").read_text())
                if f.startswith("(defun fn2-compress-sibling-")]
    assert len(selected) == 4, "expected both fresh-instance and owner control pairs"
    for form in selected:
        yield form.replace("fn2-compress-sibling-", "fn2-compress-spinning-").replace(
            "fn2-compress-record-stack-wait", "fn2-compress-record-stack-wait-spinning")
    yield "(assert-event (not (fn2-compress-spinning-owner-check)))"


if __name__ == "__main__":
    print("\n".join(mutant_forms()))
