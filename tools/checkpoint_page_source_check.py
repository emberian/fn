#!/usr/bin/env python3
"""Narrow syntax contracts; never evaluates ACL2 or simulates page contents."""
from pathlib import Path
from lisp_source import forms, read_sexp

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "books/checkpoint-page-io.lisp"


def definition(source, name):
    for text in forms(source):
        form = read_sexp(text)
        if form[:2] == ["defun", name]:
            return form
    raise AssertionError(f"missing {name}")


def harvest_contract(source):
    form = definition(source, "fn2-checkpoint-page-harvest")
    body = form[-1]
    assert body[0] == "b*" and len(body) == 3
    bindings = body[1]
    unchanged = ["mv", ":ok", "fn2-checkpoint-page", "fn2-checkpoint-page-verified", "fn2-checkpoint-construction"]
    assert bindings[0][1] == unchanged, "unrelated event must be successful no-op"
    assert body[-1] == unchanged, "consumed failure is represented in retained phase"
    success = next(value for name, value in bindings if name == "success")
    assert ["equal", "outcome", "*fn2-outcome-done*"] in success
    assert ["equal", "count", "4096"] in success
    event_guard = bindings[0][0][1]
    assert ["equal", "evkind", "*fn2-event-write-result*"] in event_guard
    assert ["equal", "opslot", ["fn2-checkpoint-page-op-slot", "0", "fn2-checkpoint-page"]] in event_guard
    assert ["equal", "opgen", ["fn2-checkpoint-page-op-gen", "0", "fn2-checkpoint-page"]] in event_guard
    page_write = bindings[-1][1]
    assert ["pending", "0"] in page_write
    phase = next(field[1] for field in page_write[2:] if field[0] == "phase")
    assert phase[0:2] == ["if", "success"] and phase[-1] == "*fn2-checkpoint-page-phase-uncertain*"
    for carrier in ("fn2-checkpoint-construction", "fn2-checkpoint-page-verified"):
        update = next(value for name, value in bindings if name == carrier)
        assert update[0:2] == ["if", "success"] and update[-1] == carrier


def main():
    source = BOOK.read_text()
    harvest_contract(source)
    mutations = (
        source.replace("(mv :ok fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction)", "(mv :unrelated fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction)", 1),
        source.replace("(equal count 4096)", "t", 1),
        source.replace("(equal opgen (fn2-checkpoint-page-op-gen 0 fn2-checkpoint-page))", "t", 1),
        source.replace("*fn2-checkpoint-page-phase-uncertain*)))) )", "*fn2-checkpoint-page-phase-complete*)))) )", 1),
    )
    for changed in mutations:
        assert changed != source, "mutation did not reach its target"
        try:
            harvest_contract(changed)
        except AssertionError:
            continue
        raise AssertionError("source contract accepted a deliberately broken harvest")
    print("checkpoint page harvest source contract: 1 positive, 4 rejection controls pass (no ACL2 execution)")


if __name__ == "__main__":
    main()
