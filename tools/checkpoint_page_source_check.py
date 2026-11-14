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



def walk(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from walk(child)


def shape_contract(source):
    expected = {
        "begin": ["fn2-checkpoint-page"],
        "context": ["fn2-checkpoint-page", "fn2-fc-context", "fn2-digests"],
        "format-step": ["fn2-checkpoint-page", "fn2-checkpoint-page-verified", "fn2-fc", "fn2-b3", "fn2-fields", "fn2-pool", "fn2-digests"],
        "issue": ["fn2-checkpoint-page", "fn2-pool", "fn2-ops", "fn2-control", "fn2-extents", "fn2-alloc-edges"],
        "harvest": ["fn2-checkpoint-page", "fn2-checkpoint-page-verified", "fn2-checkpoint-construction"],
    }
    parsed = [read_sexp(text) for text in forms(source)]
    for suffix, outputs in expected.items():
        name = "fn2-checkpoint-page-" + suffix
        function = definition(source, name)
        body = function[-1]
        assert body[0] == "b*" and len(body) == 3
        # Inspect actual result expressions; B* multi-value binders are not exits.
        def exits(tree):
            if not isinstance(tree, list) or not tree:
                return
            if tree[0] == "b*":
                for _, value in tree[1]:
                    yield from exits(value)
                yield from exits(tree[2])
            else:
                if tree[0] == "mv":
                    yield tree
                for child in tree[1:]:
                    yield from exits(child)
        results = list(exits(body))
        assert results and all(result[2:] == outputs for result in results), name + " result projection mismatch"
        theorem = next(form for form in parsed if form[:2] == ["fn2-checkpoint-page-preserves", name])
        specs = theorem[theorem.index(":specs") + 1]
        for position, carrier in enumerate(outputs, 1):
            # String theorem suffixes are omitted by lisp_source's plain reader.
            assert [carrier + "p", str(position)] in specs
            assert [carrier + "-wfp", str(position)] in specs
            assert [carrier + "-rows", str(position), ":frame", carrier] in specs
        inputs = function[3][1]
        inputs = inputs[inputs.index(":stobjs") + 1]
        hyps = theorem[theorem.index(":hyps") + 1]
        assert all([carrier + "p", carrier] in hyps and [carrier + "-wfp", carrier] in hyps for carrier in inputs)
    format_body = definition(source, "fn2-checkpoint-page-format-step")[-1]
    bound = set()
    for binder, value in format_body[1]:
        if any(node == ["fn2-fc-guard"] for node in walk(binder)):
            assert {"row", "off", "len", "base"} <= bound, "fc guard macro captures must be explicitly bound"
            break
        if isinstance(binder, str):
            bound.add(binder)
    else:
        raise AssertionError("missing literal fc guard")
    # Match scalar/stobj argument counts against the actual current callees.
    for book, callee in (("checkpoint-writer-ops.lisp", "fn2-checkpoint-writer-checker-children"),
                         ("checkpoint-boot.lisp", "fn2-checkpoint-boot-geometry-load"),
                         ("format-check.lisp", "fn2-format-run"),
                         ("machines-b.lisp", "fn2-block-write-children")):
        target = definition((ROOT / "books" / book).read_text(), callee)
        calls = [node for form in parsed for node in walk(form) if node and node[0] == callee]
        assert calls and all(len(call) - 1 == len(target[2]) for call in calls), callee + " argument count mismatch"

def main():
    source = BOOK.read_text()
    harvest_contract(source)
    shape_contract(source)
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
    print("checkpoint page source contracts: harvest + 5 return/frame contracts + captured guards + 4 actual callee arities; 4 rejection controls pass (no ACL2 execution)")


if __name__ == "__main__":
    main()
