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


def owner_contract(source, worker_source):
    parsed = [read_sexp(text) for text in forms(worker_source)]
    all_nodes = [node for form in parsed for node in walk(form)]
    def nested(name):
        return next(node for node in all_nodes if node[:2] == ["defun", name])
    take = nested("fn2-checkpoint-page-take-children")
    assert all(arg.startswith("fn2-") for arg in take[2]), "TAKE must derive destination from actual carriers"
    assert ["fn2-machines-kind-basesi", "*fn2-checkpoint-page-worker-kind*", "fn2-machines"] in list(walk(take))
    assert ["fn2-checkpoint-page-worker-generation", "0", "fn2-checkpoint-page-worker"] in list(walk(take))
    assert ["transferred", ["if", ["eq", "code", ":ok"], "1", "0"]] in list(walk(take))
    returned = nested("fn2-checkpoint-page-return-children")
    assert any(node and node[0] == "fn2-checkpoint-page-complete-p" for node in walk(returned))
    assert ["equal", ["fn2-checkpoint-page-worker-pending", "0", "fn2-checkpoint-page-worker"], "0"] in list(walk(returned))
    for callee in ("fn2-pool-hand", "fn2-pool-accept-hand"):
        target = definition((ROOT / "books/pool.lisp").read_text(), callee)
        calls = [node for node in all_nodes if node and node[0] == callee]
        assert len(calls) == 2 and all(len(call) - 1 == len(target[2]) for call in calls)
    arms = next(form for form in parsed if form[:3] == ["defmachine-arms", "fn2-checkpoint-page-worker", ":declare"])
    arms = arms[arms.index(":arms") + 1]
    allowed = {"fn2-checkpoint-page-context-op", "fn2-checkpoint-page-format-op", "fn2-checkpoint-page-issue-op", "fn2-checkpoint-page-phase-op"}
    for arm in arms:
        if arm[0] in (":context", ":format", ":issue", ":wait"):
            operations = {node[0] for node in walk(arm) if node and isinstance(node[0], str) and node[0].startswith("fn2-")}
            assert operations <= allowed, "physical phase may not pack, mutate, return or release the workspace"
    assert ["defmachine-arms", "fn2-checkpoint-page-worker", ":children"] in all_nodes
    assert ["defmachine-arms", "fn2-checkpoint-page-worker", ":wrappers"] in all_nodes
    for name in ("context", "format-step", "issue"):
        function = definition(source, "fn2-checkpoint-page-" + name)
        assert ["equal", ["fn2-checkpoint-page-transferred", "0", "fn2-checkpoint-page"], "1"] in list(walk(function))
    issued = definition(source, "fn2-checkpoint-page-issue")
    call = next(node for node in walk(issued) if node and node[0] == "fn2-block-write-children")
    assert call[1] == ["+", ["*", ["fn2-checkpoint-page-extent", "0", "fn2-checkpoint-page"], "*fn2-storage-extent-units*"], ["floor", "cursor", "4096"]]
    assert call[4:6] == ["0", "4096"] and call[8] == "cursor"
    assert call[9:12] == [["fn2-checkpoint-page-io-owner-kind", "0", "fn2-checkpoint-page"], ["fn2-checkpoint-page-io-owner-slot", "0", "fn2-checkpoint-page"], ["fn2-checkpoint-page-io-owner-gen", "0", "fn2-checkpoint-page"]]

def main():
    source = BOOK.read_text()
    harvest_contract(source)
    shape_contract(source)
    worker_source = (ROOT / "books/checkpoint-page-worker.lisp").read_text()
    owner_contract(source, worker_source)
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
    for changed in (
        worker_source.replace("(fn2-checkpoint-page-complete-p", "(fn2-checkpoint-page-live-p", 1),
        worker_source.replace("(fn2-checkpoint-page-phase-op))", "(fn2-checkpoint-page-return))", 1),
    ):
        assert changed != worker_source
        try:
            owner_contract(source, changed)
        except AssertionError:
            continue
        raise AssertionError("source contract accepted a premature ownership return")
    print("checkpoint page source contracts: harvest + 5 return/frame contracts + captured guards + 6 actual callee arities + generated owner handoff/physical arm isolation; 6 rejection controls pass (no ACL2 execution)")


if __name__ == "__main__":
    main()
