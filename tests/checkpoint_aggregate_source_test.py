#!/usr/bin/env python3
"""Narrow syntax controls for actual aggregate callers; no ACL2 execution/model."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_sexp


def parsed(source):
    return [read_sexp(text) for text in forms(source)]


def definition(source, name):
    return next(form for form in parsed(source) if form[:2] == ["defun", name])


def walk(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from walk(child)


def contract(plan, mapping, fixture):
    count = definition(plan, "fn2-checkpoint-plan-count-step")
    assert count[2] == ["fn2-checkpoint-plan", "fn2-csnapshot", "fn2-checkpoint-build", "fn2-checkpoint-refs", "fn2-checkpoint-construction", "fn2-extents", "fn2-checkpoint-plan-marks"]
    declaration = count[3][1]
    assert declaration[declaration.index(":stobjs") + 1] == count[2]
    assert ["fn2-checkpoint-refs-wfp", "fn2-checkpoint-refs"] in list(walk(declaration))
    body = count[-1]
    assert body[0] == "b*" and len(body) == 3
    bindings = body[1]
    values = {name: value for name, value in bindings if isinstance(name, str)}
    assert values["intended"] == ["fn2-checkpoint-construction-intended-bytes", "e", "fn2-checkpoint-construction"]
    begin = definition(plan, "fn2-checkpoint-plan-begin")
    begin_nodes = list(walk(begin))
    for role in ("1", "3", "4"):
        field = "role" + role + "-bytes"
        assert [field, "0"] in begin_nodes
        assert values["next-role" + role] == ["+", ["fn2-checkpoint-plan-" + field, "0", "fn2-checkpoint-plan"], ["if", ["and", "own", ["equal", "role", role]], "intended", "0"]]
        assert ["unsigned-byte-p", "60", "next-role" + role] in list(walk(values["valid"]))
        assert [field, "next-role" + role] in list(walk(bindings[-1]))
    # Exact root aggregates are checked at COUNT EOF and final closure EOF.
    for name in ("count-step", "validate-step"):
        function = definition(plan, "fn2-checkpoint-plan-" + name)
        eof = function[-1][1][2 if name == "count-step" else 3]
        assert eof[0][0] == "when"
        assert ["fn2-checkpoint-plan-aggregatesp", "fn2-checkpoint-plan", "fn2-checkpoint-refs"] in list(walk(eof))
    aggregate = definition(plan, "fn2-checkpoint-plan-aggregatesp")
    for role in ("1", "3", "4"):
        at = ["+", ["*", "6", "c"], role]
        total = ["fn2-checkpoint-plan-role" + role + "-bytes", "0", "fn2-checkpoint-plan"]
        for observed in ("root-intended-bytes", "root-completed-bytes"):
            assert ["equal", ["fn2-checkpoint-refs-" + observed, at, "fn2-checkpoint-refs"], total] in list(walk(aggregate))
    root = definition(plan, "fn2-checkpoint-plan-rootp")
    root_nodes = list(walk(root))
    assert ["equal", ["fn2-checkpoint-refs-root-intended-bytes", "r", "fn2-checkpoint-refs"], ["fn2-checkpoint-refs-root-completed-bytes", "r", "fn2-checkpoint-refs"]] in root_nodes
    assert ["<=", ["fn2-checkpoint-construction-intended-bytes", "e", "fn2-checkpoint-construction"], ["fn2-checkpoint-refs-root-intended-bytes", "r", "fn2-checkpoint-refs"]] in root_nodes
    assert ["equal", ["fn2-checkpoint-construction-intended-bytes", "e", "fn2-checkpoint-construction"], ["fn2-checkpoint-construction-completed-bytes", "e", "fn2-checkpoint-construction"]] in root_nodes
    theorem = next(form for form in parsed(plan) if form[:2] == ["fn2-checkpoint-plan-preserves", "fn2-checkpoint-plan-count-step"])
    assert theorem[2] == count[2]
    hyps = theorem[theorem.index(":hyps") + 1]
    assert all([obj + "p", obj] in hyps and [obj + "-wfp", obj] in hyps for obj in count[2])
    specs = theorem[theorem.index(":specs") + 1]
    for pos, obj in (("1", "fn2-checkpoint-plan"), ("2", "fn2-checkpoint-plan-marks")):
        assert [obj + "p", pos] in specs and [obj + "-wfp", pos] in specs and [obj + "-rows", pos, ":frame", obj] in specs
    consume = definition(mapping, "fn2-checkpoint-map-consume-page")
    nodes = list(walk(consume))
    assert ["aggregate", ["*", "page-count", "*fn2-format-page-size*"]] in nodes
    assert ["unsigned-byte-p", "60", "aggregate"] in nodes
    assert ["root-intended-bytes", "aggregate"] in nodes and ["root-completed-bytes", "aggregate"] in nodes
    assert ["encoded-length", "*fn2-format-page-size*"] in nodes
    for form in parsed(fixture):
        for call in walk(form):
            if call and call[0] == "fn2-checkpoint-plan-count-step":
                assert len(call) - 1 == len(count[2]), "actual count caller ABI mismatch"
    assert "NOT a C-cut provenance" in fixture


def main():
    plan = (ROOT / "books/checkpoint-plan.lisp").read_text()
    mapping = (ROOT / "books/checkpoint-map-build.lisp").read_text()
    fixture = (ROOT / "tests/checkpoint-aggregate-unit.lisp").read_text()
    contract(plan, mapping, fixture)
    mutations = (
        (plan.replace("(if (and own (equal role 1)) intended 0)", "(if own intended 0)", 1), mapping),
        (plan.replace("(unsigned-byte-p 60 next-role1)", "t", 1), mapping),
        (plan.replace("(fn2-checkpoint-plan-aggregatesp fn2-checkpoint-plan fn2-checkpoint-refs)", "t", 1), mapping),
        (plan, mapping.replace("(root-intended-bytes aggregate)", "(root-intended-bytes *fn2-format-page-size*)", 1)),
    )
    for changed_plan, changed_mapping in mutations:
        assert (changed_plan, changed_mapping) != (plan, mapping)
        try:
            contract(changed_plan, changed_mapping, fixture)
        except AssertionError:
            continue
        raise AssertionError("source contract accepted broken aggregate accounting")
    print("aggregate source contract + 4 rejection controls pass; actual ACL2 fixture remains UNEXECUTED, no C-cut witness claimed")


if __name__ == "__main__":
    main()
