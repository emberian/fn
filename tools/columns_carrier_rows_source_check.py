#!/usr/bin/env python3
"""Check opt-in generator source and prepared fixture; never evaluate ACL2."""
from pathlib import Path
from lisp_source import forms, read_sexp

ROOT = Path(__file__).resolve().parents[1]


def definition(source, name):
    return next((text, form) for text in forms(source)
                if (form := read_sexp(text))[:2] == ["defun", name])


def walk(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from walk(child)


def contract(source, fixture):
    text, function = definition(source, "fn2-columns-carrier-specs")
    append = function[-1][-1][-1]
    assert append[0] == "append" and len(append) == 4
    assert append[1] == read_sexp('''`((,(concatenate 'string prefix "-TYPE") ,(fn2-columns-sym table "P") ,pos)
      (,(concatenate 'string prefix suffix) ,inv ,pos :hints ,(fn2-decl-get :hints options)))''')
    assert append[-1] == ["fn2-columns-carrier-specs", ["cdr", "carriers"]]
    assert append[2] == read_sexp('''(and (fn2-decl-get :rows options)
      `((,(concatenate 'string prefix "-ROWS") ,(fn2-columns-sym table "-ROWS") ,pos :frame ,table)))''')
    assert text.count('"-ROWS"') == 2 and text.count('"-TYPE"') == 1
    # The guard collector must remain independent from the frame opt-in.
    _, hyps = definition(source, "fn2-columns-carrier-hyps")
    assert not any(node[:2] == ["fn2-decl-get", ":rows"] for node in walk(hyps))
    assert ["fn2-columns-carrier-hyps", ["cdr", "carriers"]] in list(walk(hyps))
    assert any(node == ["fn2-columns-sym", "table"] for node in walk(hyps))  # string P omitted by plain reader
    parsed = [read_sexp(text) for text in forms(fixture)]
    assert sum(form[0] == "assert-event" for form in parsed) == 3
    copy = definition(fixture, "fn2-carrier-rows-copy")[1]
    guard = copy[3][1]
    assert ["and", ["fn2-carrier-rows-left-wfp", "fn2-carrier-rows-left"],
            ["fn2-carrier-rows-right-wfp", "fn2-carrier-rows-right"]] in guard
    actual = next(form for form in parsed if form[:2] == ["fn2-carrier-rows-left-preserves", "fn2-carrier-rows-copy"])
    carriers = actual[actual.index(":carriers") + 1]
    assert carriers[0][-2:] == [":rows", "t"] and ":rows" not in carriers[1]
    assert any(form[0] == "make-event" for form in parsed), "missing generated guard/frame inspection fixture"


def main():
    source = (ROOT / "books/columns.lisp").read_text()
    fixture = (ROOT / "tests/columns-carrier-rows-fixture.lisp").read_text()
    contract(source, fixture)
    mutations = (
        source.replace("(and (fn2-decl-get :rows options)", "(and t", 1),
        source.replace(',pos :frame ,table)', ',0 :frame ,table)', 1),
        source.replace(',pos :frame ,table)', ',pos :frame ,other)', 1),
    )
    for changed in mutations:
        assert changed != source
        try:
            contract(changed, fixture)
        except AssertionError:
            continue
        raise AssertionError("source control accepted a broken opt-in row spec")
    print("carrier rows source contract: guarded opt-in/default structure + prepared fixture, 3 rejection controls pass; ACL2 fixture unexecuted")


if __name__ == "__main__":
    main()
