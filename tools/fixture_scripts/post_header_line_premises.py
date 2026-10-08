#!/usr/bin/env python3
"""Add producer-discharged line premises to nine LOCAL recipe lemmas.

These helper claims over arbitrary synthetic recipes cease to be true after
hardening. Public injection statements retain their original antecedents.
Run from the worktree; fixtures run before the two named files are written.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lisp_rewrite as lr

TARGETS = {
    "books/poster-bytes-invariants.lisp": (
        "fn-pb-block-agent-of-a-block", "fn-pb-path-agent-of-a-block"),
    "books/injection-info-params-invariants.lisp": (
        "fn-ipp-at-stamp-of-a-block", "fn-ipp-with-params-of-a-prefix",
        "fn-ipp-with-params-of-a-block", "fn-ipp-with-params-of-a-prefix-x",
        "fn-ipp-with-params-of-a-block-x", "fn-ipp-v3-block-agent",
        "fn-ipp-v3-path-agent-of-a-block-with"),
}


def transform(text, names, agent):
    parsed = lr.parse(text)
    edits = []
    for name in names:
        matches = lr.match("_", parsed.forms, head="defthm", name=name)
        assert len(matches) == 1, (name, len(matches))
        event = matches[0].node
        # Restrict the transformation to a theorem directly inside LOCAL.
        parents = lr.match("_", parsed.forms, head="local",
                           where=lambda m: event in m.node.items)
        assert len(parents) == 1, (name, "not local")
        term = event.items[2]
        assert isinstance(term, lr.Lst) and term.items[0].low == "implies"
        antecedent = term.items[1]
        assert isinstance(antecedent, lr.Lst) and antecedent.items[0].low == "and"
        old = text[antecedent.start:antecedent.end]
        assert "(true-listp date)" in old and "(equal (len date) 31)" in old
        additions = ["(fn-pb-line-textp date)",
                     "(implies gid (fn-pb-line-textp msgid))"]
        if agent:
            additions.append("(fn-pb-line-textp agent)")
        missing = [p for p in additions if p not in old]
        if missing:
            edits.append((antecedent.end - 1, antecedent.end - 1,
                          "\n                 " + "\n                 ".join(missing)))
    return lr.write(text, edits)


def fixtures():
    old = "(local (defthm probe (implies (and (true-listp date) (equal (len date) 31)) (equal x y))))\n"
    new = transform(old, ("probe",), True)
    assert new == old.replace("31))", "31)\n                 (fn-pb-line-textp date)\n                 (implies gid (fn-pb-line-textp msgid))\n                 (fn-pb-line-textp agent))")
    assert transform(new, ("probe",), True) == new
    for bad in (old.replace("(local ", "(progn "), old.replace("31", "30")):
        try:
            transform(bad, ("probe",), True)
        except AssertionError:
            pass
        else:
            raise AssertionError("fixture should refuse")


if __name__ == "__main__":
    fixtures()
    for path, names in TARGETS.items():
        p = Path(path)
        text = p.read_text()
        new = transform(text, names, "injection-info" in path)
        lr.parse(new)
        p.write_text(new)
        print(f"{path}: {len(names)} local recipe lemmas; public statements untouched")
