#!/usr/bin/env python3
"""Rename the scratch boundary calculus to its more general shielding domain.

Canonical ART predicates in article-art are deliberately outside this transform.
Comments, strings and longer symbols are preserved; only exact Lisp atoms move.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lisp_rewrite as lr

NAMES = {
    "fn-art-separated-headp": "fn-art-shielded-headp",
    "fn-art-rest-separated-headp": "fn-art-rest-shielded-headp",
}

def transform(text):
    parsed = lr.parse(text)
    edits = []
    for m in lr.match("_", parsed.forms):
        n = m.node
        if isinstance(n, lr.Atom) and not isinstance(n, lr.Str) and n.low in NAMES:
            edits.append((n.start, n.end, NAMES[n.low]))
    return lr.write(text, edits)

if __name__ == "__main__":
    sample = '; fn-art-separated-headp\n(foo fn-art-separated-headp "fn-art-separated-headp" fn-art-separated-headp-other)\n'
    expected = '; fn-art-separated-headp\n(foo fn-art-shielded-headp "fn-art-separated-headp" fn-art-separated-headp-other)\n'
    assert transform(sample) == expected
    assert transform(expected) == expected
    p = Path("books/post-header-local.lisp")
    old = p.read_text()
    new = transform(old)
    lr.parse(new)
    p.write_text(new)
    print("post-header-local: exact boundary predicate symbols renamed; canonical ART unchanged")
