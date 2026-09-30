#!/usr/bin/env python3
"""Source call/site inventory; never a compiled allocation correspondence.

Reads trusted project source without the Lisp reader. Counts all syntax sites,
including mutually exclusive branches, separately from any executed trace.
The selected runtime compiler/primitive/stack join must consume an actual trace;
these source counts alone cannot establish that join.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from ledger import Sym, read_forms

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ["books/legacy-parser-cursor.lisp", "books/article.lisp",
           "books/acceptance-alloc.lisp"]
ROOTS = ["fn-lpc-begin", "fn-lpc-tick", "fn-lpc-field", "fn-lpc-body-lines",
         "fn-lpc-tombstonep", "fn-lpc-ready-p"]
PRIMITIVES = {"+", "-", "1-", "<", "<=", "equal", "eq", "natp", "nfix", "zp",
              "integerp", "cons", "list", "car", "cdr", "consp", "not"}
BOUNDARY = {"fn-arena-get": "borrowed octet from authorized physical source",
            "fn-arena-count": "maintained arena handle count",
            "fn-arena-payload-len": "maintained arena payload length"}


def calls(expr):
    if not isinstance(expr, list) or not expr:
        return Counter()
    head = str(expr[0]).lower() if isinstance(expr[0], Sym) else None
    if head in {"quote", "declare"}:
        return Counter()
    result = Counter({head: 1}) if head else Counter()
    for arg in (expr[1:] if head else expr):
        result.update(calls(arg))
    return result


def inventory():
    definitions = {}
    fingerprints = {}
    for source in SOURCES:
        raw = (ROOT / source).read_bytes()
        fingerprints[source] = hashlib.sha256(raw).hexdigest()
        for form in read_forms(raw.decode()):
            if isinstance(form, list) and form and str(form[0]).lower() == "defun":
                name = str(form[1]).lower()
                body = [x for x in form[3:] if not
                        (isinstance(x, list) and x and str(x[0]).lower() == "declare")]
                definitions[name] = (source, body)
    pending = list(ROOTS)
    visited = {}
    while pending:
        name = pending.pop()
        if name in visited or name not in definitions:
            continue
        source, body = definitions[name]
        sites = Counter()
        for expr in body:
            sites.update(calls(expr))
        edges = sorted(n for n in sites if n in definitions)
        visited[name] = {"source": source, "calls": edges,
                         "source_sites": {n: sites[n] for n in sorted(sites)
                                          if n in PRIMITIVES or n in definitions or n in BOUNDARY},
                         "opaque_boundaries": sorted(n for n in sites if n in BOUNDARY)}
        pending.extend(edges)
    return {"scope": "source syntax inventory; no compiled/runtime or all-input cost verdict",
            "roots": ROOTS, "source_sha256": fingerprints,
            "functions": dict(sorted(visited.items())), "boundaries": BOUNDARY,
            "dynamic_index_obligations": {
                "fn-lpc-at magic index": "position<8 on the selected short-circuit branch",
                "fn-lpc-put field index": "natural selected key<5 on close-fields branch",
                "fn-lpc-field index": "natural k<5 guard; borrowed four-field span"},
            "stack_obligations": {
                "fn-lpc-tick": "fuel+1 recursive frames in general; actual staged consumer passes fuel1",
                "fn-lpc-at": "literal maximum index10; dynamic magic index<=7",
                "fn-lpc-put": "literal maximum index10; dynamic field index<=4",
                "outer quantum": "fn-obc-quantum-one is nonrecursive; consumer call graph still to inventory"},
            "excluded": ["actual compiler call graph and primitive lowering",
                         "compiler helper/runtime allocation", "guard cache and first-use metadata",
                         "native wrapper call lists", "conditions/fault construction",
                         "physical arena provider", "outer consumer/formatter/output prefixes"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = inventory()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.write:
        path = ROOT / "planning/evidence/legacy-parser-runtime-inventory.json"
        path.write_text(rendered)
        print(path)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
