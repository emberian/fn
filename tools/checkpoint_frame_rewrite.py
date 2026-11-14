#!/usr/bin/env python3
"""Derive owned checkpoint leaf frame domains from their actual declarations.

Only six multi-input frame declarations are rewritten. Operation bodies and
row-count effects stay byte-for-byte unchanged. This does not prove contracts.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import lisp_rewrite as rw

TARGETS = {
    "fn2-checkpoint-frozen-map-entry", "fn2-checkpoint-frozen-arena-entry",
    "fn2-checkpoint-map-pack-entry", "fn2-checkpoint-arena-pack-entry",
    "fn2-checkpoint-restore-header", "fn2-checkpoint-restore-entry",
}


def atom(node):
    return node.text.lower() if isinstance(node, rw.Atom) else None


def keyword(items, name):
    for i, item in enumerate(items[:-1]):
        if atom(item) == name:
            return items[i + 1]
    return None


def rewrite(source):
    parsed = rw.parse(source)
    definitions = {atom(form.items[1]): form for form in parsed.forms
                   if isinstance(form, rw.Lst) and len(form.items) >= 4 and atom(form.items[0]) == "defun"}
    edits = []
    for form in parsed.forms:
        if not isinstance(form, rw.Lst) or len(form.items) < 3:
            continue
        head, name = atom(form.items[0]), atom(form.items[1])
        if name not in TARGETS or not head or not head.endswith("-preserves"):
            continue
        definition = definitions[name]
        if rw.emit(form.items[2]) != rw.emit(definition.items[2]):
            raise ValueError(f"{name}: preservation call differs from actual formals")
        declaration = definition.items[3]
        if not isinstance(declaration, rw.Lst) or atom(declaration.items[0]) != "declare":
            raise ValueError(f"{name}: missing actual declaration")
        xargs = next((x for x in declaration.items if isinstance(x, rw.Lst) and atom(x.items[0]) == "xargs"), None)
        if xargs is None:
            raise ValueError(f"{name}: missing XARGS")
        stobjs = keyword(xargs.items, ":stobjs")
        guard = keyword(xargs.items, ":guard")
        if stobjs is None or guard is None:
            raise ValueError(f"{name}: explicit STOBJS and GUARD required")
        tables = stobjs.items if isinstance(stobjs, rw.Lst) else [stobjs]
        hyps = [f"({rw.emit(table)}p {rw.emit(table)})" for table in tables]
        guard_terms = guard.items[1:] if isinstance(guard, rw.Lst) and atom(guard.items[0]) == "and" else [guard]
        hyps += [rw.emit(term) for term in guard_terms]
        specs = keyword(form.items, ":specs")
        pack = name in {"fn2-checkpoint-map-pack-entry", "fn2-checkpoint-arena-pack-entry"}
        if not pack:
            position = keyword(form.items, ":position")
            # Rewritten declarations expose the same projection in SPECS.
            if position is None and isinstance(specs, rw.Lst):
                position = specs.items[0].items[2]
            if position is None:
                raise ValueError(f"{name}: explicit result projection required")
            table = head.removesuffix("-preserves")
            at = rw.emit(position)
            spec_text = [f'("-GUARD-DOMAIN-TYPE" {table}p {at})',
                         f'("-GUARD-DOMAIN-WFP" {table}-wfp {at})',
                         # Shape ignores column values; retain the original,
                         # broader destination-only WFP claim and row effect.
                         f'("-PRESERVES-WFP" {table}-wfp {at} :hyps (({table}p {table}) ({table}-wfp {table})))',
                         f'("-PRESERVES-ROWS" {table}-rows {at} :frame {table})']
        else:
            if not isinstance(specs, rw.Lst):
                raise ValueError(f"{name}: explicit output/effect observations required")
            spec_text, visited = [], set()
            for spec in specs.items:
                suffix = spec.items[0].text.strip('"').removeprefix("-GUARD-DOMAIN")
                if suffix in visited:
                    continue
                visited.add(suffix)
                rest = " ".join(rw.emit(item) for item in spec.items[1:])
                if suffix.endswith(("-TYPE", "-WFP")):
                    spec_text.append(f'("-GUARD-DOMAIN{suffix}" {rest})')
                    # These old explicit packer claims already have the whole
                    # source domain. Preserve their names and exact conclusion.
                    spec_text.append(f'("{suffix}" {rest})')
                else:
                    spec_text.append(f'("{suffix}" {rest})')
        replacement = (f"({head} {name}\n {rw.emit(form.items[2])}\n"
                       f" :hyps ({' '.join(hyps)})\n :specs ({' '.join(spec_text)}))")
        edits.append((form.start, form.end, replacement))
    return rw.write(source, edits), len(edits)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    for path in args.files:
        source = path.read_text()
        result, count = rewrite(source)
        if args.write:
            path.write_text(result)
        print(f"{path}: {count} actual-guard frame declaration(s), changed={source != result}")


if __name__ == "__main__":
    main()
