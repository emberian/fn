#!/usr/bin/env python3
"""Add observer opacity to unhinted top-level column preservation calls."""
from pathlib import Path
import argparse
from lisp_rewrite import Atom, Lst, match, parse, write


def add_preservation_frame_hints(text, table="pool"):
    parsed = parse(text)
    edits = []
    for found in match(None, parsed, deep=False, head=f"fn2-{table}-preserves"):
        # Options follow the macro's name and complete formal-argument list.
        options = found.node.items[3:]
        if any(isinstance(item, Atom) and item.low == ":hints" for item in options):
            continue  # Explicit hints, including NIL, are authoritative.
        edits.append((found.end - 1, found.end - 1,
                      f'\n :hints (("Goal" :in-theory (disable fn2-{table}-rows)))'))
    return write(text, edits)


def add_preservation_spec_frame_hints(text, table, observers):
    """Prove explicit unconditional frame specs from the actual producer.

    Common hints and every explicit per-spec hint (including NIL) remain
    authoritative; TYPE/WFP specs have no :frame and are untouched.
    """
    parsed = parse(text)
    edits = []
    for found in match(None, parsed, deep=False, head=f"fn2-{table}-preserves"):
        subject = found.node.items[1]
        options = found.node.items[3:]
        for i, option in enumerate(options[:-1]):
            if not isinstance(option, Atom) or option.low != ":specs":
                continue
            specs = options[i + 1]
            if not isinstance(specs, Lst):
                continue
            for spec in specs.items:
                if not isinstance(spec, Lst):
                    continue
                keys = {x.low for x in spec.items[3:] if isinstance(x, Atom)}
                if ":frame" not in keys or ":hints" in keys:
                    continue
                hint = ('\n          :hints (("Goal" :in-theory (e/d (' + subject.text + ') ('
                        + ' '.join(observers) + '))))')
                edits.append((spec.end - 1, spec.end - 1, hint))
    return write(text, edits)


def use_preservation_adapter(text, table, adapter):
    """Change only macro heads; the adapter owns generated proof selection."""
    parsed = parse(text)
    edits = []
    for found in match(None, parsed, deep=False, head=f"fn2-{table}-preserves"):
        head = found.node.items[0]
        edits.append((head.start, head.end, adapter))
    return write(text, edits)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path)
    parser.add_argument("--table", choices=("pool", "fields", "cns-edges"), default="pool")
    parser.add_argument("--adapter", help="Use this proof adapter instead of adding a common hint")
    args = parser.parse_args()
    source = args.file.read_text()
    if args.table == "cns-edges" and not args.adapter:
        parser.error("CNS type proofs need the observer enabled; select a row-only adapter")
    args.file.write_text(use_preservation_adapter(source, args.table, args.adapter)
                         if args.adapter else add_preservation_frame_hints(source, args.table))
