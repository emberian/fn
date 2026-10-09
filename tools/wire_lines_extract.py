#!/usr/bin/env python3
"""Extract wire-grammar's existing framing events, without rewriting a form.

One-time structural transformation for OWNER-CARRIER-GLOBALS Round 4.
The shared framing book avoids importing the complete grammar's general
rewrite rules into every FN-Statement consumer. Refuses missing/duplicate
names before returning any output. The caller writes the two books.
"""
try:
    from . import lisp_rewrite as lr
except ImportError:
    import lisp_rewrite as lr

NAMES = '''fn-wg-take fn-wg-drop fn-wg-prefixp fn-wg-app
fn-wg-len-of-drop fn-wg-len-of-take fn-wg-len-of-app fn-wg-app-is-append
fn-wg-app-assoc fn-wg-take-of-app fn-wg-drop-of-app fn-wg-prefixp-of-app
fn-wg-app-take-drop fn-wg-prefixp-app-drop fn-wg-prefixp-len
fn-wg-true-listp-of-take fn-wg-take-of-len
fn-wg-true-listp-of-app fn-wg-octets-of-app fn-wg-app-nil fn-wg-consp-of-app
fn-wg-octets-of-take fn-wg-octets-of-drop fn-wg-true-listp-of-drop
fn-wg-drop-of-app-longer fn-wg-true-list-fix-of-take fn-wg-consp-of-drop
fn-wg-lines fn-wg-unlines
fn-wg-lines-octets fn-wg-lines-consp fn-wg-lines-len-positive
fn-wg-unlines-of-lines'''.split()


def extract(text, names):
    parsed = lr.parse(text)
    found = []
    for name in names:
        matches = lr.match(None, parsed.forms, name=name, deep=False)
        if len(matches) != 1:
            raise ValueError(f"{name}: expected one top-level event, got {len(matches)}")
        found.append(matches[0])
    if len({m.start for m in found}) != len(found):
        raise ValueError("repeated event name")
    rest = lr.write(text, [(m.start, m.end, "") for m in found])
    forms = [text[m.start:m.end] for m in found]
    return rest, forms


def transform(text):
    rest, forms = extract(text, NAMES)
    body = []
    for name, form in zip(NAMES, forms):
        if name == 'fn-wg-lines-octets':
            body.append('(local (defthm fn-wg-consp-when-len-positive\n'
                        '  (implies (< 0 (len x)) (consp x))))')
        body.append(form)
        if name == 'fn-wg-app-is-append':
            body.append('(in-theory (disable fn-wg-app-is-append))')
    header = '''; Shared total list helpers and CRLF framing from wire-grammar.
; Extracted without changing the function or theorem forms; the full grammar
; still includes these events. Statement transport needs only this layer.
(in-package "ACL2")
(include-book "cbor-invariants")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable fn-cbor-octet-listp)))

'''
    rest = rest.replace('(include-book "octet-text")',
                        '(include-book "octet-text")\n(include-book "wire-lines")')
    rest = rest.replace('(in-theory (disable fn-wg-app-is-append))', '')
    while '\n\n\n' in rest:
        rest = rest.replace('\n\n\n', '\n\n')
    return rest, header + '\n\n'.join(body) + '\n'


if __name__ == '__main__':
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    remainder, extracted = transform(args.source.read_text())
    args.destination.write_text(extracted)
    args.source.write_text(remainder)
