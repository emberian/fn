#!/usr/bin/env python3
"""Rewrite the cursor's six conditional storage holds to their actual union.

The article window and physical bundle have distinct release paths but share
one storage-window rank. This edits only the declared holds, never budgets.
"""
from lisp_rewrite import parse, match, write

def transform(text):
    parsed = parse(text)
    old = match('(query-bundle :held)', parsed.forms)
    if len(old) != 6:
        raise ValueError('expected exactly six cursor bundle storage holds')
    return write(text, [(m.start, m.end, '(storage :held)') for m in old])
