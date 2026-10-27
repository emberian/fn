#!/usr/bin/env python3
"""Find the witnesses in `tests/acl2/` that do not bite.

`AGENTS.md` says a keystone ships with "a reachable non-degenerate witness and
one `must-fail` case per hypothesis showing the conclusion fails without it",
and that "a separating witness must separate predicates by more than their
weakest clause".  Nothing enforced that, and on 2026-09-20 three lanes each
found, by accident, a test that passed while proving nothing:

* `tests/acl2/owner-tests` asserted a durable outcome leaves the connection
  list UNCHANGED.  True only because `fn-own-conn-boundedp` was false of every
  connection, so the test pinned the defect and passed for as long as it lived.
* The S4-1 and S5-1 hostile-batch witnesses of `tests/acl2/stx-transit-tests`
  built both carriers with a prose body, so `fn-stx-delta` was `NIL` and every
  assertion held of an EMPTY delta.
* `fn-served-submission-of-append` and `fn-cpp-find-of-append` were false and
  had counterexamples, found only when a neighbouring proof reached them.

None of the three is visible to a reader of the source: each needs the VALUE.
So this tool evaluates.  `tools/ledger.py` is deliberately the other thing --
its docstring promises that "nothing is interned, evaluated, or macro-expanded,
so reading a book cannot run a book", and its teeth-form lint is a shape test
on `must-fail` bodies.  Putting an ACL2-running check inside it would break
that promise for every caller of `make check`.  This is a separate tool that
imports the ledger's reader and adds the evaluation the ledger may not do.

    python3 tools/teeth_check.py                  # static pass, no ACL2
    python3 tools/teeth_check.py --evaluate       # one ACL2 per test book
    python3 tools/teeth_check.py --evaluate tests/acl2/owner-tests.lisp
    python3 tools/teeth_check.py --report         # static + the saved values
    python3 tools/teeth_check.py --summary        # the counts `make check` prints
    python3 tools/teeth_check.py --table          # macro-generated teeth, marked apart
    python3 tools/teeth_check.py --null-witness   # an empty-result assertion with no non-empty witness
    python3 tools/teeth_check.py --must-fail      # no bare must-fail in tests/acl2 (--convert rewrites)

DEFKEYSTONE, DEFTEETH.  `(defkeystone NAME ...)` and `(defteeth NAME ...)`
(books/defkeystone.lisp, TEETH CONTRACT v1) are the macros from another book
this tool expands, through the ledger's `defkeystone_expansion` and
`defteeth_expansion`, from the form's declared :claim (the world checks the
claim against the theorem at certification): their positive, removal,
mutant, corrupted-state and bound witnesses are read as the assert-events
they expand to, and `--table` lists the keystone, its bounds and its
must-fails (under :must-fail t) with the MACRO's name.  A `defteeth` form is
a structural citation of its keystone, so the section convention below is
exact for it.  Coverage classes (generated, hand, exemptions, underived
bounds) are tools/keystone_emit.py's, from the obligation manifest.

MACRO-GENERATED TEETH.  A book may write its witnesses through a `defmacro`
that expands to one `defthm` -- `feed-connection-teeth-tests.lisp` admits a
keystone once through such a macro and then calls it again under `must-fail`,
once per hypothesis, so a must-fail that fails for the wrong reason is caught
by the same hints that prove the keystone.  A reader of the SOURCE alone
cannot see this: the sixteen must-fails of that book are sixteen calls of
three macros, and none of them is the literal text `must-fail` at the call
site for thirteen of them.  This tool reads each book's own top-level
`defmacro` forms and, for a macro whose template either submits a `must-fail`
itself or is wrapped in one at the call site, counts each call as one tooth,
attributed to the theorem name the call gives it -- never to a macro defined
in a DIFFERENT book, and never to a `must-fail` a macro only mentions inside
a comment or a string, since neither reaches the reader as a form.  `--table`
lists them, and the book's own literal (non-macro) `must-fail` forms beside
them, marked apart.

The static pass needs no ACL2 and is what `make check` runs.  `--evaluate`
writes `build/teeth/values.json`; `--report` reads it back, so the expensive
half runs when a lane asks for it and its findings survive in one file.

WHAT IT CANNOT SEE.  A flag is a question for a human, never a verdict.

* It evaluates witnesses in the world the book itself builds.  A book whose
  `include-book` fails evaluates nothing, and is reported `prefix-failed`
  rather than clean.
* "Degenerate" is a property of the printed value, not of the intent.  A
  refusal test SHOULD assert `NIL`; the tool cannot tell an asserted refusal
  from an accidental one, so it reports the pair (the claim, the value) and
  leaves the reading to the reader.
* It says nothing about whether a theorem is TRUE, whether a hypothesis is
  necessary, or whether a witness is the RIGHT witness for its keystone.
* `assert-event` bodies are ground, so every probe is ground.  A property
  under a quantifier, or a `defthm` in a test book, is out of scope.
"""
from __future__ import annotations
import argparse
import collections
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402
def code_mask(text: str) -> list[bool]:
    """True at each character that is Lisp code (not comment, string or
    character literal)."""
    mask = [True] * len(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = False
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = False
            i = j + 1
        elif text.startswith("#|", i):
            j = text.find("|#", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                mask[k] = False
            i = j
        elif text.startswith("#\\", i):
            for k in range(i, min(i + 3, n)):
                mask[k] = False
            i += 3
        else:
            i += 1
    return mask


