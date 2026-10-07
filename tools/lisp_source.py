#!/usr/bin/env python3
"""One reader for the Common Lisp / ACL2 source text the checkers read.

Every checker that reads books/ or host/ goes through this module rather than
its own paren counter.  The ad-hoc readers it replaces disagreed on the
lexical cases that matter: a character literal (`#\\"', `#\\(', `#\\;'), a
`#| |#' block comment (nesting), a `|...|' escaped symbol, and a string's
backslash escapes.  reach_check's form splitter, for one, took the `#\\"' at
host/store-write-host.lisp:160 as the start of a string and lost the file's
last 115 definitions.

What it reads is the text, positions kept: top-level forms as source slices
(`forms'), the code with comments and strings blanked (`code_only'), and the
first s-expression as nested lists of atoms (`read_sexp').  It evaluates no
reader macro beyond these lexical ones; a `#.' or `#+' form is read as the
plain tokens that follow it, which is what every caller wants (they ask what
the text names, not what a Lisp would build from it).

    python3 tools/lisp_source.py FILE...   # print each file's form count
"""
from __future__ import annotations

import sys

# A token ends at whitespace or one of these (CL's terminating macro chars).
_TERMINATORS = frozenset("()\";'`,")
_WHITESPACE = frozenset(" \t\n\r\f\v")


def _string_end(text: str, i: int) -> int:
    """TEXT[i] is the opening `"'; the index just past the closing one."""
    n = len(text)
    i += 1
    while i < n and text[i] != '"':
        i += 2 if text[i] == "\\" else 1
    return min(i + 1, n)


def _escaped_symbol_end(text: str, i: int) -> int:
    """TEXT[i] is an opening `|' of an escaped symbol; just past its close."""
    n = len(text)
    i += 1
    while i < n and text[i] != "|":
        i += 2 if text[i] == "\\" else 1
    return min(i + 1, n)


def _block_comment_end(text: str, i: int) -> int:
    """TEXT[i:i+2] is `#|'; just past the matching `|#' (blocks nest, as in CL)."""
    n, depth = len(text), 0
    while i < n:
        if text.startswith("#|", i):
            depth += 1
            i += 2
        elif text.startswith("|#", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    return n


def _char_literal_end(text: str, i: int) -> int:
    """TEXT[i:i+2] is `#\\'; just past the literal.  The character after the
    backslash is always part of it (`#\\(', `#\\"', `#\\ '); a name follows
    only an alphabetic first character (`#\\Space', `#\\Newline')."""
    n = len(text)
    j = i + 3
    if i + 2 < n and text[i + 2].isalpha():
        while j < n and text[j] not in _WHITESPACE and text[j] not in _TERMINATORS:
            j += 1
    return min(j, n)


def _atom_end(text: str, i: int) -> int:
    """TEXT[i] starts an atom; just past it (a `|...|' part is kept whole)."""
    n = len(text)
    while i < n:
        c = text[i]
        if c in _WHITESPACE or c in _TERMINATORS:
            return i
        if c == "|":
            i = _escaped_symbol_end(text, i)
        elif c == "\\":
            i += 2
        else:
            i += 1
    return n


def tokens(text: str):
    """(kind, start, end) over TEXT, kind one of open, close, quote (', `, ,
    ,@), string, comment, atom.  Whitespace yields nothing."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in _WHITESPACE:
            i += 1
        elif c == ";":
            end = text.find("\n", i)
            end = n if end < 0 else end
            yield ("comment", i, end)
            i = end
        elif c == "#" and text.startswith("#|", i):
            end = _block_comment_end(text, i)
            yield ("comment", i, end)
            i = end
        elif c == "#" and text.startswith("#\\", i):
            end = _char_literal_end(text, i)
            yield ("atom", i, end)
            i = end
        elif c == '"':
            end = _string_end(text, i)
            yield ("string", i, end)
            i = end
        elif c == "(":
            yield ("open", i, i + 1)
            i += 1
        elif c == ")":
            yield ("close", i, i + 1)
            i += 1
        elif c in "'`":
            yield ("quote", i, i + 1)
            i += 1
        elif c == ",":
            end = i + 2 if text.startswith(",@", i) else i + 1
            yield ("quote", i, end)
            i = end
        elif c == "#" and text.startswith("#(", i):
            # A vector literal: its `(' is the open token.
            i += 1
        elif c == "#" and text.startswith("#'", i):
            yield ("quote", i, i + 2)
            i += 2
        else:
            end = max(_atom_end(text, i), i + 1)
            yield ("atom", i, end)
            i = end


def code_only(text: str) -> str:
    """TEXT with `;' comments removed up to (not including) the newline,
    and each `#| |#' block and each string literal replaced by one space.
    Character literals and escaped symbols are code and are kept."""
    out, last = [], 0
    for kind, start, end in tokens(text):
        if kind == "comment" or kind == "string":
            out.append(text[last:start])
            if kind == "string" or text.startswith("#|", start):
                out.append(" ")
            last = end
    out.append(text[last:])
    return "".join(out)


def form_spans(text: str) -> list[tuple[int, int]]:
    """(start, end) of each top-level parenthesized form of TEXT."""
    spans, depth, start = [], 0, None
    for kind, s, e in tokens(text):
        if kind == "open":
            if depth == 0:
                start = s
            depth += 1
        elif kind == "close" and depth > 0:
            depth -= 1
            if depth == 0 and start is not None:
                spans.append((start, e))
                start = None
    return spans


def forms(text: str) -> list[str]:
    """Top-level parenthesized forms of TEXT, as source slices."""
    return [text[s:e] for s, e in form_spans(text)]


def read_sexp(text: str):
    """The first s-expression of TEXT as nested lists of lower-cased atom
    strings, strings and comments dropped.  A quote mark reads as the Lisp
    reader reads it: 'x is ["quote", x], #'f is ["function", f], `x
    ["quasiquote", x], ,x ["unquote", x], ,@x ["unquote-splicing", x].
    None if TEXT has no atom or list."""
    marks = {"'": "quote", "#'": "function", "`": "quasiquote",
             ",": "unquote", ",@": "unquote-splicing"}
    stack: list[list] = [[]]
    pending: list[list] = [[]]   # per level: quote marks awaiting their datum

    def put(datum):
        while pending[-1]:
            datum = [pending[-1].pop(), datum]
        stack[-1].append(datum)

    for kind, s, e in tokens(text):
        if kind == "open":
            stack.append([])
            pending.append([])
        elif kind == "close":
            if len(stack) == 1:
                continue
            done = stack.pop()
            pending.pop()
            put(done)
            if len(stack) == 1:
                return stack[0][0]
        elif kind == "quote":
            pending[-1].append(marks[text[s:e]])
        elif kind == "atom":
            put(text[s:e].lower())
            if len(stack) == 1:
                return stack[0][0]
    return stack[0][0] if stack[0] else None


def line_of(text: str, offset: int) -> int:
    """1-based line number of OFFSET in TEXT."""
    return text.count("\n", 0, offset) + 1


def main(argv: list[str]) -> int:
    for path in argv:
        with open(path, encoding="utf-8", errors="surrogateescape") as handle:
            print(f"{path}: {len(forms(handle.read()))} forms")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
