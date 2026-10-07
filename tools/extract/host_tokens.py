#!/usr/bin/env python3
"""tools/extract/host_tokens.py TREE OUT.lsp -- the words of the host files
the selected native build loads raw (its progn! block), upcased, as an
ACL2 list of strings: the candidates for the Common Lisp product's roots
(tools/extract/forms-export.lisp keeps those that name a world function,
stobj or defconst). Comments and strings are skipped. Optional third
argument BUILD selects the native build script; default
host/native/build.lisp.

Which words: fn's own names (FN..., *FN...*, CREATE-...) wherever they
appear, since the host names them as quoted data for fnn-call dispatch too;
any other word only where the host APPLIES it -- the head of a form `(w',
`#'w' or a quoted `'w'.  A word the host uses only as a variable or a
keyword-like name (an `ev' parameter, an flet's `fmt') would otherwise root
the ACL2 function of the same name: `ev' rooted ACL2's evaluator
(tools/extract/closure_why.py, 2026-10-07)."""
import re
import sys
from pathlib import Path

import core_build


def strip(s):
    """The text with comments, strings and character literals blanked (one
    pass, so a quote in a comment or a semicolon in a string is read right)."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c == ";":
            j = s.find("\n", i)
            i = n if j < 0 else j
        elif s.startswith("#|", i):
            j = s.find("|#", i + 2)
            i = n if j < 0 else j + 2
        elif s.startswith("#\\", i):
            i += 3
            while i < n and s[i].isalnum():
                i += 1
            out.append(" ")
        elif c == '"':
            i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1
            out.append(" ")
        else:
            out.append(c)
            i += 1
    return "".join(out)


WORD = r"([A-Za-z*$][A-Za-z0-9$*+<>=/-]*)"
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ledger  # noqa: E402  (tools/ledger.py: the non-evaluating reader)
from ledger import Sym  # noqa: E402


def own(word):
    """fn's own name: FN..., *FN..., or a stobj creator CREATE-..."""
    return word.lstrip("*").startswith("FN") or word.startswith("CREATE-")


def _word(x):
    """X's token, or None for a keyword, a package-qualified symbol or a reader object."""
    if not isinstance(x, Sym) or not x or x[0] in ":#&" or ":" in x or not re.fullmatch(WORD, str(x)):
        return None
    return str(x).upper()


LAMBDA_HEADS = {"lambda"}
DEF_HEADS = {"defun", "defmacro", "defun-inline", "defun-notinline", "defn", "defmethod"}
BIND_HEADS = {"let", "let*", "symbol-macrolet"}
FUN_BIND_HEADS = {"flet", "labels", "macrolet"}
LL_EXPR_HEADS = {"destructuring-bind", "multiple-value-bind"}


def _walk(x, words, applied, quoted=False):
    w = _word(x)
    if w:
        words.add(w)
        return
    if not isinstance(x, list) or not x:
        return
    if quoted:
        for y in x:
            _walk(y, words, applied, True)
        return
    h = _word(x[0])
    hl = h.lower() if h else None
    rest = x[1:]
    if hl == "quote":
        if rest and _word(rest[0]):
            applied.add(_word(rest[0]))
        for y in rest:
            _walk(y, words, applied, True)
    elif hl == "function":
        if rest and _word(rest[0]):
            applied.add(_word(rest[0]))
        else:
            for y in rest:
                _walk(y, words, applied)
    elif hl == "declare":
        return
    elif hl in DEF_HEADS and len(x) >= 3:
        _walk(x[1], words, applied, True)
        _lambda_list(x[2], words, applied)
        for y in x[3:]:
            _walk(y, words, applied)
    elif hl in LAMBDA_HEADS and len(x) >= 2:
        _lambda_list(x[1], words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    elif hl in BIND_HEADS and len(x) >= 2 and isinstance(x[1], list):
        for b in x[1]:
            if isinstance(b, list):
                for y in b[1:]:
                    _walk(y, words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    elif hl in FUN_BIND_HEADS and len(x) >= 2 and isinstance(x[1], list):
        for d in x[1]:
            if isinstance(d, list) and len(d) >= 2:
                _lambda_list(d[1], words, applied)
                for y in d[2:]:
                    _walk(y, words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    elif hl in LL_EXPR_HEADS and len(x) >= 3:
        _lambda_list(x[1], words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    elif hl in ("dolist", "dotimes") and len(x) >= 2 and isinstance(x[1], list):
        for y in x[1][1:]:
            _walk(y, words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    elif hl == "handler-case" and len(x) >= 2:
        _walk(x[1], words, applied)
        for c in x[2:]:
            if isinstance(c, list):
                for y in c[2:]:
                    _walk(y, words, applied)
    elif hl and hl.startswith("with-") and len(x) >= 2 and isinstance(x[1], list) and x[1] \
            and _word(x[1][0]):
        for y in x[1][1:]:
            _walk(y, words, applied)
        for y in x[2:]:
            _walk(y, words, applied)
    else:
        if h:
            applied.add(h)
            rest = x[1:]
        else:
            rest = x
        for y in rest:
            _walk(y, words, applied)


def _lambda_list(ll, words, applied):
    """A lambda list binds its symbols; only its default forms are code."""
    if not isinstance(ll, list):
        return
    for p in ll:
        if isinstance(p, list):
            for y in p[1:]:
                _walk(y, words, applied)


def file_tokens(text):
    try:
        forms = ledger.read_forms(text)
    except ledger.ReadError as error:
        # unreadable: every word, as before (a superset of the roots is safe)
        print("host_tokens: unreadable, every word kept: %s" % error, file=sys.stderr)
        return set(t.upper() for t in re.findall(r"(?<![\w:])" + WORD, strip(text)))
    words, applied = set(), set()
    for f in forms:
        _walk(f, words, applied)
    return {w for w in words if own(w)} | applied


def tokens(tree, build="host/native/build.lisp"):
    toks = set()
    for rel in core_build.host_files(tree, build):
        toks |= file_tokens((tree / rel).read_text(errors="replace"))
    return sorted(toks)


if __name__ == "__main__":
    tree, out = Path(sys.argv[1]), Path(sys.argv[2])
    toks = tokens(tree, sys.argv[3] if len(sys.argv) > 3 else "host/native/build.lisp")
    out.write_text("(" + "\n".join('"%s"' % t for t in toks) + ")\n")
    print("host_tokens: %d words" % len(toks))
