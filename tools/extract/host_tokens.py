#!/usr/bin/env python3
"""tools/extract/host_tokens.py TREE OUT.lsp -- every word of the host files
the image loads raw (host/native/build.lisp's progn! block), upcased, as an
ACL2 list of strings: the candidates for the Common Lisp product's roots
(tools/extract/core-export.lisp keeps those that name a world function or
defconst).  Comments and strings are skipped."""
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


def tokens(tree, build="host/native/build.lisp"):
    toks = set()
    for rel in core_build.host_files(tree, build):
        s = strip((tree / rel).read_text(errors="replace"))
        toks |= set(t.upper() for t in re.findall(r"(?<![\w:])([A-Za-z*$][A-Za-z0-9$*+<>=/-]*)", s))
    return sorted(toks)


if __name__ == "__main__":
    tree, out = Path(sys.argv[1]), Path(sys.argv[2])
    toks = tokens(tree, sys.argv[3] if len(sys.argv) > 3 else "host/native/build.lisp")
    out.write_text("(" + "\n".join('"%s"' % t for t in toks) + ")\n")
    print("host_tokens: %d words" % len(toks))
