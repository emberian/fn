#!/usr/bin/env python3
"""No raw host macro is used before its definition (lane ops-fixes, 2026-09-27).

    python3 tools/host_macro_order_check.py [FILE ...]

The native image `load`s host/native/*.lisp in host/native/build.lisp's
order, compiling each form as it goes.  A form that names a macro defined
later in load order compiles as a FUNCTION call: its arguments are evaluated
and the macro's name is called.  Batch AW moved a use of
`(fnn-log-with-kernel (log) ...)` above the macro in host/native/io.lisp:
`(log)` was evaluated as CL:LOG with no arguments, and every start of a
format-9 store with committed records faulted with "invalid number of
arguments: 0" (exit 4, the node could not restart after its first post).
SBCL warns about the undefined function at load; the build does not stop.

With no FILE, the files are build.lisp's `(load "host/native/X.lisp")`
lines in order.  Strings and comments are blanked before the scan.  Exit 0
when every macro use follows its definition, 1 with each early use named
(FILE:LINE, the macro, where it is defined).
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "host" / "native" / "build.lisp"


def blank(text: str) -> str:
    """TEXT with string contents, `;' comments and #| |# blocks replaced by
    spaces (newlines kept), so offsets and line numbers are unchanged."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
        elif c == "#" and i + 1 < n and text[i + 1] == "\\":
            # A character object: #\( or #\; or #\" is not syntax.
            for k in range(i, min(i + 3, n)):
                out[k] = " "
            i += 3
        elif c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif c == "#" and i + 1 < n and text[i + 1] == "|":
            j = text.find("|#", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def load_order():
    text = BUILD.read_text(errors="replace")
    return [ROOT / m.group(1) for m in
            re.finditer(r'\(load "(host/native/[^"]+\.lisp)"\)', blank_keep_strings(text))]


def blank_keep_strings(text: str) -> str:
    """Only comments removed (the load lines' paths are strings)."""
    return re.sub(r";[^\n]*", "", text)


def check(files):
    sources = [(f, blank(f.read_text(errors="replace"))) for f in files]
    defs = {}
    for index, (f, text) in enumerate(sources):
        for m in re.finditer(r"\(defmacro\s+([^\s()]+)", text):
            defs.setdefault(m.group(1).lower(), (index, m.start(), f, text.count("\n", 0, m.start()) + 1))
    early = []
    for name, (dindex, doffset, dfile, dline) in sorted(defs.items()):
        pattern = re.compile(r"\(" + re.escape(name) + r"(?=[\s()])", re.I)
        for index, (f, text) in enumerate(sources[:dindex + 1]):
            for m in pattern.finditer(text):
                if index == dindex and m.start() >= doffset:
                    break
                early.append("%s:%d uses %s before its definition at %s:%d" % (
                    shown(f), text.count("\n", 0, m.start()) + 1, name, shown(dfile), dline))
    return early


def shown(path: Path):
    try:
        return path.resolve().relative_to(ROOT)
    except ValueError:
        return path


def main(argv=None):
    args = argv if argv is not None else sys.argv[1:]
    files = [Path(a) for a in args] or load_order()
    early = check(files)
    for line in early:
        print("macro used early:", line)
    if not early:
        print("host_macro_order_check: %d files, every macro use follows its definition"
              % len(files))
    return 1 if early else 0


if __name__ == "__main__":
    sys.exit(main())
