#!/usr/bin/env python3
"""No raw host function is defined twice (lane commit-onto-log, 2026-09-27).

    python3 tools/host_defun_check.py [FILE ...]

The native image `ld`s every host/native/*.lisp into one package; a second
`(defun NAME` for a name already defined silently replaces the first (SBCL
warns once at load, the build does not stop).  Batch AU landed two
`fnn-log-line`s in host/native/io.lisp: w6-log-core's log-verb helper
(WHAT LOG SIZE) replaced the service-log writer (LINE), and every owner
crashed at its first service-log line.  A defstruct's accessors count as
definitions (`(defstruct (fnn-log ...) path fd unit ...)` defines
fnn-log-unit), which is how a later `(defun fnn-log-unit ()` collides.

Exit 0 when every name is defined once, 1 with each duplicate named.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def definitions(path: Path):
    text = path.read_text(errors="replace")
    for m in re.finditer(r"^\((?:defun|defmacro|defgeneric) ([^\s()]+)", text, re.M):
        yield m.group(1).lower(), path, text.count("\n", 0, m.start()) + 1
    for m in re.finditer(r"^\(defstruct \(([^\s()]+)((?:.|\n)*?)\)\n((?:.|\n)*?)\)\s*\n\n", text, re.M):
        name, body = m.group(1).lower(), m.group(3)
        line = text.count("\n", 0, m.start()) + 1
        body = re.sub(r";[^\n]*", "", body)
        depth, slots, tok = 0, [], ""
        for ch in body:
            if ch == "(":
                depth += 1
                if depth == 1:
                    tok = ""
                continue
            if ch == ")":
                depth -= 1
                if depth == 0 and tok.strip():
                    slots.append(tok.strip().split()[0])
                    tok = ""
                continue
            if depth == 1:
                tok += ch
            elif depth == 0:
                if ch.isspace():
                    if tok.strip():
                        slots.append(tok.strip())
                    tok = ""
                else:
                    tok += ch
        if depth == 0 and tok.strip():
            slots.append(tok.strip())
        for slot in slots:
            if re.fullmatch(r"[a-z0-9*+-]+", slot.lower()):
                yield "%s-%s" % (name, slot.lower()), path, line


def shown(path: Path):
    try:
        return path.resolve().relative_to(ROOT)
    except ValueError:
        return path


def main(argv=None):
    # The build scripts (build.lisp, build-dtn.lisp, ...) are alternative
    # image entries, each defining its own fn-native-entry: not one image.
    files = [Path(a) for a in (argv or sys.argv[1:])] or sorted(
        p for p in (ROOT / "host/native").glob("*.lisp") if not p.name.startswith("build"))
    seen, dups = {}, []
    for f in files:
        for name, path, line in definitions(f):
            if name in seen:
                dups.append("%s: %s:%d and %s:%d" % (name, seen[name][0], seen[name][1],
                                                    shown(path), line))
            else:
                seen[name] = (shown(path), line)
    for d in dups:
        print("defined twice:", d)
    return 1 if dups else 0


if __name__ == "__main__":
    sys.exit(main())
