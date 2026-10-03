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
    # A defstruct's accessors, read as an s-expression over the comment- and
    # string-masked text (2026-10-03: the regex that ended a defstruct at the
    # next blank line slurped the forms after one with no blank line under
    # it, and a one-line `(defstruct (name (:constructor ...))' read as
    # options to the end of the line: host/native/snapshot-producer.lisp
    # "defined" fnn-snapshot-job-and, -that, ... twice at one line).
    sys.path.insert(0, str(ROOT / "tools"))
    import must_fail_check  # the one Lisp comment/string mask in tools/
    mask = must_fail_check.code_mask(text)
    for m in re.finditer(r"^\(defstruct\b", text, re.M):
        items = top_level_items(text, mask, m.start())
        if len(items) < 2:
            continue
        head = items[1]
        name = (head[1:].split()[0] if head.startswith("(") else head).lower()
        conc = re.search(r"\(:conc-name\s+([^\s()]+)\)", head) if head.startswith("(") else None
        prefix = conc.group(1).lower() if conc else name + "-"
        line = text.count("\n", 0, m.start()) + 1
        for item in items[2:]:
            if item.startswith('"'):
                continue
            slot = item[1:].split()[0] if item.startswith("(") else item
            if re.fullmatch(r"[a-z0-9*+-]+", slot.lower()):
                yield prefix + slot.lower(), path, line


def top_level_items(text: str, mask, start: int) -> list[str]:
    """The top-level elements of the form opening at START, as source text
    (a list element whole, a string whole); code outside comments only."""
    items, depth, i, n, begin = [], 0, start, len(text), None
    while i < n:
        c = text[i]
        if not mask[i]:
            if c == '"' and depth == 1 and begin is None:
                j = i
                while j < n and not mask[j]:
                    j += 1
                items.append(text[i:j])
                i = j
                continue
            i += 1
            continue
        if c == "(":
            depth += 1
            if depth == 2:
                begin = i
        elif c == ")":
            if depth == 2 and begin is not None:
                items.append(text[begin:i + 1])
                begin = None
            depth -= 1
            if depth == 0:
                break
        elif depth == 1 and not c.isspace():
            j = i
            while j < n and mask[j] and not text[j].isspace() and text[j] not in "()":
                j += 1
            items.append(text[i:j])
            i = j
            continue
        i += 1
    return items


def shown(path: Path):
    try:
        return path.resolve().relative_to(ROOT)
    except ValueError:
        return path


def main(argv=None):
    # The build scripts (build.lisp, build-dtn.lisp, ...) are alternative
    # image entries, each defining its own fn-native-entry: not one image.
    # A parked file (planning/host-parked.json) is loaded by no image, so it
    # cannot collide with what one loads; host_loaded_check keeps it out.
    import json
    parked_path = ROOT / "planning" / "host-parked.json"
    parked = (set(json.loads(parked_path.read_text()).get("parked", {}))
              if parked_path.exists() else set())
    files = [Path(a) for a in (argv or sys.argv[1:])] or sorted(
        p for p in (ROOT / "host/native").glob("*.lisp") if not p.name.startswith("build")
        and str(p.relative_to(ROOT)) not in parked)
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
