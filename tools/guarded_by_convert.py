#!/usr/bin/env python3
"""Convert `guarded-by:' comment contracts on host globals to declarations.

A lock contract written as a comment beside a defvar was bound to the
variable by position (tools/lock_discipline_check.py read the defvar's own
line and the two after it), so moving a defvar re-targeted the comment
silently (CONVERGE-2 row 31: *fnn-extent-image-id* moved to io.lisp and the
owner-mutex contract it had been sitting beside fell to
*fnn-extent-checkpoint-id*).  The contract is now a form that names its
variable, (fnn-guarded-by VAR LOCK) (host/native/io.lisp), which the checker
reads; a comment contract left beside a defvar is a checker problem.

For each top-level defvar/defparameter in host/native/*.lisp whose contract
comment the checker's position rule binds today, this tool inserts
(fnn-guarded-by VAR LOCK) on the line after the defvar form and strips the
`guarded-by: LOCK' words from the comment, keeping the rest of it byte for
byte.  It REFUSES, with a named reason, a contract it cannot convert
faithfully, and prints those as the residual for a person to decide:
  - self: the comment binds to the lock variable itself (a comment written
    above the variable it meant, between the lock's defvar and the next);
  - lock: the lock text names no lock global and is not the owner mutex;
  - unbound: a top-level `guarded-by:' comment the position rule binds to
    no defvar.

    python3 tools/guarded_by_convert.py            # dry run: what it would do
    python3 tools/guarded_by_convert.py --write    # rewrite the files
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import lisp_source  # noqa: E402

GUARDED = re.compile(r"guarded-by:\s*([^(;]+?)\s*(?:\(|\.\s|\.$|$)")
DEFVAR = re.compile(r"\((defvar|defparameter)\s+(\S+)", re.I)
OWNER_MUTEX = ("the owner mutex", "owner mutex")
OWNER_LOCK_FORM = "(fnn-owner-service-lock)"
LOCK_GLOBAL = re.compile(r"^\*[a-z0-9-]+\*$")


def lock_form(text: str) -> str | None:
    text = text.strip().rstrip(".")
    if text in OWNER_MUTEX:
        return OWNER_LOCK_FORM
    if LOCK_GLOBAL.match(text):
        return text
    return None


def strip_contract(line: str, match: re.Match) -> str | None:
    """LINE with the words `guarded-by: LOCK' (and a following `.  ') removed;
    None when nothing but comment markers would be left."""
    start, end = match.start(), match.end(1)
    rest = line[end:]
    rest = re.sub(r"^\.\s*", "", rest) if rest.startswith(".") else rest.lstrip()
    head = re.sub(r",\s*$", "", line[:start])   # "...len), guarded-by: X" keeps "...len)"
    new = (head + rest).rstrip()
    if re.fullmatch(r"\s*;+\s*", new) or not new.strip():
        return None
    if re.fullmatch(r".*\S\s+;+", new):          # a trailing comment emptied
        return re.sub(r"\s+;+$", "", new)
    return new


def plan_file(text: str):
    """(edits, residual) for one file's TEXT.  An edit is (defvar line index,
    insertion after line index, var, lock form, comment line index, new
    comment line or None)."""
    lines = text.split("\n")
    edits, residual, bound_lines = [], [], set()
    for start, end in lisp_source.form_spans(text):
        m = DEFVAR.match(text, start)
        if not m or (start > 0 and text[start - 1] != "\n"):
            continue
        var = m.group(2).lower()
        first = text.count("\n", 0, start)
        last = text.count("\n", 0, end)
        found = None
        # the checker's rule: the defvar's own line, then the two after it,
        # stopping at the next form
        for k in range(first, min(first + 3, len(lines))):
            g = GUARDED.search(lines[k])
            if g and (k == first or lines[k].lstrip().startswith(";")):
                found = (k, g)
                break
            if k > first and lines[k].lstrip().startswith("("):
                break
        if not found:
            continue
        k, g = found
        bound_lines.add(k)
        lock_text = g.group(1).strip().rstrip(".")
        form = lock_form(lock_text)
        if form is None:
            residual.append((k + 1, var, f"lock: `{lock_text}' names no lock global"))
            continue
        if form == var:
            residual.append((k + 1, var, "self: the comment binds to the lock itself "
                                         "(it was written above the variable it meant)"))
            continue
        edits.append((first, last, var, form, k, strip_contract(lines[k], g)))
    for k, line in enumerate(lines):
        if k not in bound_lines and line.startswith(";") and GUARDED.search(line):
            residual.append((k + 1, None, "unbound: no defvar takes this comment by position"))
    return edits, residual


def apply(text: str, edits) -> str:
    lines = text.split("\n")
    out = list(lines)
    # bottom-up so indices stay valid
    for first, last, var, form, k, new in sorted(edits, key=lambda e: -max(e[1], e[4])):
        if new is None:
            del out[k]
            if k <= last:
                last -= 1
        else:
            out[k] = new
        insert_at = last + 1
        out.insert(insert_at, f"(fnn-guarded-by {var} {form})")
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--root", default=str(ROOT))
    args = ap.parse_args(argv)
    root = Path(args.root)
    total, residual_count = 0, 0
    for path in sorted((root / "host" / "native").glob("*.lisp")):
        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8")
        edits, residual = plan_file(text)
        for first, last, var, form, k, new in edits:
            print(f"{rel}:{first + 1}: (fnn-guarded-by {var} {form})")
        for line, var, why in residual:
            print(f"{rel}:{line}: RESIDUAL {var or '-'}: {why}")
        total += len(edits)
        residual_count += len(residual)
        if args.write and edits:
            path.write_text(apply(text, edits), encoding="utf-8")
    print(f"guarded_by_convert: {total} contract(s) {'converted' if args.write else 'to convert'}, "
          f"{residual_count} residual")
    return 0


if __name__ == "__main__":
    sys.exit(main())
