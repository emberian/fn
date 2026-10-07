#!/usr/bin/env python3
"""tools/generator_twin_check.py -- no NEW hand-written twin of a generator-shaped form.

A ratchet that only shrinks keeps the representation drain from regrowing
(ruling 1: generators are the design of record).  Over books/*.lisp, read with
tools/lisp_rewrite.py (nothing is interned or macro-expanded), it finds two
kinds of twin and fails (`--check`) on any book whose count exceeds
tools/generator_twin_baseline.json, and on any
baseline row above the book's count (a stale row is headroom for a new twin):

  octet-clone    a `defabsstobj'/`defstobj' that declares `:congruent-to fn-octets',
                 or a `defstobj' that is a field-for-field copy of fn-octets$c (one
                 resizable (unsigned-byte 8) array plus one (integer 0 *) fill) --
                 written by hand where `(def-buffer NAME)' (books/def-buffer.lisp)
                 generates it.  fn-octets itself is the generator's base and
                 exempt; a backquoted template (def-buffer's own expansion) is not
                 a form of the book.
  record-stobj   a `defabsstobj' whose :foundation is a `defstobj' written by hand
                 in some book.  The row is the book that holds the defstobj.  A
                 foundation `def-representation' emits is not in the source, so it
                 is not seen; fn-octets$c is the octet-clone case above.

The baseline rows are {book: {kinds, count, reason}}.  `--write-baseline' only
shrinks (tools/ratchet.py `refused'): raising or adding a row needs an ACKS.md
line `ratchet:generator_twin_check:<book>'.  A book the reader refuses
(`Unsupported': #. #+ ...) is reported by name and is a failure: a book that
cannot be read cannot be cleared.
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as lr  # noqa: E402
import ratchet  # noqa: E402

TOOL = "generator_twin_check"
BASELINE = ROOT / "tools" / "generator_twin_baseline.json"
OCTETS_BASE = {"fn-octets", "fn-octets$c"}


def _low(n):
    return n.low if isinstance(n, lr.Atom) and not isinstance(n, lr.Str) else None


def _forms(node):
    """Every list form inside NODE, skipping backquoted templates."""
    if isinstance(node, lr.Pre):
        if node.prefix.startswith("`"):
            return
        yield from _forms(node.node)
    elif isinstance(node, lr.Lst):
        yield node
        for i in node.items:
            yield from _forms(i)


def _kw(form, key):
    items = form.items
    for i, it in enumerate(items[:-1]):
        if _low(it) == key:
            return _low(items[i + 1])
    return None


def _is_u8_array(ft):
    return "(array (unsigned-byte 8)" in ft and ":resizable t" in ft


def _is_fill(ft):
    return "(integer 0 *)" in ft


def _field_copy(form, text):
    fields = [i for i in form.items[2:] if isinstance(i, lr.Lst)]
    if len(fields) != 2:
        return False
    a, b = (" ".join(text[f.start:f.end].lower().split()) for f in fields)
    return (_is_u8_array(a) and _is_fill(b)) or (_is_u8_array(b) and _is_fill(a))


def scan(books, root=ROOT):
    """(defstobjs {name: book}, defabs [(book, name, foundation, clone?)], octet [(book, name, why)],
    unreadable [(book, message)])."""
    defstobjs, absts, octet, bad = {}, [], [], []
    for p in books:
        text = p.read_text(encoding="utf-8", errors="surrogateescape")
        low = text.lower()
        if "defstobj" not in low and "defabsstobj" not in low:
            continue
        book = str(p.relative_to(root)) if p.is_absolute() and root in p.parents else str(p)
        try:
            parsed = lr.parse(text)
        except lr.ReadError as e:
            bad.append((book, f"{type(e).__name__}: {e}"))
            continue
        for top in parsed.forms:
            for f in _forms(top):
                head = _low(f.items[0]) if f.items else None
                name = _low(f.items[1]) if len(f.items) > 1 else None
                if head not in ("defstobj", "defabsstobj") or name is None:
                    continue
                if head == "defstobj":
                    defstobjs.setdefault(name, book)
                    if name not in OCTETS_BASE and _kw(f, ":congruent-to") == "fn-octets":
                        octet.append((book, name, "defstobj :congruent-to fn-octets"))
                    elif name not in OCTETS_BASE and _field_copy(f, parsed.text):
                        octet.append((book, name, "field-for-field copy of fn-octets$c"))
                else:
                    found = _kw(f, ":foundation")
                    if name not in OCTETS_BASE and _kw(f, ":congruent-to") == "fn-octets":
                        octet.append((book, name, "defabsstobj :congruent-to fn-octets"))
                    elif name not in OCTETS_BASE and found == "fn-octets$c":
                        octet.append((book, name, "defabsstobj over fn-octets$c"))
                    elif found and found not in OCTETS_BASE:
                        absts.append((book, name, found))
    return defstobjs, absts, octet, bad


def twins(books, root=ROOT):
    """({book: {"kinds": [...], "count": n}}, details, unreadable)."""
    defstobjs, absts, octet, bad = scan(books, root)
    rows, detail = {}, []

    def add(book, kind, what):
        r = rows.setdefault(book, {"kinds": [], "count": 0})
        if kind not in r["kinds"]:
            r["kinds"].append(kind)
        r["count"] += 1
        detail.append(f"{book}: {kind}: {what}")

    for book, name, why in octet:
        add(book, "octet-clone", f"{name} ({why})")
    for book, name, found in absts:
        if found in defstobjs:  # a hand defstobj; a generated foundation is not in the source
            add(defstobjs[found], "record-stobj", f"{found} (foundation of {name}, in {book})")
    for r in rows.values():
        r["kinds"].sort()
    return rows, sorted(detail), bad


def all_books(root=ROOT):
    return sorted((root / "books").glob("*.lisp"))


def load_baseline(path=BASELINE):
    return json.loads(Path(path).read_text())["rows"]


def new_rows(rows, baseline):
    return {b: r for b, r in sorted(rows.items()) if r["count"] > baseline.get(b, {}).get("count", 0)}


def write_baseline(rows, path=BASELINE, acks=None):
    """Shrink-only.  Returns refusals ([] when written).  A row keeps its reason."""
    path = Path(path)
    old = ratchet.old_rows(TOOL, path, lambda: load_baseline(path))
    refusals = ratchet.refused(TOOL, None if old is None else {b: r["count"] for b, r in old.items()},
                               {b: r["count"] for b, r in rows.items()}, acks)
    if refusals:
        return refusals
    out = {}
    for b, r in sorted(rows.items()):
        out[b] = {"kinds": r["kinds"], "count": r["count"],
                  "reason": (old or {}).get(b, {}).get("reason", "UNDECIDED: no reason recorded")}
    path.write_text(json.dumps({"comment": "shrink-only; regenerate with tools/generator_twin_check.py "
                                "--write-baseline (a raise needs an ACKS.md line)", "rows": out},
                               indent=1) + "\n")
    return []


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true", help="fail on any book not in the baseline")
    g.add_argument("--write-baseline", action="store_true", help="shrink-only rewrite")
    g.add_argument("--list", action="store_true", help="every current twin")
    ap.add_argument("--books-dir", type=Path, default=ROOT / "books")
    ap.add_argument("--baseline", type=Path, default=BASELINE)
    a = ap.parse_args(argv)
    root = a.books_dir.parent
    rows, detail, bad = twins(sorted(a.books_dir.glob("*.lisp")), root)
    for book, msg in bad:
        print(f"generator_twin_check: UNREADABLE {book}: {msg}")
    if a.list:
        print("\n".join(detail))
        return 1 if bad else 0
    if a.write_baseline:
        refusals = write_baseline(rows, a.baseline)
        if ratchet.report(TOOL, refusals):
            return 1
        print(f"generator_twin_check: wrote {len(rows)} row(s) to {a.baseline}")
        return 0
    base = load_baseline(a.baseline)
    new = new_rows(rows, base)
    for b, r in new.items():
        print(f"generator_twin_check: NEW twin in {b}: {r['count']} (baseline {base.get(b, {}).get('count', 0)}), "
              f"{'+'.join(r['kinds'])}")
        for d in detail:
            if d.startswith(b + ":"):
                print("  " + d)
    stale = sorted(b for b, r in base.items() if rows.get(b, {}).get("count", 0) < r["count"])
    for b in stale:
        print(f"generator_twin_check: STALE row {b} (baseline {base[b]['count']}, now "
              f"{rows.get(b, {}).get('count', 0)}); lower it with --write-baseline in the lane that drained it")
    if stale and not (new or bad):
        # A stale row is headroom: a new twin could land in that book up to the old count unseen.
        return 1
    if new or bad:
        print("generator_twin_check: a generator should emit this: (def-buffer NAME) or def-representation; "
              "grow the generator if it lacks the vocabulary (ruling 1)")
        return 1
    print(f"generator_twin_check: ok, {sum(r['count'] for r in rows.values())} baselined twin(s) in "
          f"{len(rows)} book(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
