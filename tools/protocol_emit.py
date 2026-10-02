#!/usr/bin/env python3
"""The NNTP protocol table (books/protocol-table.lisp) as JSON.

The table is one `defprotocol` form.  This reads it with the ledger's
non-evaluating reader (tools/ledger.py: nothing is interned, evaluated or
macro-expanded, so reading the book cannot run it) and writes the rows as
JSON for the programs that used to keep their own copy:

  * tests/fuzz_nntp.py takes each command's argument grammar (`:fuzz`);
  * tools/docs_check.py writes the FAQ's command region from `:rfc` and
    `:faq` (docs/articles/fn-faq-2.txt);
  * the reply texts by (command, key) are the ones `fn-proto-text` expands
    to inside the books.

    python3 tools/protocol_emit.py                # JSON on stdout
    python3 tools/protocol_emit.py --check        # rows well formed; names defined
    python3 tools/protocol_emit.py --text GROUP no-group
    python3 tools/protocol_emit.py --expand books/nntp-post.lisp

`--expand BOOK` prints BOOK with each `(fn-proto-text ROW KEY)` replaced by
the quoted literal the macro expands to: the byte-identical-expansion
differential of a book converted to table lookups is
`diff <(git show BASE:BOOK) <(protocol_emit.py --expand BOOK)`.  It mirrors
the macro (books/protocol-table.lisp fn-proto-text-of, fn-proto-shared-text)
for that comparison only; the books admit what ACL2's macro expands.

`--check` refuses a row whose :parser/:model/:cat/:xref names a function no
book defines (a stale name after a rename), and a :fuzz production the
fuzzer's interpreter does not know.  ACL2 checks the rest of the row shape
when the book certifies (`fn-proto-tablep`).
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import ledger  # noqa: E402
from ledger import Sym  # noqa: E402

TABLE = ROOT / "books" / "protocol-table.lisp"

# The productions tests/fuzz_nntp.py interprets (Gen.words).
FUZZ_OPS = {"pool", "choice", "opt", "msgid", "pool+msgid", "alt", "split",
            "bound", "rep", "rep-choice", "cases"}


def _kw(x) -> str:
    return str(x)[1:] if isinstance(x, Sym) and str(x).startswith(":") else str(x)


def _num(x):
    """A number the reader left as text (a ratio such as 1/5) as a float."""
    if isinstance(x, (int, float)):
        return x
    return float(Fraction(str(x)))


def _production(p):
    """A :fuzz production as JSON: [op, ...] lists, words as strings."""
    if isinstance(p, list):
        if not p:
            return []
        head = p[0]
        if isinstance(head, Sym) and str(head).startswith(":"):
            op = _kw(head)
            rest = p[1:]
            if op == "opt":
                return [op, _num(rest[0])] + [_production(x) for x in rest[1:]]
            if op == "split":
                return [op] + [[_num(arm[0])] + [_production(x) for x in arm[1:]]
                               for arm in rest]
            if op in ("pool", "pool+msgid"):
                return [op, _kw(rest[0])]
            if op == "bound":
                return [op, _kw(rest[0]), int(rest[1])]
            if op == "rep":
                return [op, str(rest[0]), int(rest[1])]
            if op == "rep-choice":
                return [op, [_production(x) for x in rest[0]], int(rest[1])]
            return [op] + [_production(x) for x in rest]
        return [_production(x) for x in p]
    if isinstance(p, Sym):
        raise ValueError("a symbol in a :fuzz production: %s" % p)
    return str(p)


def _symbols(x) -> list[str]:
    return [str(s).lower() for s in (x or []) if isinstance(s, Sym)]


def _plist(items) -> dict:
    out = {}
    for i in range(0, len(items) - 1, 2):
        out[_kw(items[i])] = items[i + 1]
    return out


def read_table(path: Path = TABLE) -> list:
    forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
    for form, _line in forms:
        if isinstance(form, list) and form and form[0] == "defprotocol":
            return form[2:]
    raise SystemExit("%s: no defprotocol form" % path)


def load(path: Path = TABLE) -> dict:
    rows = []
    for row in read_table(path):
        name = str(row[0])
        pl = _plist(row[1:])
        replies = []
        for e in pl.get("replies") or []:
            replies.append({"code": int(e[0]), "class": _kw(e[1]), "layer": _kw(e[2]),
                            "key": _kw(e[3]), "text": str(e[4]),
                            "flags": [_kw(f) for f in e[5:]]})
        rows.append({
            "name": name,
            "rfc": str(pl.get("rfc", "")),
            "dispatch": _kw(pl.get("dispatch")),
            "parser": _symbols(pl.get("parser")),
            "model": _symbols(pl.get("model")),
            "cat": _symbols(pl.get("cat")),
            "xref": _symbols(pl.get("xref")),
            "live": [[str(v[0]), str(v[1]).lower()] for v in (pl.get("live") or [])],
            "framing": _kw(pl.get("framing")),
            "variants": [[str(v[0]), str(v[1])] for v in (pl.get("variants") or [])],
            "replies": replies,
            "fuzz": _production(pl["fuzz"]) if "fuzz" in pl else None,
            "faq": str(pl.get("faq", "")),
        })
    return {"source": TABLE.relative_to(ROOT).as_posix(), "rows": rows}


def row(table: dict, name: str) -> dict:
    for r in table["rows"]:
        if r["name"] == name:
            return r
    raise KeyError(name)


def text(table: dict, name: str, key: str) -> str:
    for e in row(table, name)["replies"]:
        if e["key"] == key and "computed" not in e["flags"]:
            return e["text"]
    raise KeyError((name, key))


def shared_text(table: dict, key: str):
    """fn-proto-shared-text: KEY's literal text in every row that has one, or None."""
    found = None
    for r in table["rows"]:
        here = next((e["text"] for e in r["replies"]
                     if e["key"] == key and "computed" not in e["flags"]), None)
        if here is None:
            continue
        if found is not None and here != found:
            return None
        found = here
    return found


PROTO_TEXT = re.compile(r'\(fn-proto-text\s+(\*|"[^"]*")\s+:([^\s()]+)\s*\)')


def expand(table: dict, source: str) -> str:
    """SOURCE with every (fn-proto-text ROW KEY) replaced by its quoted literal."""
    def one(m):
        name, key = m.group(1), m.group(2).lower()
        t = shared_text(table, key) if name == "*" else text(table, name.strip('"'), key)
        if t is None:
            raise KeyError((name, key))
        return '"%s"' % t.replace("\\", "\\\\").replace('"', '\\"')
    return PROTO_TEXT.sub(one, source)


def defined_functions() -> set[str]:
    import callgraph
    names = set()
    for path in (ROOT / "books").glob("*.lisp"):
        forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
        names.update(d.name for d in callgraph.collect(forms, path.name))
    return names


def _ops(p, found):
    if isinstance(p, list) and p:
        if isinstance(p[0], str) and p[0] in FUZZ_OPS | {"opt", "split"}:
            found.add(p[0])
        for x in p[1:] if isinstance(p[0], str) else p:
            _ops(x, found)


def check(table: dict) -> list[str]:
    failures = []
    defined = defined_functions()
    seen = set()
    for r in table["rows"]:
        if r["name"] in seen:
            failures.append("row %s appears twice" % r["name"])
        seen.add(r["name"])
        for col in ("parser", "model", "cat", "xref"):
            for fn in r[col]:
                if fn not in defined:
                    failures.append("row %s :%s names %s, which no book defines"
                                    % (r["name"], col, fn))
        for form, fn in r["live"]:
            if fn not in defined:
                failures.append("row %s :live %s names %s, which no book defines"
                                % (r["name"], form, fn))
        keys = [e["key"] for e in r["replies"]]
        if len(keys) != len(set(keys)):
            failures.append("row %s repeats a reply key" % r["name"])
        for e in r["replies"]:
            if not e["text"].startswith(str(e["code"])):
                failures.append("row %s reply %s does not begin with %d"
                                % (r["name"], e["key"], e["code"]))
        if r["fuzz"] is not None:
            ops = set()
            _ops(r["fuzz"], ops)
            unknown = ops - FUZZ_OPS
            if unknown:
                failures.append("row %s :fuzz uses %s" % (r["name"], sorted(unknown)))
    return failures


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--text", nargs=2, metavar=("COMMAND", "KEY"))
    ap.add_argument("--expand", metavar="BOOK")
    args = ap.parse_args(argv)
    table = load()
    if args.expand:
        sys.stdout.write(expand(table, Path(args.expand).read_text(encoding="utf-8")))
        return 0
    if args.text:
        print(text(table, args.text[0], args.text[1]))
        return 0
    if args.check:
        failures = check(table)
        for f in failures:
            print("FAIL " + f)
        print("protocol_emit: %d rows, %d replies, %d failure(s)" % (
            len(table["rows"]), sum(len(r["replies"]) for r in table["rows"]), len(failures)))
        return 1 if failures else 0
    json.dump(table, sys.stdout, indent=1)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
