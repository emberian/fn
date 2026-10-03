#!/usr/bin/env python3
"""The host-called octet-list codecs (D27, row Q2 of COMPLETE-BEFORE-6.6.0).

AGENTS.md: the served path uses concrete representations; octet lists are
the logical model, and each representation boundary has a named theorem
connecting the host-called implementation to it.  This lint counts the
sites where the host still hands a CODEC an octet LIST it consed from a
byte vector (`fnn-octet-list`, host/native/io.lisp; 16 octets of heap an
octet), so that the count can only shrink, and reaches zero.

A site is a host dispatch form `(fnn-X 'fn-NAME ...)` inside a `defun` of a
host file whose arguments include a list conversion -- a direct
`(fnn-octet-list ...)`, `#'fnn-octet-list` under mapcar, the payload's
converted list `fnn-owner-payload-octets`, or a variable the same defun
bound to such a conversion -- and whose ACL2 entry fn-NAME is a codec: it
matches one of the classes in tools/list_codec_baseline.json (frame and
control request, record write and recovery, article parse, status, BP /
TCPCL / feed / N16, digest, group names).  A dispatch handing ACL2 a
bounded identity (a Message-ID, a group name, a label) is not a codec site
unless its entry is in a class: the classes name the entries the row's
backlog lines name.

`--list` prints every site; `--all` also prints the unclassified dispatches
that receive a list (information: the next class to add); `--write`
rewrites the baseline to the current counts.  The check fails when any
file's count exceeds its baseline, or when a file not in the baseline has a
site.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools.ledger import Sym, head  # noqa: E402

BASELINE = ROOT / "tools" / "list_codec_baseline.json"
CONVERSIONS = ("fnn-octet-list", "fnn-owner-payload-octets")
BINDERS = ("let", "let*")
# A binding whose value is coerced to a number is not an octet list, whatever
# codec computed it: `(let ((next (fnn-nat (fnn-core 'fn-store-cfg-next-txid
# (mapcar #'fnn-octet-list records) ...)))) ...)' binds a txid, and
# fnn-recover-log's (fnn-core 'fn-lgc-consume-to kernel next) is not a site
# (2026-10-03, check-lane CL16: that counted it; the codec site itself, the
# cfg-next-txid dispatch, is judged where it is).
SCALAR_HEADS = ("fnn-nat", "length")


def host_files() -> list[Path]:
    out = sorted((ROOT / "host").glob("*.lisp"))
    out += sorted((ROOT / "host" / "native").glob("*.lisp"))
    return out


def symbols(x, acc: set) -> None:
    if isinstance(x, list):
        for y in x:
            symbols(y, acc)
    elif isinstance(x, Sym):
        acc.add(str(x))


def mentions_conversion(x, bound: set[str]) -> bool:
    acc: set = set()
    symbols(x, acc)
    return any(c in acc for c in CONVERSIONS) or bool(acc & bound)


def quoted_entry(arg) -> str | None:
    """'fn-name as the reader gives it: (quote fn-name)."""
    if isinstance(arg, list) and len(arg) == 2 and head(arg) == "quote" and isinstance(arg[1], Sym):
        name = str(arg[1])
        if name.startswith("fn-") and not name.startswith("fnn-"):
            return name
    return None


def bound_names(form, bound: set[str]) -> None:
    """Variables this form binds to a list conversion (let, let*)."""
    if not isinstance(form, list) or not form:
        return
    if isinstance(form[0], Sym) and str(form[0]) in BINDERS and len(form) > 1 and isinstance(form[1], list):
        for b in form[1]:
            if isinstance(b, list) and len(b) >= 2 and isinstance(b[0], Sym):
                scalar = (isinstance(b[1], list) and b[1] and isinstance(b[1][0], Sym)
                          and str(b[1][0]) in SCALAR_HEADS)
                if not scalar and mentions_conversion(b[1], bound):
                    bound.add(str(b[0]))
    for y in form:
        bound_names(y, bound)


def dispatches(form, bound: set[str], out: list) -> None:
    """Every (fnn-X 'fn-NAME args...) whose args mention a conversion."""
    if not isinstance(form, list) or not form:
        return
    if (isinstance(form[0], Sym) and str(form[0]).startswith("fnn-") and len(form) > 1):
        entry = quoted_entry(form[1])
        if entry and mentions_conversion(form[2:], bound):
            out.append(entry)
    for y in form:
        dispatches(y, bound, out)


def scan(files=None) -> list[dict]:
    sites = []
    for path in files or host_files():
        text = path.read_text()
        rel = str(path.relative_to(ROOT)) if ROOT in path.resolve().parents else str(path)
        try:
            forms = ledger.Reader(text).top_level()
        except Exception as e:  # a host file the reader cannot read is a finding
            sites.append({"file": rel, "defun": "?", "entry": "?",
                          "error": str(e)})
            continue
        for form, _pos in forms:
            if not (isinstance(form, list) and form and head(form) == "defun" and len(form) > 2):
                continue
            bound: set[str] = set()
            bound_names(form, bound)
            found: list = []
            dispatches(form[3:], bound, found)
            for entry in found:
                sites.append({"file": rel, "defun": str(form[1]),
                              "entry": entry})
    return sites


def classify(sites: list[dict], classes: dict[str, list[str]]) -> None:
    compiled = {name: [re.compile(p) for p in pats] for name, pats in classes.items()}
    for s in sites:
        s["class"] = None
        for name, pats in compiled.items():
            if any(p.match(s["entry"]) for p in pats):
                s["class"] = name
                break


def counts(sites: list[dict]) -> dict[str, int]:
    out: dict[str, int] = {}
    for s in sites:
        if s.get("class"):
            out[s["file"]] = out.get(s["file"], 0) + 1
    return dict(sorted(out.items()))


def load_baseline() -> dict:
    return json.loads(BASELINE.read_text())


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", action="store_true", help="print every classified site")
    ap.add_argument("--all", action="store_true", help="also print the unclassified dispatches")
    ap.add_argument("--write", action="store_true", help="rewrite the baseline to the current counts")
    args = ap.parse_args(argv)
    base = load_baseline()
    sites = scan()
    classify(sites, base["classes"])
    now = counts(sites)
    total = sum(now.values())
    if args.list or args.all:
        for s in sites:
            if s.get("class") or args.all:
                print(f"{s['file']}:{s['defun']} {s['entry']} [{s.get('class') or '-'}]")
    errors = [s for s in sites if "error" in s]
    for s in errors:
        print(f"list_codec_check: cannot read {s['file']}: {s['error']}")
    if args.write:
        base["sites"] = now
        base["total"] = total
        BASELINE.write_text(json.dumps(base, indent=1) + "\n")
        print(f"list_codec_check: baseline written: {total} sites in {len(now)} files")
        return 0
    bad = []
    for f, n in now.items():
        b = base["sites"].get(f)
        if b is None:
            bad.append(f"{f}: {n} sites, not in the baseline")
        elif n > b:
            bad.append(f"{f}: {n} sites, baseline {b}")
    for line in bad:
        print(f"list_codec_check: {line}")
    shrunk = sum(base["sites"].values()) - total
    print(f"list_codec_check: {total} host-called octet-list codec sites in {len(now)} files"
          f" (baseline {base['total']}{', shrunk by %d: run --write' % shrunk if shrunk > 0 else ''})")
    return 1 if (bad or errors) else 0


if __name__ == "__main__":
    sys.exit(main())
