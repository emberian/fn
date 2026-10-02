#!/usr/bin/env python3
"""The holder world, closed over the raw host (books/def-holder.lisp).

A `def-holder' declaration names, for one resource, every holder and the
host functions that acquire and release it.  ACL2's world can check the
logic holders (def-holder-check walks every function of the world); the raw
host (host/native/*.lisp, host/*.lisp loaded raw) is outside the world, so
this tool reads the declarations and the host source and checks, both ways:

* every HOST holder's :acquire and :release are called inside at least one
  of its :in functions, and every :in function exists;
* every call of a declared :acquire or :release anywhere in the raw host is
  inside an :in function of a row that declares it (fail closed: an
  undeclared acquirer is a refusal, not a holder);
* every ROOT holder's :in functions exist;
* a (:physical CUTS :cut K :after K2) effect has both cuts marked inside the
  row's :in functions, K2 before K in source order; a :process-local or
  :durable effect has its :NAME-decided and :NAME-released markers there.
  A declared cut is a name; the marker is what makes it a checked host
  release.  Missing markers are reported and fail only under --strict (the
  host side of a new row lands after the row).

What it reads: `(def-holder ...)' forms in books/*.lisp through the
ledger's non-evaluating reader; host text through
native_program_check's tokenizer (no Lisp reader, no evaluation; strings
and comments are not calls).  What it cannot decide: dynamic calls
(funcall, apply$), calls through macros the tokenizer does not expand, and
whether a call inside an :in function runs under the lock the row assumes.

Exit status: 1 on any refusal (or on a missing marker under --strict), 0
otherwise.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools.native_program_check import Str, positioned_tokens  # noqa: E402

HOST_GLOBS = ("host/native/*.lisp", "host/*.lisp")


def _sym(x) -> str:
    return str(x).lower()


def declarations(root: Path = ROOT) -> list[dict]:
    """Every (def-holder NAME . KVS) in books/*.lisp, as {name, book, line, kvs}."""
    out = []
    for path in sorted((root / "books").glob("*.lisp")):
        text = path.read_text(encoding="utf-8")
        if "def-holder" not in text:
            continue
        for form, line in ledger.Reader(text).top_level():
            if ledger.head(form) != "def-holder" or len(form) < 2:
                continue
            out.append({"name": _sym(form[1]), "book": path.relative_to(root).as_posix(),
                        "line": line, "kvs": ledger.keyword_plist(form[2:])})
    return out


def holders(decl: dict) -> list[dict]:
    """The declaration's holders: {kind, host|root|logic, acquire, release, in}."""
    out = []
    for h in decl["kvs"].get(":holders", []) or []:
        if not isinstance(h, list) or not h:
            continue
        kv = ledger.keyword_plist(h[1:])
        row = {"kind": _sym(h[0]), "in": [_sym(x) for x in (kv.get(":in") or [])]}
        if kv.get(":host") is not None and _sym(kv[":host"]) != "nil":
            row.update(sort="host", acquire=_sym(kv.get(":acquire", "")),
                       release=_sym(kv.get(":release", "")))
        elif kv.get(":root") is not None and _sym(kv[":root"]) != "nil":
            status = kv.get(":status") or []
            row.update(sort="root", status=_sym(status[0]) if status else "")
        else:
            row.update(sort="logic")
        out.append(row)
    return out


def effect(decl: dict) -> dict:
    """{kind, cuts: [marker keywords in order]} of the declaration's :effect."""
    e = decl["kvs"].get(":effect") or []
    kind = _sym(e[0]) if e else ""
    if kind == ":physical":
        kv = ledger.keyword_plist(e[2:])
        return {"kind": kind, "cuts": [_sym(kv.get(":after", "")), _sym(kv.get(":cut", ""))]}
    name = decl["name"]
    return {"kind": kind, "cuts": [f":{name}-decided", f":{name}-released"]}


# ---------------------------------------------------------------------------
# The raw host: each top-level defun's span, and the symbols called in it.

class HostFunction:
    def __init__(self, name: str, path: str, line: int):
        self.name = name
        self.path = path
        self.line = line
        self.calls: list[tuple[str, int]] = []     # (callee, offset): `(callee', `'callee', `#'callee'
        self.keywords: list[tuple[str, int]] = []  # (:keyword, offset)


def host_functions(root: Path = ROOT) -> dict[str, list[HostFunction]]:
    """Every (defun NAME ...) of the raw host, by name (a name may be defined twice)."""
    out: dict[str, list[HostFunction]] = {}
    for pattern in HOST_GLOBS:
        for path in sorted(root.glob(pattern)):
            text = path.read_text(encoding="utf-8")
            rel = path.relative_to(root).as_posix()
            depth = 0
            current: HostFunction | None = None
            tokens = list(positioned_tokens(text))
            for i, (offset, token) in enumerate(tokens):
                if isinstance(token, Str):
                    continue
                if token == "(":
                    if depth == 0 and i + 2 < len(tokens):
                        head_token = tokens[i + 1][1]
                        name_token = tokens[i + 2][1]
                        if (not isinstance(head_token, Str) and head_token in ("defun", "defmacro")
                                and not isinstance(name_token, Str)):
                            current = HostFunction(name_token, rel, text.count("\n", 0, offset) + 1)
                            out.setdefault(name_token, []).append(current)
                    elif current is not None and i + 1 < len(tokens):
                        callee = tokens[i + 1][1]
                        if not isinstance(callee, Str) and callee not in ("(", ")"):
                            current.calls.append((callee, offset))
                    depth += 1
                elif token == ")":
                    depth -= 1
                    if depth == 0:
                        current = None
                elif token in ("'", "#'"):
                    if current is not None and i + 1 < len(tokens):
                        quoted = tokens[i + 1][1]
                        if not isinstance(quoted, Str) and quoted not in ("(", ")"):
                            current.calls.append((quoted, offset))
                elif current is not None and token.startswith(":"):
                    current.keywords.append((token, offset))
    return out


def book_functions(root: Path = ROOT) -> set[str]:
    """Every (defun NAME ...) of books/*.lisp (a root's keeper may be a book function)."""
    import re
    names: set[str] = set()
    pattern = re.compile(r"^\((?:defun|defun-nx|defund)\s+([^\s()]+)", re.M)
    for path in (root / "books").glob("*.lisp"):
        for m in pattern.finditer(path.read_text(encoding="utf-8")):
            names.add(m.group(1).lower())
    return names


def check(root: Path = ROOT, strict: bool = False) -> tuple[list[str], list[str]]:
    """(refusals, notes) over every declaration."""
    decls = declarations(root)
    fns = host_functions(root)
    books = book_functions(root)
    refusals: list[str] = []
    notes: list[str] = []
    declared_sites: dict[str, set[str]] = {}   # acquire/release name -> :in functions that may call it
    for decl in decls:
        where = f"{decl['book']}:{decl['line']} {decl['name']}"
        for h in holders(decl):
            # a host holder's keepers are raw host functions; a root's may be
            # a book function (an unwired component's entry)
            known = (fns.keys() | books) if h["sort"] == "root" else fns.keys()
            missing = [f for f in h["in"] if f not in known]
            for f in missing:
                refusals.append(f"{where}: holder {h['kind']}: :in {f} is no function of the raw host"
                                + (" or of books/" if h["sort"] == "root" else ""))
            if h["sort"] == "host":
                for verb in ("acquire", "release"):
                    name = h[verb]
                    declared_sites.setdefault(name, set()).update(h["in"])
                    if name not in fns:
                        refusals.append(f"{where}: holder {h['kind']}: :{verb} {name} is no function of the raw host")
                        continue
                    if not any(any(c == name for c, _ in fn.calls)
                               for f in h["in"] if f in fns for fn in fns[f]):
                        refusals.append(f"{where}: holder {h['kind']}: :{verb} {name} is called in none of its :in {h['in']}")
            elif h["sort"] == "root":
                notes.append(f"{where}: root {h['kind']} {h.get('status', '')} in {h['in']}")
        # the effect's markers inside the row's :in functions, in order
        eff = effect(decl)
        ins = [f for h in holders(decl) for f in h["in"]]
        positions: dict[str, tuple[str, int]] = {}
        for f in ins:
            for fn in fns.get(f, []):
                for kw, offset in fn.keywords:
                    if kw in eff["cuts"] and kw not in positions:
                        positions[kw] = (fn.path, offset)
        absent = [c for c in eff["cuts"] if c not in positions]
        if absent:
            line = f"{where}: effect {eff['kind']}: cut marker(s) {absent} not in any :in function {sorted(set(ins))} (declared, not a checked host release)"
            (refusals if strict else notes).append(line)
        elif eff["kind"] == ":physical":
            after, cut = eff["cuts"]
            if positions[after] >= positions[cut]:
                refusals.append(f"{where}: effect :physical: {cut} is marked before {after} in the host; the release must follow the durable replacement")
    # every host call of a declared acquire/release is inside a declared :in function
    for name, allowed in sorted(declared_sites.items()):
        for fname, fn_list in fns.items():
            if fname == name:
                continue  # the wrapper's own definition
            for fn in fn_list:
                if any(c == name for c, _ in fn.calls) and fname not in allowed:
                    refusals.append(f"{fn.path}:{fn.line} {fname} calls {name}, which is declared only in {sorted(allowed)}: an undeclared acquirer is a refusal, not a holder")
    if not decls:
        notes.append("no def-holder declarations in books/")
    return refusals, notes


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--strict", action="store_true",
                    help="a declared cut with no host marker is a refusal too")
    args = ap.parse_args(argv)
    refusals, notes = check(strict=args.strict)
    for n in notes:
        print("note: " + n)
    for r in refusals:
        print("REFUSED: " + r)
    print(f"holder check: {len(declarations())} declaration(s), {len(refusals)} refusal(s), "
          f"{len(notes)} note(s){' (strict)' if args.strict else ''}")
    return 1 if refusals else 0


if __name__ == "__main__":
    sys.exit(main())
