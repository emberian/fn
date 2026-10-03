#!/usr/bin/env python3
"""The registry half of `def-cost': what each dispatched entry's cost claim is.

`(def-cost NAME [:visits BOUND :sizes ((S TERM) ...)] [:unaccounted (F ...)])`
(books/def-cost.lisp) derives NAME's visit cost from its executed body in the
world and proves the declared bound as a theorem about that derived cost,
partial over the callees it names :unaccounted (ACL2 refuses a declaration
whose :unaccounted is not the derived set).  This reads the same forms in
books/ and host/ with the ledger's non-evaluating reader and GENERATES

* planning/cost-obligations.json -- one row per DISPATCHED entry of
  planning/interfaces.json (every host-called entry, so an entry with no
  declaration is a row too): its class (common-lisp-compliant | ideal |
  program), and its cost claim:
    proved       a def-cost with :visits and nothing unaccounted
    partial      a def-cost with :visits, partial over the named callees
    derived      a def-cost with no :visits (the twins exist, no bound)
    none         no def-cost
  with the bound, the size names, the unaccounted list, the theorem name and
  the file that declares it;
* planning/cost-contracts.json -- the trusted base `*fn-cost-contracts*'
  (books/def-cost.lisp), one row per primitive: template, reason, and
  `witness` (the measured micro-benchmark record under the recorded
  toolchain, when one exists under planning/evidence/; null until then,
  counted as `unwitnessed`).

THE RATCHET (`--check`, a `make check' step): both files must be what the
tree says (regenerate with `--write`); and against the PROTECTED BASE --
origin/dev's committed copy when the ref is reachable, else HEAD's -- compared
BY NAME: an entry whose base claim is `proved` or `partial` may not fall back
(a downgrade fails; a changed body that no longer proves is a refusal in
ACL2 first, and this says why the registry moved); an entry absent from the
base with class common-lisp-compliant and no declaration is a NEW
undeclared entry: allowed only while planning/cost-baseline.json lists its
name (the baseline SHRINKS: `--baseline` rewrites it from the current `none`
set and refuses to add a name); a contract row that changed its template or
vanished fails (the trusted base is reviewed, never edited in passing); the
unwitnessed count may not grow.

    python3 tools/cost_obligations.py            # report
    python3 tools/cost_obligations.py --check    # exit 1 on any finding
    python3 tools/cost_obligations.py --write    # regenerate the two files
    python3 tools/cost_obligations.py --baseline # rewrite the undeclared baseline (shrink only)
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

OBLIGATIONS = ROOT / "planning" / "cost-obligations.json"
CONTRACTS = ROOT / "planning" / "cost-contracts.json"
BASELINE = ROOT / "planning" / "cost-baseline.json"
INTERFACES = ROOT / "planning" / "interfaces.json"
GENERATOR = ROOT / "books" / "def-cost.lisp"
SOURCES = ("books", "host")
CLAIMS = ("proved", "partial", "derived", "none")
RANK = {c: i for i, c in enumerate(CLAIMS)}


def _sym(x) -> str:
    return str(x).lower() if isinstance(x, (str, ledger.Sym)) else ledger.source_text(x)


def _forms(root: Path, directory: str):
    for path in sorted((root / directory).glob("*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace")
        if "def-cost" not in text and "*fn-cost-contracts*" not in text:
            continue
        for form, _line in ledger.Reader(text).top_level():
            yield path.relative_to(root).as_posix(), form


def declarations(root: Path = ROOT) -> dict[str, dict]:
    """NAME -> {bound, sizes, unaccounted, file} for every def-cost form."""
    found: dict[str, dict] = {}
    for directory in SOURCES:
        for relative, form in _forms(root, directory):
            if ledger.head(form) != "def-cost" or len(form) < 2:
                continue
            name = _sym(form[1])
            kv = ledger.keyword_plist(form[2:])
            if name in found:
                raise ValueError("{} has two def-cost declarations ({} and {})".format(
                    name, found[name]["file"], relative))
            sizes = kv.get(":sizes") or []
            found[name] = {
                "bound": ledger.source_text(kv[":visits"]) if kv.get(":visits") is not None else None,
                "sizes": [_sym(s[0]) for s in sizes if isinstance(s, list) and s],
                "unaccounted": sorted(_sym(f) for f in (kv.get(":unaccounted") or [])),
                "file": relative}
    return found


def contracts(root: Path = ROOT) -> list[dict]:
    """The trusted base, read from the generator's defconst."""
    for relative, form in _forms(root, "books"):
        if relative != "books/def-cost.lisp" or ledger.head(form) != "defconst":
            continue
        if len(form) < 3 or _sym(form[1]) != "*fn-cost-contracts*":
            continue
        rows = form[2]
        if isinstance(rows, list) and rows and ledger.head(rows) == "quote":
            rows = rows[1]
        out = []
        for row in rows:
            if not (isinstance(row, list) and len(row) == 3):
                raise ValueError("contract row {} is not (PRIMITIVE TEMPLATE REASON)".format(
                    ledger.source_text(row)))
            out.append({"primitive": _sym(row[0]),
                        "template": ledger.source_text(row[1]),
                        "reason": row[2] if isinstance(row[2], str) else ledger.source_text(row[2]),
                        "witness": None})
        return out
    raise ValueError("books/def-cost.lisp defines no *fn-cost-contracts*")


def claim(decl: dict | None) -> str:
    if decl is None:
        return "none"
    if decl["bound"] is None:
        return "derived"
    return "partial" if decl["unaccounted"] else "proved"


def build(root: Path = ROOT) -> dict:
    interfaces = json.loads((root / "planning" / "interfaces.json").read_text(encoding="utf-8"))
    decls = declarations(root)
    rows = []
    for entry in interfaces["entries"]:
        if not entry.get("dispatched_from"):
            continue
        d = decls.get(entry["name"])
        rows.append({
            "name": entry["name"], "class": entry["class"], "claim": claim(d),
            "bound": d["bound"] if d else None,
            "sizes": d["sizes"] if d else [],
            "unaccounted": d["unaccounted"] if d else [],
            "theorem": "{}-visits-bound".format(entry["name"]) if d and d["bound"] else None,
            "declared_in": d["file"] if d else None})
    rows.sort(key=lambda r: r["name"])
    counts = {c: sum(1 for r in rows if r["claim"] == c) for c in CLAIMS}
    by_class = {k: {c: sum(1 for r in rows if r["class"] == k and r["claim"] == c) for c in CLAIMS}
                for k in ("common-lisp-compliant", "ideal", "program")}
    # declarations on names the registry does not dispatch (a book function
    # declared in a test, an internal function): recorded, not rows
    undispatched = sorted(n for n in decls if n not in {r["name"] for r in rows})
    return {"schema_version": 1,
            "description": "generated by tools/cost_obligations.py --write; do not edit",
            "counts": counts, "by_class": by_class,
            "undispatched_declarations": undispatched, "entries": rows}


def build_contracts(root: Path = ROOT) -> dict:
    rows = contracts(root)
    return {"schema_version": 1,
            "description": "generated by tools/cost_obligations.py --write from "
                           "books/def-cost.lisp *fn-cost-contracts*; the trusted base",
            "count": len(rows), "unwitnessed": sum(1 for r in rows if r["witness"] is None),
            "contracts": rows}


def render(doc: dict) -> str:
    return json.dumps(doc, indent=1, sort_keys=False) + "\n"


def base_copy(path: Path, root: Path = ROOT) -> dict | None:
    """origin/dev's committed copy of PATH when reachable, else HEAD's, else None."""
    relative = path.relative_to(root).as_posix()
    for ref in ("origin/dev", "HEAD"):
        try:
            text = subprocess.run(["git", "-C", str(root), "show", "{}:{}".format(ref, relative)],
                                  capture_output=True, text=True, check=True).stdout
        except (subprocess.CalledProcessError, FileNotFoundError):
            continue
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return None
    return None


def load_baseline(root: Path = ROOT) -> set[str]:
    path = root / "planning" / "cost-baseline.json"
    if not path.is_file():
        return set()
    return set(json.loads(path.read_text(encoding="utf-8")).get("undeclared", []))


def check(root: Path = ROOT, base: dict | None = None, base_contracts: dict | None = None,
          baseline: set[str] | None = None) -> list[str]:
    findings: list[str] = []
    try:
        doc = build(root)
        cdoc = build_contracts(root)
    except ValueError as error:
        return ["cost_obligations: {}".format(error)]
    for path, fresh in ((root / "planning" / "cost-obligations.json", doc),
                        (root / "planning" / "cost-contracts.json", cdoc)):
        if not path.is_file():
            findings.append("{} is absent: run --write".format(path.relative_to(root).as_posix()))
        elif path.read_text(encoding="utf-8") != render(fresh):
            findings.append("{} differs from what the tree says: run --write".format(
                path.relative_to(root).as_posix()))
    if baseline is None:
        baseline = load_baseline(root)
    if base is None:
        base = base_copy(root / "planning" / "cost-obligations.json", root)
    if base_contracts is None:
        base_contracts = base_copy(root / "planning" / "cost-contracts.json", root)
    base_rows = {r["name"]: r for r in (base or {}).get("entries", [])}
    for row in doc["entries"]:
        old = base_rows.get(row["name"])
        if old is not None and RANK[row["claim"]] > RANK[old["claim"]]:
            findings.append("{}: cost claim fell from {} to {} (the base holds {})".format(
                row["name"], old["claim"], row["claim"], old.get("theorem") or "its declaration"))
        if (old is None and row["claim"] == "none"
                and row["class"] == "common-lisp-compliant"
                and row["name"] not in baseline):
            findings.append("{}: a new guard-verified dispatched entry with no def-cost "
                            "and not in planning/cost-baseline.json".format(row["name"]))
    stale = sorted(n for n in baseline if n not in {r["name"] for r in doc["entries"]
                                                     if r["claim"] == "none"})
    for name in stale:
        findings.append("planning/cost-baseline.json lists {}, which is declared or no longer "
                        "dispatched: run --baseline".format(name))
    old_contracts = {r["primitive"]: r for r in (base_contracts or {}).get("contracts", [])}
    new_contracts = {r["primitive"]: r for r in cdoc["contracts"]}
    for name, old in old_contracts.items():
        new = new_contracts.get(name)
        if new is None:
            findings.append("contract {} vanished from *fn-cost-contracts* (the trusted base is "
                            "reviewed, never edited in passing)".format(name))
        elif new["template"] != old["template"]:
            findings.append("contract {} changed its template from {} to {}".format(
                name, old["template"], new["template"]))
    if base_contracts is not None and cdoc["unwitnessed"] > base_contracts.get("unwitnessed", 0):
        findings.append("unwitnessed contracts grew from {} to {}".format(
            base_contracts.get("unwitnessed", 0), cdoc["unwitnessed"]))
    return findings


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--baseline", action="store_true")
    args = parser.parse_args(argv)
    if args.write:
        OBLIGATIONS.write_text(render(build()), encoding="utf-8")
        CONTRACTS.write_text(render(build_contracts()), encoding="utf-8")
        print("wrote planning/cost-obligations.json and planning/cost-contracts.json")
    if args.baseline:
        doc = build()
        old = load_baseline()
        names = sorted(r["name"] for r in doc["entries"]
                       if r["claim"] == "none" and r["class"] == "common-lisp-compliant")
        if old and set(names) - old:
            print("cost_obligations: the baseline only shrinks; new undeclared entries: {}".format(
                ", ".join(sorted(set(names) - old))))
            return 1
        BASELINE.write_text(json.dumps({"description": "guard-verified dispatched entries with "
                                        "no def-cost yet; shrinks only (tools/cost_obligations.py)",
                                        "undeclared": names}, indent=1) + "\n", encoding="utf-8")
        print("wrote planning/cost-baseline.json: {} undeclared".format(len(names)))
    if args.check:
        findings = check()
        for line in findings:
            print(line)
        print("cost_obligations: {} finding(s)".format(len(findings)))
        return 1 if findings else 0
    if not (args.write or args.baseline):
        doc = build()
        print(json.dumps(doc["counts"]))
        for row in doc["entries"]:
            if row["claim"] != "none":
                print("{:<40} {:<8} {}".format(row["name"], row["claim"], row["bound"] or ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
