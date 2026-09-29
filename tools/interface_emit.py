#!/usr/bin/env python3
"""The registry half of `definterface': the host-called entries, generated.

`(definterface NAME :class C [:kinds ...] [:exempt ...] [:keystones ...]
[:root :extract|:extract-extra] [:direct "why"])` (books/definterface.lisp)
declares a host-called entry; ACL2 checks each declaration against the
image's world when host/native/build.lisp loads host/interfaces.lisp (and the
extractor's world when it loads host/interfaces-extract.lisp).  This reads
the same forms with the ledger's non-evaluating reader and GENERATES:

* planning/interfaces.json -- one row per declared entry: its class, the
  kinds its guard gives the host entry guard, its exempt formals with their
  reasons, its keystones, its extraction role, whether the raw host applies
  it directly, and the raw host files that dispatch it;
* tools/extract/roots.sh -- the extractor's default ROOTS and EXTRA
  (tools/extract/build.sh sources it), in declaration order;

and hands tools/harness_check.py its exempt formals (`entry_kind_exempt')
and its direct applications (`entry_direct_allowed'), which were hand lists
there.

THE HOST-BINDING CHECK (`--check') is independent of the declarations: it
reads the raw host (tools/harness_check.py's reading of host/native/*.lisp)
for the names it dispatches through fnn-call and the ACL2 functions it
applies directly, and refuses

* a declared entry the raw host never dispatches (stale), unless it is an
  extraction root or EXTRA function (the extracted driver calls those) or
  :direct;
* a :direct entry the raw host does not apply directly, and a direct
  application that no :direct declaration names (harness_check's
  entry-guards lint reports the latter with its site);
* a declaration whose NAME no book or ACL2-mode host file defines;
* a generated file that differs from what the forms say.

What it cannot check is the world: the class, the kinds and the keystones
are ACL2's to confirm, at image build (host/interfaces.lisp) and in
tests/acl2/definterface-tests.lisp.

    python3 tools/interface_emit.py            # report
    python3 tools/interface_emit.py --check    # exit 1 on any finding (make check)
    python3 tools/interface_emit.py --write    # regenerate the two files
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

SOURCES = ("host/interfaces.lisp", "host/interfaces-extract.lisp")
REGISTRY = ROOT / "planning" / "interfaces.json"
ROOTS_SH = ROOT / "tools" / "extract" / "roots.sh"
KEYS = {":class", ":kinds", ":exempt", ":keystones", ":root", ":direct"}


def _sym(x) -> str:
    return str(x).lower()


def _plist(items: list, where: str) -> dict:
    out: dict = {}
    if len(items) % 2:
        raise ValueError("{}: odd keyword list".format(where))
    for index in range(0, len(items), 2):
        key = _sym(items[index])
        if key not in KEYS:
            raise ValueError("{}: unknown keyword {}".format(where, key))
        out[key] = items[index + 1]
    return out


def declarations(root: Path = ROOT) -> list[dict]:
    """Every definterface form in SOURCES, in order, parsed."""
    found: list[dict] = []
    for relative in SOURCES:
        path = root / relative
        if not path.is_file():
            continue
        for form, line in ledger.Reader(path.read_text(encoding="utf-8")).top_level():
            if ledger.head(form) != "definterface":
                continue
            where = "{}:{}".format(relative, line)
            kv = _plist(form[2:], where)
            kinds = [[_sym(f), _sym(r)] for f, r in (kv.get(":kinds") or [])]
            exempt = {_sym(f): why for f, why in (kv.get(":exempt") or [])}
            keystones = []
            for entry in kv.get(":keystones") or []:
                if isinstance(entry, list):
                    keystones.append({"theorem": _sym(entry[0]), "via": _sym(entry[2])})
                else:
                    keystones.append({"theorem": _sym(entry)})
            role = kv.get(":root")
            found.append({
                "name": _sym(form[1]),
                "source": relative,
                "line": line,
                "class": _sym(kv.get(":class", "")).lstrip(":"),
                "kinds": kinds,
                "exempt": exempt,
                "keystones": keystones,
                "root": _sym(role).lstrip(":") if role is not None else None,
                "direct": kv.get(":direct"),
            })
    return found


def entry_kind_exempt(root: Path = ROOT) -> dict[tuple[str, str], str]:
    """(entry, formal) -> why, for tools/harness_check.py's entry-guards lint."""
    return {(d["name"], formal): why
            for d in declarations(root) for formal, why in d["exempt"].items()}


def entry_direct_allowed(root: Path = ROOT) -> dict[str, str]:
    """entry -> why, for the ACL2 functions the raw host applies directly."""
    return {d["name"]: d["direct"] for d in declarations(root) if d["direct"]}


def render_roots(decls: list[dict]) -> str:
    roots = " ".join(d["name"] for d in decls if d["root"] == "extract")
    extra = " ".join(d["name"] for d in decls if d["root"] == "extract-extra")
    return ("# GENERATED by tools/interface_emit.py from the definterface :root\n"
            "# declarations in host/interfaces.lisp and host/interfaces-extract.lisp.\n"
            "# Do not edit; regenerate.\n"
            'FN_EXTRACT_ROOTS_DECLARED="{}"\n'
            'FN_EXTRACT_EXTRA_DECLARED="{}"\n').format(roots, extra)


def host_reading(root: Path = ROOT) -> dict:
    """What the raw host does, read from its source (harness_check's reading)."""
    from tools import harness_check
    tree = ledger.load_tree()
    raw = ledger.raw_host_paths(tree)
    rawdefs, _ambiguous = harness_check.raw_definitions({r: tree.hosts[r].forms for r in raw})
    dispatched: dict[str, set[str]] = {}
    direct: dict[str, set[str]] = {}
    for relative in sorted(raw):
        for form, _line in tree.hosts[relative].forms:
            applications: list = []
            harness_check.raw_applications(form, applications)
            for name, _count in applications:
                if name.startswith("'"):
                    dispatched.setdefault(name[1:], set()).add(relative)
                elif name in tree.functions and name not in rawdefs:
                    direct.setdefault(name, set()).add(relative)
    defined = set(tree.functions) | set(harness_check._acl2_definition_forms(tree, raw))
    return {"dispatched": dispatched, "direct": direct,
            "defined": defined, "entries": len(dispatched)}


def render_registry(decls: list[dict], reading: dict) -> str:
    rows = []
    for d in decls:
        rows.append({
            "name": d["name"],
            "declared_in": d["source"],
            "class": d["class"],
            "kinds": d["kinds"],
            "exempt": d["exempt"],
            "keystones": d["keystones"],
            "extraction": d["root"],
            "direct": d["direct"],
            "dispatched_from": sorted(reading["dispatched"].get(d["name"], ())),
            "applied_directly_in": sorted(reading["direct"].get(d["name"], ())),
        })
    doc = {
        "schema_version": 1,
        "description": ("GENERATED by tools/interface_emit.py from the definterface forms "
                        "(books/definterface.lisp) in host/interfaces.lisp and "
                        "host/interfaces-extract.lisp; ACL2 checks each against the world "
                        "at image build.  Do not edit; regenerate."),
        # The raw host's total entry count is printed, not written: it moves
        # with every host change, and a registry row should not.
        "coverage": {"declared": len(decls),
                     "declared_and_dispatched": sum(1 for d in decls
                                                    if d["name"] in reading["dispatched"]),
                     "guard_verified": sum(1 for d in decls
                                           if d["class"] == "common-lisp-compliant")},
        "entries": rows,
    }
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


def findings(decls: list[dict], reading: dict, root: Path = ROOT) -> list[str]:
    out: list[str] = []
    seen: dict[str, str] = {}
    for d in decls:
        where = "{}:{}".format(d["source"], d["line"])
        name = d["name"]
        if name in seen:
            out.append("{}: {} is declared twice (first at {})".format(where, name, seen[name]))
        seen[name] = where
        if name not in reading["defined"] and not name.startswith("create-"):
            out.append("{}: {} is defined by no book or ACL2-mode host file".format(where, name))
        if d["direct"]:
            if name not in reading["direct"]:
                out.append("{}: {} is declared :direct but the raw host never applies it "
                           "directly (stale)".format(where, name))
        elif d["root"] is None and name not in reading["dispatched"]:
            out.append("{}: {} is declared but the raw host never dispatches it (stale); "
                       "remove the declaration or name its role".format(where, name))
    direct_declared = {d["name"] for d in decls if d["direct"]}
    for name in sorted(set(reading["direct"]) - direct_declared):
        out.append("the raw host applies {} directly ({}), bypassing fnn-call's entry "
                   "guard, and no definterface :direct names it".format(
                       name, ", ".join(sorted(reading["direct"][name]))))
    if not ROOTS_SH.is_file() or ROOTS_SH.read_text() != render_roots(decls):
        out.append("tools/extract/roots.sh is not what the declarations say; "
                   "run tools/interface_emit.py --write")
    if not REGISTRY.is_file() or REGISTRY.read_text() != render_registry(decls, reading):
        out.append("planning/interfaces.json is not what the declarations say; "
                   "run tools/interface_emit.py --write")
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    if args.write:
        from tools import acl2_slots  # noqa: E402
        acl2_slots.refuse_on_laptop("tools/interface_emit.py --write")
    decls = declarations()
    reading = host_reading()
    if args.write:
        ROOTS_SH.write_text(render_roots(decls))
        REGISTRY.write_text(render_registry(decls, reading))
    problems = findings(decls, reading)
    declared = sum(1 for d in decls if d["name"] in reading["dispatched"])
    print("interface_emit: {} declared; {} of the raw host's {} dispatched entries; "
          "{} extraction roots, {} EXTRA; {} finding(s)".format(
              len(decls), declared, reading["entries"],
              sum(1 for d in decls if d["root"] == "extract"),
              sum(1 for d in decls if d["root"] == "extract-extra"), len(problems)))
    for problem in problems:
        print("  " + problem)
    return 1 if (args.check and problems) else 0


if __name__ == "__main__":
    raise SystemExit(main())
