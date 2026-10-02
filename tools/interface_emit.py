#!/usr/bin/env python3
"""The registry half of `definterface': the host-called entries, generated.

`(definterface NAME :class C [:kinds ...] [:exempt ...] [:keystones ...]
[:root :extract|:extract-extra] [:direct "why"] [:raw-with (THM ...)])`
(books/definterface.lisp)
declares a host-called entry; ACL2 checks each declaration against the
image's world when host/native/build.lisp loads host/interfaces.lisp (and the
extractor's world when it loads host/interfaces-extract.lisp).  This reads
the same forms with the ledger's non-evaluating reader and GENERATES:

* planning/interfaces.json -- one row per declared entry: its class, the
  kinds its guard gives the host entry guard, its exempt formals with their
  reasons, its keystones, its extraction role, whether the raw host applies
  it directly, the theorems of its `:raw-with` argument (D40: the host
  dispatches the entry to its guard-verified definition, not its executable
  counterpart; the top-level `raw_dispatched` lists those entries), and the
  raw host files that dispatch it;
* tools/extract/roots.sh -- the extractor's default ROOTS and EXTRA
  (tools/extract/build.sh sources it), in declaration order;
* the subsystem each entry is filed under (SUBSYSTEMS below: a name prefix,
  else the dispatching host file), a column of the registry.
  planning/interfaces-gaps.md is tools/coverage.py's: what the certified
  world says about each entry (its direct theorems, the ones about its
  callers or callees, and nothing), from a dump of the world, not a name match;

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
* a dispatched entry that no declaration names (every host-called entry is
  declared);
* a generated file that differs from what the forms say;

* any way the raw host could reach a book function other than a quoted
  dispatch (tools/raw_dispatch_rule.py: a book symbol outside a dispatcher's
  name position, a symbol made at run time, a world or function-cell read,
  a function position holding a value not traced to a host function).

* a `:raw-with` on an entry not declared :common-lisp-compliant, or naming a
  theorem no book defines (the world check -- every carried guard conjunct
  concluded by a named theorem -- is ACL2's at image build);

* a declaration whose :class or :kinds is not what the image build will
  find (tools/interface_kinds.py computes both from the source the way
  books/definterface.lisp's fn-di-problem reads the world, and skips what
  the source alone cannot decide -- item 68: the image build stopped on a
  missing :kinds after its 25 minutes).

What it cannot check is the world: the keystones, and the class and kinds
the source cannot decide, are ACL2's to confirm, at image build
(host/interfaces.lisp) and in tests/acl2/definterface-tests.lisp.

    python3 tools/interface_emit.py            # report
    python3 tools/interface_emit.py --check    # exit 1 on any finding (make check)
    python3 tools/interface_emit.py --write    # regenerate the two files
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

SOURCES = ("host/interfaces.lisp", "host/interfaces-extract.lisp",
           "host/account-adoption-interfaces.lisp")
REGISTRY = ROOT / "planning" / "interfaces.json"
ROOTS_SH = ROOT / "tools" / "extract" / "roots.sh"
RAW_DECLARATIONS = ROOT / "host" / "interfaces-raw.lisp"
KEYS = {":class", ":kinds", ":exempt", ":keystones", ":root", ":direct", ":delegates",
        ":raw-with", ":raw-guarded"}

# The subsystems a declaration is filed under (host/interfaces.lisp's
# sections; planning/interfaces-gaps.md).  A name prefix decides first, then
# the first dispatching host file the table names, else nntp/served (the
# extraction roots: the served program's driver calls them).
SUBSYSTEMS = ("store", "owner", "nntp/served", "peer/feed", "bp", "web",
              "admin/operator", "control")
SUBSYSTEM_PREFIX = (
    ("control", ("fn-native-control", "fn-native-hybrid-control", "fn-hl-host",
                 "fn-owner-control", "fn-ncl-", "fn-cpj-", "fn-cp-", "fn-hctl")),
    ("admin/operator", ("fn-native-operator", "fn-native-admin", "fn-native-auth-admin",
                        "fn-native-live", "fn-native-health", "fn-native-config", "fn-nop-",
                        "fn-nls-", "fn-heap-", "fn-cfg-", "fn-bs-profile", "fn-wf",
                        "fn-workflow")),
    ("web", ("fn-web", "fn-native-web")),
    ("bp", ("fn-bp", "fn-tcpcl", "fn-tcl-", "fn-dtn")),
    ("peer/feed", ("fn-pull", "fn-feed", "fn-peer", "fn-pinv", "fn-anchor", "fn-hsig",
                   "fn-jpub", "fn-redeem", "fn-th-", "fn-cu-")),
    ("owner", ("fn-owner",)),
    ("nntp/served", ("fn-reader", "fn-served", "fn-outcome", "fn-native-auth", "fn-wire",
                     "fn-cbud", "fn-rdc")),
    ("store", ("fn-store", "fn-lg", "fn-smid", "fn-lz", "fn-arx", "fn-arena", "fn-ns-",
               "fn-ock", "fn-srs", "fn-sx", "fn-otm", "fn-log", "fn-sbud", "fn-scka",
               "fn-olr", "fn-frame", "fn-b3", "fn-blake3", "fn-sha", "create-fn-",
               "fn-intern", "fn-clock", "fn-octets")),
)
SUBSYSTEM_FILE = {
    "io": "store", "checkpoint": "store", "extent": "store", "heap": "admin/operator",
    "owner": "owner", "keys": "owner", "consumer-local": "control", "topic-local": "control",
    "auth": "nntp/served", "login-bindings": "nntp/served", "tls-reload": "nntp/served",
    "mux": "nntp/served", "pull-service": "peer/feed", "feed-service": "peer/feed",
    "feed-filename": "peer/feed", "peer-invite": "peer/feed", "anchor": "peer/feed",
    "immutable-publish": "peer/feed", "signatures": "peer/feed",
    "signature-command": "peer/feed", "bp-service": "bp", "bp": "bp", "bp-node": "bp",
    "bp-app": "bp", "bp-obligation": "bp", "bp-contact": "bp", "tcpcl": "bp",
    "web-host": "web", "operator": "admin/operator", "operator-live": "admin/operator",
    "admin": "admin/operator", "workflow": "admin/operator", "config": "admin/operator",
    "control": "control", "hybrid-control": "control"}


def subsystem(name: str, files) -> str:
    for sub, prefixes in SUBSYSTEM_PREFIX:
        if name.startswith(prefixes):
            return sub
    for relative in sorted(files):
        sub = SUBSYSTEM_FILE.get(Path(relative).stem)
        if sub:
            return sub
    return "nntp/served"


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
                "delegates": _sym(kv.get(":delegates")) if kv.get(":delegates") is not None else None,
                # D40 raw dispatch: the named preservation argument
                "raw_with": [_sym(t) for t in (kv.get(":raw-with") or [])],
                "raw_guarded": kv.get(":raw-guarded"),
            })
    rows = None
    for d in found:
        # `:raw-with (:carried NAME)' (books/def-carried.lisp): only the
        # statements def-carried GENERATES -- NAME-ENTRY-carries and every
        # NAME-PRED-bridge -- resolved here from the def-carried forms of
        # the tree; ACL2 resolves the same from the world's fn-carried table
        # and compares each generated formula with the statement regenerated
        # from the world (books/def-carried.lisp fn-cd-raw-problem).
        raw = d["raw_with"]
        if raw and raw[0] == ":carried":
            if rows is None:
                rows = carried_rows(root)
            # exactly (:carried NAME): anything else resolves to nothing and
            # is a finding (books/definterface.lisp fn-di-raw-with-formp
            # refuses the same forms)
            d["raw_with_carried"] = raw[1] if len(raw) == 2 else "(malformed)"
            d["raw_with"] = (carried_theorems(rows, raw[1], d["name"])
                             if len(raw) == 2 else [])
    return found


CARRIED_SOURCES = "books"


def carried_rows(root: Path = ROOT) -> dict[str, dict]:
    """NAME -> {established, transitions, concludes} of every top-level
    def-carried form in the tree's books, each a list of [function, theorem]."""
    rows: dict[str, dict] = {}
    for path in sorted((root / CARRIED_SOURCES).glob("*.lisp")):
        text = path.read_text(encoding="utf-8")
        if "(def-carried " not in text:
            continue
        for form, _line in ledger.Reader(text).top_level():
            if ledger.head(form) != "def-carried" or len(form) < 2:
                continue
            kv = ledger.keyword_plist(form[2:])
            rows[_sym(form[1])] = {
                key: [[_sym(e[0]), _sym(e[1])] for e in (kv.get(":" + key) or [])
                      if isinstance(e, list) and len(e) >= 2
                      and isinstance(e[0], (str, ledger.Sym)) and isinstance(e[1], (str, ledger.Sym))]
                for key in ("established", "transitions", "concludes")}
            # the opens whose argument def-carried says is PRODUCED: the raw
            # host must never hand them one (books/def-carried.lisp :produced)
            rows[_sym(form[1])]["produced"] = [
                _sym(e[0]) for e in (kv.get(":established") or [])
                if isinstance(e, list) and len(e) >= 2
                and isinstance(e[0], (str, ledger.Sym))
                and any(isinstance(x, (str, ledger.Sym)) and _sym(x) == ":produced"
                        for x in e[2:])]
    return rows


def carried_generated(rows: dict[str, dict]) -> set[str]:
    """Every theorem name the def-carried forms generate."""
    return {"{}-{}-{}".format(name, f, suffix)
            for name, row in rows.items()
            for key, suffix in (("established", "establishes"),
                                ("transitions", "carries"), ("concludes", "bridge"))
            for f, _t in row[key]}


def carried_theorems(rows: dict[str, dict], carried: str | None, entry: str) -> list[str]:
    """The :raw-with theorems of ENTRY through the carried invariant CARRIED,
    all generated: CARRIED-ENTRY-carries and every CARRIED-PRED-bridge;
    [] when there is no such row or ENTRY is not one of its transitions."""
    row = rows.get(carried or "")
    if row is None or not any(f == entry for f, _t in row["transitions"]):
        return []
    return (["{}-{}-carries".format(carried, entry)]
            + ["{}-{}-bridge".format(carried, p) for p, _t in row["concludes"]])


def _lisp_data(value) -> str:
    """Preserve source data, including malformed specs for ACL2 to refuse."""
    if isinstance(value, list):
        return "(" + " ".join(_lisp_data(item) for item in value) + ")"
    if isinstance(value, ledger.Sym):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value)
    return str(value)


def render_raw_declarations(decls: list[dict]) -> str:
    """Selected image table source; absent or invalid targets fail closed."""
    forms = ["; GENERATED by tools/interface_emit.py from raw route declarations.",
             "; No availability filter: an absent target refuses the selected image.",
             '(in-package "ACL2")', '(include-book "../books/definterface")']
    for d in decls:
        guarded = d.get("raw_guarded")
        if not d.get("raw_with") and guarded is None:
            if d["name"] in {"fn-di-raw-with-problem", "fn-di-raw-guarded-problem", "fn-di-raw-guarded-target"}:
                forms.append('(definterface {} :class :{} :direct {})'.format(
                    d["name"], d["class"], json.dumps(d["direct"])))
            continue
        kinds = " ".join("({} {})".format(*pair) for pair in d["kinds"])
        route = ""
        if d.get("raw_with_carried"):
            route += " :raw-with (:carried " + d["raw_with_carried"] + ")"
        elif d.get("raw_with"):
            route += " :raw-with (" + " ".join(d["raw_with"]) + ")"
        if guarded is not None:
            route += " :raw-guarded " + _lisp_data(guarded)
        forms.append("(definterface {} :class :{} :kinds ({}){})".format(
            d["name"], d["class"], kinds, route))
    return "\n".join(forms) + "\n"


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
    # Bindings use host forms and function names, never theorem suspects.
    # Ledger callers requesting suspects still trigger the full analysis.
    tree = ledger.load_tree(lazy=True)
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
    defined = (set(tree.functions) | set(harness_check._acl2_definition_forms(tree, raw))
               | generated_names(root))
    return {"dispatched": dispatched, "direct": direct,
            "defined": defined, "entries": len(dispatched)}


# Functions a macro introduces that the ledger's reader does not list: an
# abstract stobj's exports (`(NAME :logic ...' in a defabsstobj) and a
# defevent's recognizer and encoder.
_GENERATED = re.compile(r"\((fn-[^\s()]+)\s+:logic\s|:(?:recognizer|encode)\s+(fn-[^\s()]+)")


def generated_names(root: Path = ROOT) -> set[str]:
    names: set[str] = set()
    for path in sorted((root / "books").glob("*.lisp")):
        for a, b in _GENERATED.findall(path.read_text(encoding="utf-8", errors="replace")):
            names.add((a or b).lower())
    return names


def subsystem_of(d: dict, reading: dict) -> str:
    return subsystem(d["name"], reading["dispatched"].get(d["name"], ()))


def render_registry(decls: list[dict], reading: dict) -> str:
    rows = []
    for d in decls:
        rows.append({
            "name": d["name"],
            "subsystem": subsystem_of(d, reading),
            "declared_in": d["source"],
            "class": d["class"],
            "kinds": d["kinds"],
            "exempt": d["exempt"],
            "keystones": d["keystones"],
            "extraction": d["root"],
            "direct": d["direct"],
            "delegates": d.get("delegates"),
            "raw_with": d.get("raw_with") or [],
            "raw_with_carried": d.get("raw_with_carried"),
            "raw_guarded": d.get("raw_guarded"),
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
                                           if d["class"] == "common-lisp-compliant"),
                     "with_keystone": sum(1 for d in decls if d["keystones"]),
                     "raw_dispatched": sum(1 for d in decls if d.get("raw_with") or d.get("raw_guarded") is not None)},
        # D40: every entry the host dispatches to its raw (guard-verified)
        # definition, with the theorems its declaration names; ACL2 checks
        # each against the loaded world at image build
        # (books/definterface.lisp fn-di-raw-with-problem).
        "raw_dispatched": [{"name": d["name"], "raw_with": d["raw_with"],
                            "raw_with_carried": d.get("raw_with_carried")}
                           for d in decls if d.get("raw_with")],
        "raw_guarded": [{"name": d["name"], "abi": d["raw_guarded"]}
                        for d in decls if d.get("raw_guarded") is not None],
        "entries": rows,
    }
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


THEOREM_FORM = re.compile(r"^\s*\(defthmd?\s+([^\s()]+)", re.M)


def tree_theorems(root: Path = ROOT) -> set[str]:
    """The names every non-local defthm/defthmd of the tree's books defines
    (a `(local (defthm' line starts with `(local', so it is not one)."""
    found: set[str] = set()
    for path in sorted((root / "books").glob("*.lisp")):
        found.update(m.group(1).lower()
                     for m in THEOREM_FORM.finditer(path.read_text(encoding="utf-8")))
    return found | carried_generated(carried_rows(root))


def findings(decls: list[dict], reading: dict, root: Path = ROOT) -> list[str]:
    out: list[str] = []
    seen: dict[str, str] = {}
    theorems = tree_theorems(root) if any(d.get("raw_with") for d in decls) else set()
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
        if d.get("raw_with_carried") is not None and not d.get("raw_with"):
            out.append("{}: {} :raw-with (:carried {}) resolves to no theorems: no def-carried "
                       "row of that name in {}/ names {} among its transitions".format(
                           where, name, d["raw_with_carried"], CARRIED_SOURCES, name))
        if d.get("raw_with"):
            # D40: the source can say this much; the world check (the guard's
            # carried conjuncts concluded by the named theorems) is ACL2's at
            # image build.
            if d["class"] != "common-lisp-compliant":
                out.append("{}: {} is declared :raw-with but :class {}; only a guard-verified "
                           "entry executes faithfully raw".format(where, name, d["class"]))
            for theorem in d["raw_with"]:
                if theorem not in theorems:
                    out.append("{}: {} :raw-with names {}, which no book defines as a "
                               "non-local theorem".format(where, name, theorem))
    # def-carried :produced: an open whose premises are discharged only at
    # its producers' outputs; the raw host (outside the ACL2 world the
    # caller scan reads) must never call it at all.
    for row_name, row in sorted(carried_rows(root).items()):
        for f in row.get("produced", []):
            for kind in ("dispatched", "direct"):
                if f in reading[kind]:
                    out.append("the raw host {} {} ({}), an open whose argument the "
                               "def-carried row {} says is produced (:produced): only an "
                               "ACL2 caller passing a producer's call may reach it".format(
                                   "dispatches" if kind == "dispatched" else "applies",
                                   f, ", ".join(sorted(reading[kind][f])), row_name))
    for name in sorted(set(reading["dispatched"]) - set(seen)):
        out.append("the raw host dispatches {} ({}) and no definterface declares it".format(
            name, ", ".join(sorted(reading["dispatched"][name]))))
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
    if (not RAW_DECLARATIONS.is_file()
            or RAW_DECLARATIONS.read_text() != render_raw_declarations(decls)):
        out.append("host/interfaces-raw.lisp is not what the declarations say; "
                   "run tools/interface_emit.py --write")
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--kinds", action="store_true",
                        help="also report :class/:kinds disagreements without --check")
    args = parser.parse_args(argv)
    if args.write:
        from tools import acl2_slots  # noqa: E402
        acl2_slots.refuse_on_laptop("tools/interface_emit.py --write")
    decls = declarations()
    reading = host_reading()
    if args.write:
        ROOTS_SH.write_text(render_roots(decls))
        REGISTRY.write_text(render_registry(decls, reading))
        RAW_DECLARATIONS.write_text(render_raw_declarations(decls))
    problems = findings(decls, reading)
    # the raw host reaches a book function only through the dispatcher
    # (tools/raw_dispatch_rule.py: r28-F1, by construction)
    from tools import raw_dispatch_rule
    rule_problems, covered = raw_dispatch_rule.findings(declared={d["name"] for d in decls})
    print(raw_dispatch_rule.summary(covered, rule_problems))
    problems += rule_problems
    if args.check or args.kinds:
        # the image build's :class / :kinds check, estimated from the source
        # (tools/interface_kinds.py, obstructions-8 item 68)
        from tools import interface_kinds
        judged, skipped = interface_kinds.judge(
            decls, interface_kinds.read_source(interface_kinds.tree_files()))
        problems += judged
        print("interface_emit: :class/:kinds as the image build checks them: {} "
              "disagreement(s), {} declaration(s) the source cannot judge".format(
                  len(judged), skipped))
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
