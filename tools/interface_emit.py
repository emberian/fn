#!/usr/bin/env python3
"""The registry half of `definterface': the host-called entries, generated.

`(definterface NAME :class C [:kinds ...] [:exempt ...] [:keystones ...]
[:root :extract|:extract-extra] [:direct "why"] [:raw-with (THM ...)])`
(books/definterface.lisp)
declares a host-called entry; ACL2 checks each declaration against the
image's world when host/native/build.lisp loads host/interfaces.lisp (the
extraction world loads the same file, tools/extract/world-host.lisp).  This reads
the same forms with the ledger's non-evaluating reader and GENERATES:

* planning/interfaces.json -- one row per declared entry: its class, the
  kinds its guard gives the host entry guard, its exempt formals with their
  reasons, its keystones, its extraction role, whether the raw host applies
  it directly, the theorems of its `:raw-with` argument (D40: the host
  dispatches the entry to its guard-verified definition, not its executable
  counterpart; the top-level `raw_dispatched` lists those entries), and the
  raw host files that dispatch it;
* tools/extract/roots.sh -- the extractor's default ROOTS and EXTRA
  (tools/depth_check.py reads it), in declaration order;
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
* a `:raw-with (:carried NAME)` when any dispatch is undeclared:
  def-carried's completeness depends on the complete interface table;
* a `:raw-with (:carried NAME [:assuming A-ID])` whose :assuming is not
  exactly the assumption the row's named escape `:incomplete (A-ID ...)`
  states (books/def-carried.lisp), or names an assumption that
  specs/failures.md does not register;
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

* a keystone whose defthm formula never mentions its target (the :via or
  :step-of function, else the entry): the static half of
  fn-di-keystone-problem (keystone_findings; a :via target's call closure is read from the source too);

What it cannot check is the world: the keystones' call closure, and the class and kinds
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

from tools import box_artifacts, interfaces_relocate, ledger  # noqa: E402

SOURCES = ("host/interfaces.lisp", "host/account-adoption-interfaces.lisp")
# a box-step artifact, never committed (tools/box_artifacts.py)
REGISTRY = ROOT / box_artifacts.DIR / "interfaces.json"
ROOTS_SH = ROOT / "tools" / "extract" / "roots.sh"
RAW_DECLARATIONS = ROOT / "host" / "interfaces-raw.lisp"
STEP_OF_STATUS = "keystone via fold; host-loop correspondence owed"

KEYS = {":class", ":kinds", ":exempt", ":keystones", ":root", ":direct", ":delegates",
        ":raw-with", ":raw-guarded", ":operation"}

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


def declaration_files(root: Path = ROOT) -> list[str]:
    """Where definterface forms live: SOURCES (the book-defined entries), then every
    other host file that declares an entry where it defines it
    (tools/interfaces_relocate.py), in the order host/native/build.lisp loads them,
    unloaded ones last by name."""
    order: dict[str, int] = {}
    build = root / "host" / "native" / "build.lisp"
    if build.is_file():
        order = interfaces_relocate.load_order(root)
    declared = sorted(
        (r for r in interfaces_relocate.host_files(root)
         if Path(r).name != RAW_DECLARATIONS.name
         and "(definterface " in (root / r).read_text(encoding="utf-8")),
        key=lambda r: (order.get(r, len(order)), r))
    return list(SOURCES) + [r for r in declared if r not in SOURCES]


def declarations(root: Path = ROOT) -> list[dict]:
    """Every definterface form in declaration_files, in order, parsed."""
    found: list[dict] = []
    for relative in declaration_files(root):
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
                if isinstance(entry, list) and _sym(entry[1]) == ":step-of":
                    # A theorem about the fold the host drives one step at a
                    # time (books/definterface.lisp): never the entry's proof.
                    row = {"theorem": _sym(entry[0]), "step_of": _sym(entry[2]),
                           "status": STEP_OF_STATUS}
                    if len(entry) > 3:
                        row["step"] = _sym(entry[3])
                    keystones.append(row)
                elif isinstance(entry, list):
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
                **({"operation": {key.lstrip(":"): ledger.source_text(value)
                                   for key, value in ledger.keyword_plist(kv[":operation"]).items()}}
                   if kv.get(":operation") is not None else {}),
            })
    found.sort(key=lambda d: d["name"])  # declaration order is the files' layout, not a fact
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
            # exactly (:carried NAME) or (:carried NAME :assuming A-ID):
            # anything else resolves to nothing and is a finding
            # (books/definterface.lisp fn-di-raw-with-formp refuses the
            # same forms)
            wellformed = len(raw) == 2 or (len(raw) == 4 and raw[2] == ":assuming")
            d["raw_with_carried"] = raw[1] if wellformed else "(malformed)"
            d["raw_with_assuming"] = raw[3] if wellformed and len(raw) == 4 else None
            d["raw_with"] = (carried_theorems(rows, raw[1], d["name"])
                             if wellformed else [])
    return found


# A def-carried row is a book's or, when its transitions are host functions
# (the owner's writers, host/owner-host.lisp), an ld'd host file's
# (host/owner-served-carried.lisp).
CARRIED_SOURCES = ("books", "host")
FAILURES = ROOT / "specs" / "failures.md"


def carried_rows(root: Path = ROOT) -> dict[str, dict]:
    """NAME -> {established, transitions, concludes, source, incomplete} of
    every top-level def-carried form in the tree's books and host files,
    each of the first three a list of [function, theorem]; incomplete is
    [A-ID, [OWED ...]] for a row with def-carried's named escape, else None."""
    rows: dict[str, dict] = {}
    for path in [p for d in CARRIED_SOURCES for p in sorted((root / d).glob("*.lisp"))]:
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
            rows[_sym(form[1])]["source"] = path.relative_to(root).as_posix()
            incomplete = kv.get(":incomplete")
            rows[_sym(form[1])]["incomplete"] = (
                [_sym(incomplete[0]), [_sym(x) for x in incomplete[1]]]
                if isinstance(incomplete, list) and len(incomplete) == 2
                and isinstance(incomplete[1], list) else None)
            # the opens whose argument def-carried says is PRODUCED: the raw
            # host must never hand them one (books/def-carried.lisp :produced)
            rows[_sym(form[1])]["produced"] = [
                _sym(e[0]) for e in (kv.get(":established") or [])
                if isinstance(e, list) and len(e) >= 2
                and isinstance(e[0], (str, ledger.Sym))
                and any(isinstance(x, (str, ledger.Sym)) and _sym(x) == ":produced"
                        for x in e[2:])]
    writer_rows(root, rows)
    return rows


# books/def-carried-writer.lisp: a `(def-carried-writers-row NAME :profile P
# :from PILOT)` form (a book or an ld'd host file) is a def-carried row ACL2
# writes from the pilot's row and the table of writers declared against P --
# `(def-carried-writer FN :profile P ...)` or a profile's shorthand, a
# `(defmacro M (fn &rest kvs) `(def-carried-writer ,fn :profile P ,@kvs))`
# read from its own definition, never from a map typed here.  The same forms
# are mirrored: the pilot's open and bridges, the transitions the pilot's
# then the writers' (FN, its theorem FN-preserves-SUFFIX, the profile's
# :suffix or its invariant, or the writer's :name), the bridges the pilot's
# then the writers' :bridges.
WRITER_SOURCES = ("books", "host")


def _writer_forms(root: Path):
    for directory in WRITER_SOURCES:
        for path in sorted((root / directory).glob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            if "def-carried" not in text and "defmacro" not in text:
                continue
            for form, _line in ledger.Reader(text).top_level():
                yield form


def _shorthand_profile(form) -> str | None:
    """The profile P of (defmacro M (fn &rest kvs) `(def-carried-writer ,fn
    :profile P ,@kvs)), else None."""
    if ledger.head(form) != "defmacro" or len(form) < 4:
        return None
    body = form[3]
    if not (isinstance(body, list) and len(body) == 2
            and ledger.head(body) == "quasiquote" and isinstance(body[1], list)):
        return None
    inner = body[1]
    if ledger.head(inner) != "def-carried-writer" or len(inner) < 4:
        return None
    if not (isinstance(inner[1], list) and ledger.head(inner[1]) == "unquote"):
        return None
    if _sym(inner[2]) != ":profile" or not isinstance(inner[3], (str, ledger.Sym)):
        return None
    return _sym(inner[3])


def _add_writer(writers: list, profile: str, fn: str, kv: dict) -> None:
    # a writer is declared once (ACL2 refuses the second); the mirror refuses too
    if any(p == profile and f == fn for p, f, _kv in writers):
        raise ValueError("{} is declared a writer of {} twice".format(fn, profile))
    writers.append((profile, fn, kv))


def writer_rows(root: Path, rows: dict[str, dict]) -> None:
    profiles: dict[str, dict] = {}
    shorthands: dict[str, str] = {}
    writers: list[tuple[str, str, dict]] = []     # (profile, fn, options)
    row_forms: list[tuple[str, dict]] = []
    for form in _writer_forms(root):
        head = ledger.head(form)
        if head == "def-carried-profile" and len(form) >= 2:
            kv = ledger.keyword_plist(form[2:])
            profiles[_sym(form[1])] = {
                "invariant": _sym(kv[":invariant"]) if kv.get(":invariant") is not None else "",
                "suffix": _sym(kv[":suffix"]) if kv.get(":suffix") is not None else None}
        elif head == "def-carried-writer" and len(form) >= 2:
            kv = ledger.keyword_plist(form[2:])
            if kv.get(":profile") is not None:
                _add_writer(writers, _sym(kv[":profile"]), _sym(form[1]), kv)
        elif head == "def-carried-writers-row" and len(form) >= 2:
            row_forms.append((_sym(form[1]), ledger.keyword_plist(form[2:])))
        elif (profile := _shorthand_profile(form)) is not None:
            shorthands[_sym(form[1])] = profile
        elif head in shorthands and len(form) >= 2:
            _add_writer(writers, shorthands[head], _sym(form[1]), ledger.keyword_plist(form[2:]))
    for name, kv in row_forms:
        profile_name = _sym(kv[":profile"]) if kv.get(":profile") is not None else ""
        pilot = rows.get(_sym(kv[":from"]) if kv.get(":from") is not None else "")
        profile = profiles.get(profile_name)
        if pilot is None or profile is None:
            continue
        suffix = profile["suffix"] or profile["invariant"]
        transitions = list(pilot["transitions"])
        concludes = list(pilot["concludes"])
        for p, fn, options in writers:
            if p != profile_name:
                continue
            theorem = (_sym(options[":name"]) if options.get(":name") is not None
                       else "{}-preserves-{}".format(fn, suffix))
            transitions.append([fn, theorem])
            for bridge in options.get(":bridges") or []:
                if not (isinstance(bridge, list) and len(bridge) == 2):
                    raise ValueError("{}: {} :bridges entry {} is not (PRED THM)".format(
                        name, fn, ledger.source_text(bridge)))
                pred, thm = _sym(bridge[0]), _sym(bridge[1])
                held = [c for c in concludes if c[0] == pred]
                if held and held[0][1] != thm:
                    # ACL2 refuses the row (fn-cw-merge-bridges); the mirror must not
                    # quietly keep one of the two
                    raise ValueError("{}: the bridge for {} is named twice with different "
                                     "theorems, {} and {}".format(name, pred, held[0][1], thm))
                if not held:
                    concludes.append([pred, thm])
        rows[name] = {"established": list(pilot["established"]),
                      "transitions": transitions, "concludes": concludes,
                      "produced": list(pilot["produced"])}


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


DTN_BUILD = ROOT / "host" / "native" / "build-dtn.lisp"


def dtn_host_files(path: Path = DTN_BUILD) -> set[str] | None:
    """The host files build-dtn.lisp ld's (repository-relative), or None
    when it cannot be read (then nothing is scoped out)."""
    if not path.is_file():
        return None
    return set(re.findall(r'^\(ld "(host/[^"]+\.lisp)"', path.read_text(encoding="utf-8"), re.M))


def raw_guarded_books(decls: list[dict], root: Path = ROOT) -> list[str]:
    """Literal stobj ABI slots require their defining books in the raw world.

    Derive dependencies from source definitions, never from a live ACL2 world
    or an availability filter. Malformed ABIs remain for definterface to refuse.
    """
    needed: set[str] = set()
    for declaration in decls:
        spec = declaration.get("raw_guarded")
        if not isinstance(spec, list) or len(spec) != 3:
            continue
        for slots in spec[1:]:
            if not isinstance(slots, list):
                continue
            needed.update(_sym(slot) for slot in slots
                          if isinstance(slot, ledger.Sym) and _sym(slot) not in {"nil", "state"})
    if not needed:
        return []
    definitions: dict[str, list[str]] = {name: [] for name in needed}
    for path in sorted((root / "books").rglob("*.lisp")):
        source = path.read_text(encoding="utf-8")
        # Only parse candidate definitions, keeping ordinary emission scoped.
        if not any(re.search(r"\(def(?:abs)?stobj\s+" + re.escape(name) + r"(?=\s|\))",
                             source, re.I) for name in needed):
            continue
        for form, _line in ledger.Reader(source).top_level():
            if ledger.head(form) in {"defstobj", "defabsstobj"} and len(form) > 1:
                name = _sym(form[1])
                if name in definitions:
                    definitions[name].append(path.relative_to(root).with_suffix("").as_posix())
    for name, books in definitions.items():
        if len(books) != 1:
            raise ValueError("raw-guarded stobj {} needs one literal defining book; found {}".format(
                name, ", ".join(books) or "none"))
    return sorted({books[0] for books in definitions.values()})


def raw_route_books(decls: list[dict], root: Path = ROOT) -> list[str]:
    """The emitted raw routes need their entry/proof books as well as stobjs.

    fn-hroot-*-demand lives outside the stobj-defining book; selecting only
    ABI stobjs made interfaces-raw depend on the surrounding image world.
    """
    from tools import interfaces_relocate
    books = raw_guarded_books(decls, root)
    held = interfaces_relocate.include_closure(
        root, ["books/definterface.lisp", *[book + ".lisp" for book in books]])
    needed = {name for d in decls if (d.get("raw_with") or d.get("raw_guarded") is not None)
              and not d.get("raw_with_carried")
              for name in [d["name"], *d.get("raw_with", [])]}
    # Parse only candidate definition sites. Generated creators are already
    # covered by raw_guarded_books; missing declarations remain gate findings.
    pattern = re.compile(r"\((?:defun|defund|defthm|defthmd)\s+(" +
                         "|".join(re.escape(n) for n in sorted(needed)) + r")(?=[\s)])", re.I)
    for path in sorted((root / "books").glob("*.lisp")) if needed else []:
        if not pattern.search(path.read_text(encoding="utf-8")):
            continue
        book = ledger.analyze_book(path, path.relative_to(root).as_posix())
        if not needed.intersection(book.definitions):
            continue
        rel = path.relative_to(root).as_posix()
        if rel not in held:
            books.append(rel[:-5])
            held.update(interfaces_relocate.include_closure(root, [rel]))
    return books


def render_raw_declarations(decls: list[dict], rows: dict | None = None,
                            scope: set[str] | None = None, root: Path = ROOT) -> str:
    """Selected image table source; absent or invalid targets fail closed.
    The one scope rule, written into the file: a `:raw-with (:carried ROW)'
    whose ROW is defined in a host file the DTN build does not load is
    outside the DTN image (its row and its entry are not in that world),
    and is listed as such, never dropped silently."""
    rows = rows or {}
    forms = ["; GENERATED by tools/interface_emit.py from raw route declarations.",
             "; No availability filter: an absent target refuses the selected image.",
             '(in-package "ACL2")', '(include-book "../books/definterface")']
    forms.extend('(include-book "../{}")'.format(book)
                 for book in raw_route_books(decls, root))
    for d in decls:
        row_source = (rows.get(d.get("raw_with_carried") or "") or {}).get("source", "")
        if (scope is not None and row_source.startswith("host/")
                and row_source not in scope):
            forms.append("; outside the DTN image: {} :raw-with (:carried {}), whose row is "
                         "defined in {}, which host/native/build-dtn.lisp does not load".format(
                             d["name"], d["raw_with_carried"], row_source))
            continue
        guarded = d.get("raw_guarded")
        if not d.get("raw_with") and guarded is None:
            if d["name"] in {"fn-di-raw-with-problem", "fn-di-raw-guarded-problem", "fn-di-raw-guarded-target"}:
                forms.append('(definterface {} :class :{} :direct {})'.format(
                    d["name"], d["class"], json.dumps(d["direct"])))
            continue
        kinds = " ".join("({} {})".format(*pair) for pair in d["kinds"])
        route = ""
        if d.get("raw_with_carried"):
            route += " :raw-with (:carried " + d["raw_with_carried"] + (
                " :assuming " + d["raw_with_assuming"].upper() if d.get("raw_with_assuming") else "") + ")"
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
            "# declarations in host/interfaces.lisp.\n"
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
# abstract stobj's exports (`(NAME :logic ...' in a defabsstobj, `(:read NAME
# :logic ...' in a def-generic) and a
# defevent's recognizer and encoder.
_GENERATED = re.compile(r"\((?::(?:read|update)\s+)?(fn-[^\s()]+)\s+:logic\s|:(?:recognizer|encode)\s+(fn-[^\s()]+)")


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
                        "(books/definterface.lisp) in host/interfaces.lisp; "
                        "ACL2 checks each against the world "
                        "at image build.  Do not edit; regenerate."),
        # The raw host's total entry count is printed, not written: it moves
        # with every host change, and a registry row should not.
        "coverage": {"declared": len(decls),
                     "declared_and_dispatched": sum(1 for d in decls
                                                    if d["name"] in reading["dispatched"]),
                     "guard_verified": sum(1 for d in decls
                                           if d["class"] == "common-lisp-compliant"),
                     # a :step-of keystone is about the fold, not the entry
                     "with_keystone": sum(1 for d in decls
                                          if any("step_of" not in k for k in d["keystones"])),
                     "with_fold_keystone_only": sum(1 for d in decls if d["keystones"] and all(
                         "step_of" in k for k in d["keystones"])),
                     "raw_dispatched": sum(1 for d in decls if d.get("raw_with") or d.get("raw_guarded") is not None)},
        # D40: every entry the host dispatches to its raw (guard-verified)
        # definition, with the theorems its declaration names; ACL2 checks
        # each against the loaded world at image build
        # (books/definterface.lisp fn-di-raw-with-problem).
        "raw_dispatched": [dict({"name": d["name"], "raw_with": d["raw_with"],
                                 "raw_with_carried": d.get("raw_with_carried")},
                                **({"raw_with_assuming": d["raw_with_assuming"].upper(),
                                    "raw_dispatch_trust": "temporary-native-dispatch"}
                                   if d.get("raw_with_assuming") else {}))
                           for d in decls if d.get("raw_with")],
        "raw_guarded": [{"name": d["name"], "abi": d["raw_guarded"]}
                        for d in decls if d.get("raw_guarded") is not None],
        "entries": rows,
    }
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


def tree_theorems(root: Path = ROOT) -> set[str]:
    """Non-local theorems, including the ledger's shared generator mirrors."""
    found: set[str] = set()
    for path in sorted((root / "books").glob("*.lisp")):
        book = ledger.analyze_book(path, path.relative_to(root).as_posix())
        found.update(theorem.name for theorem in book.theorems if not theorem.local)
    return found | carried_generated(carried_rows(root))


def registered_assumptions(path: Path) -> set[str]:
    """The assumption ids specs/failures.md registers: its table rows
    `| A-ID | ... |`, lower-cased as the reader reads symbols."""
    if not path.is_file():
        return set()
    return {m.group(1).lower() for m in
            re.finditer(r"^\|\s*(A-[A-Z0-9-]+)\s*\|", path.read_text(encoding="utf-8"), re.M)}


def assumption_findings(where: str, d: dict, rows: dict, registered: set[str]) -> list[str]:
    """def-carried's named escape, written at the entry: a :raw-with over a
    row with :incomplete (A-ID ...) says :assuming A-ID exactly, over a row
    without one says no :assuming, and A-ID is a registered assumption."""
    row = rows.get(d["raw_with_carried"]) or {}
    owed = row.get("incomplete")
    assuming = d.get("raw_with_assuming")
    out = []
    if owed and assuming != owed[0]:
        out.append("{}: {} :raw-with (:carried {}) relies on a row complete only under the "
                   "named assumption {}: write :raw-with (:carried {} :assuming {})".format(
                       where, d["name"], d["raw_with_carried"], owed[0].upper(),
                       d["raw_with_carried"], owed[0].upper()))
    elif assuming and not owed:
        out.append("{}: {} :raw-with (:carried {} :assuming {}): the row declares no "
                   ":incomplete escape, so the assumption names nothing it rests on".format(
                       where, d["name"], d["raw_with_carried"], assuming.upper()))
    if assuming and assuming not in registered:
        out.append("{}: {} :raw-with ... :assuming {}, which specs/failures.md does not "
                   "register (a named assumption is a row of its table)".format(
                       where, d["name"], assuming.upper()))
    return out


def findings(decls: list[dict], reading: dict, root: Path = ROOT) -> list[str]:
    out: list[str] = []
    seen: dict[str, str] = {}
    undeclared = sorted(set(reading["dispatched"]) - {d["name"] for d in decls})
    theorems = tree_theorems(root) if any(d.get("raw_with") for d in decls) else set()
    rows = carried_rows(root) if any(d.get("raw_with_carried") for d in decls) else {}
    registered = (registered_assumptions(root / "specs" / "failures.md")
                  if any(d.get("raw_with_carried") for d in decls) else set())
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
        if d.get("raw_with_carried") is not None and undeclared:
            # Generated theorem names alone cannot establish completeness:
            # an undeclared dispatch may write the carried state without
            # appearing in the world's fn-interfaces table.
            out.append("{}: {} :raw-with (:carried {}) cannot rely on def-carried's "
                       "completeness: requires 0 undeclared dispatches; undeclared entries: {}".format(
                           where, name, d["raw_with_carried"], ", ".join(undeclared)))
        if d.get("raw_with_carried") is not None and not d.get("raw_with"):
            out.append("{}: {} :raw-with (:carried {}) resolves to no theorems: no def-carried "
                       "row of that name in {} names {} among its transitions".format(
                           where, name, d["raw_with_carried"],
                           " or ".join(s + "/" for s in CARRIED_SOURCES), name))
        if d.get("raw_with_carried") is not None:
            out.extend(assumption_findings(where, d, rows, registered))
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
    for name in undeclared:
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
    try:
        box_artifacts.path("interfaces.json", root)
    except box_artifacts.Refused as error:
        out.append(str(error))
    if not REGISTRY.is_file() or REGISTRY.read_text() != render_registry(decls, reading):
        out.append("build/box/interfaces.json is not what the declarations say; "
                   "run tools/interface_emit.py --write (the box step)")
    if (not RAW_DECLARATIONS.is_file()
            or RAW_DECLARATIONS.read_text() != render_raw_declarations(
                decls, carried_rows(root), dtn_host_files(root / "host" / "native" / "build-dtn.lisp"))):
        out.append("host/interfaces-raw.lisp is not what the declarations say; "
                   "run tools/interface_emit.py --write")
    return out


def _mentions(form, target: str) -> bool:
    """Does the symbol TARGET occur in FORM outside a quoted datum?  The
    structural reader's reading of fn-di-keystone-problem's all-fnnames."""
    stack = [form]
    while stack:
        item = stack.pop()
        if isinstance(item, ledger.Sym):
            if str(item).lower() == target:
                return True
        elif isinstance(item, list) and item and not (
                isinstance(item[0], ledger.Sym) and str(item[0]).lower() == "quote"):
            stack.extend(item)
    return False


def _body_symbols(form, out: set, heads: set | None = None) -> None:
    """Add every symbol of FORM outside a quote to OUT, and the symbols in
    call position to HEADS."""
    if isinstance(form, ledger.Sym):
        out.add(str(form).lower())
    elif isinstance(form, list) and form and not (
            isinstance(form[0], ledger.Sym) and str(form[0]).lower() == "quote"):
        if heads is not None and isinstance(form[0], ledger.Sym):
            heads.add(str(form[0]).lower())
        for item in form:
            _body_symbols(item, out, heads)


def macro_bodies(files) -> dict[str, list]:
    """defmacro name -> its definition form, and name -> the top-level form
    that generates it (a macro call whose first argument is NAME), for the
    closure to read through."""
    out: dict[str, list] = {}
    origin: dict[str, str] = {}
    invocations: dict[str, list] = {}

    def visit(form):
        if not isinstance(form, list) or not form:
            return
        head = ledger.head(form)
        if head == "defmacro" and len(form) > 3 and isinstance(form[1], ledger.Sym):
            out.setdefault(str(form[1]).lower(), form)
            stack = [form]
            while stack:  # a defun written out inside the macro's template
                node = stack.pop()
                if isinstance(node, list):
                    if (len(node) > 3 and isinstance(node[0], ledger.Sym) and str(node[0]).lower() == "defun"
                            and isinstance(node[1], ledger.Sym)):
                        out.setdefault(str(node[1]).lower(), node)
                        origin.setdefault(str(node[1]).lower(), str(form[1]).lower())
                    stack.extend(node)
        elif head in ("progn", "encapsulate", "local", "with-output", "defsection"):
            for item in form[1:]:
                visit(item)
        else:
            if isinstance(form[0], ledger.Sym):
                invocations.setdefault(str(form[0]).lower(), []).append(form)
            if (len(form) > 2 and isinstance(form[1], ledger.Sym)
                    and head not in ("definterface", "defthm", "defthmd", "defthm-inline",
                                     "verify-guards", "in-theory", "deftheory", "defconst")):
                out.setdefault(str(form[1]).lower(), form)

    for _relative, text in files:
        for form, _line in ledger.Reader(text).top_level():
            visit(form)
    # a function a macro template writes out is also read through every
    # call of that macro (its rows are what the template's body calls)
    for fn, macro in origin.items():
        out[fn] = out[fn] + [call for call in invocations.get(macro, [])]
    return out


def call_closure(name: str, source, macros: dict[str, list]) -> tuple[set[str], bool]:
    """(closure, certain): books/definterface.lisp's fn-di-callees over the
    source -- NAME and every function some function in it mentions in its
    definition body.  The walk is a superset of all-fnnames: any symbol
    outside a quote, and through a tree macro every symbol of its definition
    (its expansion is the world's, and can call only what the macro names).
    A function the reader sees no defun for is read through the top-level
    form that names it first (its generator), else it is a leaf.  certain is False only when NAME itself is not a
    defun the reader sees (or a template's): then a miss is not a finding."""
    seen: set[str] = set()
    todo = [name]
    certain = name in source.definitions or name in macros
    while todo:
        fn = todo.pop()
        if fn in seen:
            continue
        seen.add(fn)
        defined = fn in source.definitions
        form = source.definitions[fn].form if defined else macros.get(fn)
        if form is None:
            continue
        symbols: set[str] = set()
        _body_symbols(form[-1] if defined else form[2:], symbols)
        todo.extend(symbols)
    return seen, certain


def keystone_findings(decls: list[dict], root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(findings, unresolved): the STATIC half of books/definterface.lisp's
    fn-di-keystone-problem, for the image build's host-ld.

    That check refuses a keystone whose theorem (1) is no theorem of the world,
    (2) whose formula does not call its target -- the :via function, the
    :step-of fold, or, for a bare keystone, the entry itself -- or (3) whose
    target is not in the entry's call closure.  A source reader can decide
    (2): the keystone's defthm is read structurally with the ledger's
    non-evaluating reader and the target must occur among its formula's
    symbols outside a quote (never a text search: a comment or docstring
    cannot satisfy it).  n-bp-heap landed a keystone whose formula never
    mentioned its :via target and only host-ld, at an image build, said so
    (CONVERGE-3 row 43).  Not decided here: (3) for a :step-of keystone and a closure
    through a tree macro, which need the world and stay with host-ld; and a keystone with no
    non-local defthm in books/ (generated by a macro the ledger does not model,
    or defined elsewhere), listed in UNRESOLVED by name, never silently
    passed, and not a finding."""
    wanted: dict[str, list[tuple[dict, str]]] = {}
    for d in decls:
        for k in d["keystones"]:
            target = k.get("via") or k.get("step_of") or d["name"]
            wanted.setdefault(k["theorem"], []).append((d, target))
    formulas: dict[str, list] = {}
    for path in sorted((root / "books").glob("*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace").lower()
        if not any(name in text for name in wanted):
            continue
        book = ledger.analyze_book(path, path.relative_to(root).as_posix())
        for theorem in book.theorems:
            if theorem.name in wanted and not theorem.local:
                formulas.setdefault(theorem.name, []).append(theorem.statement)
    problems, unresolved = [], []
    k_via = {(d["name"], k["theorem"]): True for d in decls for k in d["keystones"] if k.get("via")}
    source = None
    macros: dict[str, list] = {}
    cache: dict[str, tuple[set[str], bool]] = {}

    def closures(name):
        nonlocal source
        if source is None:
            from tools import interface_kinds
            if root == ROOT:
                files = interface_kinds.tree_files()
            else:
                files = [(p.relative_to(root).as_posix(), p.read_text(encoding="utf-8"))
                         for sub in ("books", "host") for p in sorted((root / sub).glob("*.lisp"))]
            source = interface_kinds.read_source(files)
            macros.update(macro_bodies(files))
        if name not in cache:
            cache[name] = call_closure(name, source, macros)
        return cache[name]

    for theorem, uses in sorted(wanted.items()):
        for d, target in uses:
            where = "{}:{}".format(d["source"], d["line"])
            if theorem not in formulas:
                unresolved.append("{}: {} keystone {}: no non-local defthm of that name in books/".format(
                    where, d["name"], theorem))
            elif not any(_mentions(f, target) for f in formulas[theorem]):
                problems.append(
                    "{}: {} keystone {} does not call {}: its formula never mentions it "
                    "(fn-di-keystone-problem refuses this at host-ld)".format(
                        where, d["name"], theorem, target))
            elif k_via.get((d["name"], theorem)):
                closure, certain = closures(d["name"])
                if target not in closure:
                    if certain:
                        problems.append(
                            "{}: {} keystone {}'s function {} is not in {}'s call closure "
                            "(fn-di-keystone-problem refuses this at host-ld)".format(
                                where, d["name"], theorem, target, d["name"]))
                    else:
                        unresolved.append(
                            "{}: {} keystone {} :via {}: call closure not decidable from source".format(
                                where, d["name"], theorem, target))
    return problems, unresolved


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
        box_artifacts.path("interfaces.json")  # refuses a committed copy by name
        REGISTRY.parent.mkdir(parents=True, exist_ok=True)
        REGISTRY.write_text(render_registry(decls, reading))
        RAW_DECLARATIONS.write_text(render_raw_declarations(decls, carried_rows(), dtn_host_files()))
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
        # def-carried's completeness at the image: every declared entry that
        # returns the carried state is listed or owed (tools/carried_entries.py)
        from tools import carried_entries
        carried_problems, carried_undecided = carried_entries.findings(decls, interface_kinds)
        problems += carried_problems
        print("interface_emit: def-carried completeness as the image build checks it: {} "
              "finding(s), {} entr(ies) the source cannot decide (listed by "
              "tools/carried_entries.py, not failures)".format(
                  len(carried_problems), len(carried_undecided)))
        keystone_problems, unresolved = keystone_findings(decls)
        problems += keystone_problems
        print("interface_emit: keystones, the formula-mentions-its-target half of "
              "fn-di-keystone-problem: {} finding(s), {} unresolved (listed, not failures; the "
              "a :via call closure the source cannot decide stays with host-ld)".format(len(keystone_problems), len(unresolved)))
        for line in unresolved:
            print("  unresolved " + line)
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
