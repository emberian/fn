#!/usr/bin/env python3
"""Every read of a retained payload says which KIND it takes: handle or octets.

Since the records flip (PKT-635) the retained article's payload
(`fn-article-payload`, books/acceptance.lisp) and the held row's
(`fn-held-payload`, books/held-record.lisp) are HANDLES
(books/payload-kinds.lisp `fn-payload-handle-p`): naturals naming an arena
payload, whose octets are `fn-handle-bytes` of the handle.  On 2026-09-27 six
defects handed such a handle to a function that reads octets -- moderation's
held body, the BP request ADU, the 9P article entries, the control HDR status,
reclaim's counts -- and every one was a silent refusal downstream, because
the tree's functions are total (`:guard t`) and a natural is a perfectly good
argument to `consp`/`len`.  A guard cannot catch what the tree's style never
states, so this check reads what the source does with the value.

For every definition (not theorem) in books/ and the ACL2-mode host files, an
occurrence of `(fn-article-payload X)` or `(fn-held-payload X)` is accepted
when the value goes

  * directly into a HANDLE SINK: a function declared, in a book,
    `(fn-payload-kind FN :handle "why")` -- it reads the arena at the
    handle, tests it as a natural, or ignores it (payload-kinds.lisp declares
    the arena readers and the record constructors);
  * into a `let`/`let*` binding whose every use is itself accepted (one hop);
  * or when the ENCLOSING function is declared `(fn-payload-kind FN :wire
    "why")`: its articles are the octet model's (alpha, fn-articles-wire-of),
    so its payload IS octets.

Anything else is a finding: the function consumes a handle without saying
which kind it takes.  WAIVERS below name the known live defects owned by
another lane (each with its owner); a waiver whose finding is gone is itself
a finding, so the table only shrinks.

    python3 tools/payload_kind_check.py            # findings, exit 1 if any
    python3 tools/payload_kind_check.py --report   # everything, exit 0
    python3 tools/payload_kind_check.py --json build/payload-kind.json
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

ACCESSORS = {"fn-article-payload", "fn-held-payload"}
DEFINERS = {"defun", "defund", "defun-inline", "defun-nx", "define"}
DECLARER = "fn-payload-kind"

# Known live handle-as-octets consumers, owned elsewhere: (book, function) ->
# owner.  Each is a defect; the entry leaves this table when the owner's fix
# merges (a stale entry is a finding).
WAIVERS: dict[tuple[str, str], str] = {
    # Live defects this lane found and did not fix (each a packet in
    # planning/backlog-2026-09-25.md; the owner fixes, then drops the row).
    ("books/control-served.lisp", "fn-ctl-control-status"):
        "PKT-EG-1: the control status reads the target and keys of a handle",
    ("books/control-served.lisp", "fn-ctl-served-status"):
        "PKT-EG-1: the served control status reads the target and keys of a handle",
    ("books/nntp.lisp", "fn-nntp-control-hdr-response"):
        "PKT-EG-1: HDR :fn-control reads the target of a handle",
    ("books/store-reclaim.lisp", "fn-rcl-verdict"):
        "PKT-EG-2: never :already-reclaimed over a handle",
    ("books/store-reclaim.lisp", "fn-rcl-summary"):
        "PKT-EG-2: reclaimable and freed octets count a handle's len (0)",
    ("books/owner.lisp", "fn-own-feed-reply"):
        "PKT-EG-2b: the book owner's feed reply sends fn-own-feed-article's handle "
        "(the host reads fn-ofa-feed-article)",
    ("books/stx-index.lisp", "fn-stx-index-of-store"):
        "PKT-EG-3: parses a handle; benign only because live callers pass a NIL keyring",
    # Pre-flip twins with no live caller: they compare a handle with octets.
    ("books/store-node.lisp", "fn-sn-existing-action"): "PKT-EG-4: retire (pre-flip twin)",
    ("books/poster-bytes.lisp", "fn-pb-existing-action"): "PKT-EG-4: retire (pre-flip twin)",
    ("books/poster-bytes-buffer.lisp", "fn-pbb-existing-action"): "PKT-EG-4: retire (pre-flip twin)",
    ("books/store-reclaim.lisp", "fn-rcl-existing-action"): "PKT-EG-4: retire (pre-flip twin)",
    ("books/store-reclaim-buffer.lisp", "fn-rclb-existing-action"): "PKT-EG-4: retire (pre-flip twin)",
    ("books/moderation-verbs.lisp", "fn-mvb-held-article"):
        "matrix-reds (the sixth instance, 2026-09-27)",
    ("books/bp-outbound.lisp", "fn-bpo-request-message"):
        "bp-sender READY (PKT-843)",
}


def forms_of(relative: str) -> list[tuple[object, int]]:
    return ledger.Reader((ROOT / relative).read_text(encoding="utf-8")).top_level()


def definitions(form, line: int, out: list) -> None:
    name = ledger.head(form)
    if name is None:
        return
    if name in ("progn", "encapsulate", "local", "with-output", "defsection",
                "mutual-recursion", "make-event"):
        for item in form[1:]:
            definitions(item, line, out)
        return
    if name in DEFINERS and len(form) >= 4 and isinstance(form[1], ledger.Sym):
        out.append((str(form[1]).lower(), form, line))


def declarations(form, out: dict) -> None:
    name = ledger.head(form)
    if name is None:
        return
    if name in ("progn", "encapsulate", "local"):
        for item in form[1:]:
            declarations(item, out)
        return
    if name == DECLARER and len(form) >= 3 and isinstance(form[1], ledger.Sym):
        out[str(form[1]).lower()] = str(form[2]).lower()


SOURCES: set[str] = set()


def is_access(form) -> bool:
    name = ledger.head(form)
    return name is not None and (
        (name in ACCESSORS and len(form) == 2) or name.lower() in SOURCES)


def uses(form, var: str, parent=None, out=None) -> list:
    """Each (parent-call) whose argument is the symbol VAR, under FORM."""
    if out is None:
        out = []
    if isinstance(form, ledger.Sym):
        if str(form).lower() == var:
            out.append(parent)
        return out
    if not isinstance(form, list) or not form:
        return out
    if ledger.head(form) == "quote":
        return out
    for item in form[1:] if isinstance(form[0], ledger.Sym) else form:
        uses(item, var, form, out)
    return out


def sink_ok(parent, sinks: set[str]) -> bool:
    name = ledger.head(parent)
    return name is not None and name.lower() in sinks


def scan_body(form, sinks: set[str], bad: list, parent=None) -> None:
    """Record each accessor occurrence under FORM that is not accepted."""
    if not isinstance(form, list) or not form:
        return
    name = ledger.head(form)
    if name == "quote":
        return
    if name in ("let", "let*") and len(form) >= 3 and isinstance(form[1], list):
        body = form[2:]
        for binding in form[1]:
            if (isinstance(binding, list) and len(binding) == 2
                    and isinstance(binding[0], ledger.Sym) and is_access(binding[1])):
                var = str(binding[0]).lower()
                parents = []
                for item in body:
                    uses(item, var, None, parents)
                if not parents or all(p is not None and sink_ok(p, sinks)
                                      for p in parents):
                    scan_body(binding[1][1], sinks, bad, binding[1])
                    continue
                heads = sorted({str(ledger.head(p) or "?").lower() for p in parents
                                if p is not None and not sink_ok(p, sinks)})
                bad.append((binding[1], "let " + var + " -> " + ",".join(heads)))
                scan_body(binding[1][1], sinks, bad, binding[1])
            elif isinstance(binding, list):
                for item in binding[1:]:
                    scan_body(item, sinks, bad, form)
        for item in body:
            scan_body(item, sinks, bad, form)
        return
    if is_access(form):
        if parent is None or not sink_ok(parent, sinks):
            bad.append((form, str(ledger.head(parent) or "?").lower() if parent else "?"))
        scan_body(form[1], sinks, bad, form)
        return
    for item in form[1:] if isinstance(form[0], ledger.Sym) else form:
        scan_body(item, sinks, bad, form)


def paths() -> list[str]:
    books = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "books").glob("*.lisp"))
    hosts = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "host").glob("*.lisp"))
    return books + hosts


def scan() -> tuple[list[dict], dict]:
    declared: dict[str, str] = {}
    parsed: dict[str, list] = {}
    for relative in paths():
        parsed[relative] = forms_of(relative)
        for form, _line in parsed[relative]:
            declarations(form, declared)
    sinks = {name for name, kind in declared.items() if kind in (":handle", ":source")}
    SOURCES.clear()
    SOURCES.update(name for name, kind in declared.items() if kind == ":source")
    wire = {name for name, kind in declared.items() if kind == ":wire"}
    findings: list[dict] = []
    counts = {"definitions_reading_payload": 0, "accepted_sites": 0,
              "wire_definitions": 0, "handle_definitions": 0,
              "handle_sinks": len(sinks), "waived": 0}
    seen_waivers: set = set()
    for relative, forms in parsed.items():
        for form, line in forms:
            defs: list = []
            definitions(form, line, defs)
            for name, definition, where in defs:
                text = repr(definition).lower()
                if not any(word in text for word in ACCESSORS | SOURCES):
                    continue
                bad: list = []
                total: list = []
                for item in definition[3:]:
                    if name in SOURCES:
                        break
                    scan_body(item, sinks, bad)
                    scan_body(item, {"__all__"}, total)
                if not total:
                    continue
                counts["definitions_reading_payload"] += 1
                if name in wire:
                    counts["wire_definitions"] += 1
                    continue
                if name in sinks:
                    counts["handle_definitions"] += 1
                    continue
                counts["accepted_sites"] += len(total) - len(bad)
                if not bad:
                    continue
                key = (relative, name)
                if key in WAIVERS:
                    seen_waivers.add(key)
                    counts["waived"] += 1
                    continue
                findings.append({
                    "where": "{}:{}".format(relative, where), "function": name,
                    "sites": len(bad),
                    "problem": "reads a retained payload (a handle) into [{}] without "
                               "declaring its kind: read the octets through the arena "
                               "(fn-handle-bytes), declare the callee (fn-payload-kind F "
                               ":handle ...) if it takes a handle, or the function "
                               "(fn-payload-kind {} :wire ...) if its articles are the "
                               "octet model's".format(
                                   "; ".join(sorted({b[1] for b in bad})), name)})
    for key, owner in sorted(WAIVERS.items()):
        if key not in seen_waivers:
            findings.append({"where": key[0], "function": key[1], "sites": 0,
                             "problem": "stale waiver ({}): the finding is gone; "
                                        "drop it from WAIVERS".format(owner)})
    return findings, counts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", action="store_true")
    parser.add_argument("--json")
    args = parser.parse_args(argv)
    findings, counts = scan()
    for row in findings:
        print("payload-kind: {where} {function}: {problem}".format(**row))
    print("payload-kind: {} finding{}; {}".format(
        len(findings), "" if len(findings) == 1 else "s",
        ", ".join("{} {}".format(k.replace("_", " "), v) for k, v in counts.items())))
    for key, owner in sorted(WAIVERS.items()):
        print("payload-kind: waived {}:{} ({})".format(key[0], key[1], owner))
    if args.json:
        Path(args.json).write_text(json.dumps({"findings": findings, "counts": counts},
                                              indent=2) + "\n", encoding="utf-8")
    return 0 if args.report or not findings else 1


if __name__ == "__main__":
    sys.exit(main())
