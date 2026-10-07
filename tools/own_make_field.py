#!/usr/bin/env python3
"""own_make_field.py: add the owner's sixteenth field (`proc') to every
`(fn-own-make ...)' construction (lane owner-globals-28).

fn-own-make grew one positional argument, appended last (books/owner.lisp:
`... node-secret refused proc').  A construction that carries its owner's
fields forward must carry the new one the same way.  This tool reads each
Lisp file with tools/lisp_rewrite.py, finds every `(fn-own-make a1 .. a15)',
and inserts the sixteenth argument after the fifteenth, byte for byte (the
edit is one zero-width insertion; nothing else in the file moves).

The sixteenth argument, by the first rule that applies:
  1. a15 is `(fn-own-refused X)'            -> `(fn-own-proc X)'
     (a14, when it is `(fn-own-node-secret Y)', must name the same X, else the
     site is refused: mixed-source-owners);
  2. a15 is the symbol `refused'            -> the symbol `proc' (the universal
     form of a theorem; refused when the enclosing top-level form already
     mentions `proc': name-collision);
  3. a14 is `(fn-own-node-secret X)' and a15 is anything else (the step
     replaces the refused memory, e.g. fn-own-transit-refused, but keeps the
     rest of X) -> `(fn-own-proc X)';
  4. a14 and a15 are both the literal `nil' (a fresh literal owner, a test
     fixture or fn-own-start) -> `(fn-oproc-initial)';
  5. a14 and a15 are the numbered variables `cN-1' `cN' (a theorem over an
     arbitrary owner's fields) -> the next, `cN+1' (name-collision refused);
  6. otherwise the site is REFUSED with a named reason and listed.
A call with 16 arguments is already converted (the tool is idempotent).

A second pass carries the field through `:instance' hints.  A lemma stated
over `(fn-own-make .. refused proc)' gained the free variable `proc'; a hint
`(:instance LEMMA .. (refused (fn-own-refused X)))' that binds every other
field leaves `proc' free, so the instance no longer describes the owner the
hint meant (the certify of 2026-10-07 failed exactly there:
fn-ocmt-own-complete-preserves-ocl-relation,
fn-rix-own-complete-enabled-is-ccar).  The pass adds `(proc (fn-own-proc X))'
after the refused binding, or `(proc (fn-oproc-initial))' after `(refused
nil)' when the node-secret binding is `nil' too, but ONLY when LEMMA is
defined in the scanned tree (by defthm/defthmd) and its text names `proc' (an
extra binding ACL2 would refuse).  A lemma it cannot find is REFUSED
(instance-lemma-not-found), so a macro-generated lemma is listed, not guessed.  A
list headed `fn-own-make' with any other arity is not a construction (a name
list in a hint, a reference in a quoted form): it is skipped and listed
apart.  A file the reader refuses is listed with the reader's reason.

  tools/own_make_field.py [--write] [--json] [PATH ...]    (default books host tests)

Exit 0 when there are no refused sites and no unreadable files, else 1; the
residual list is on stdout either way.
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lisp_rewrite as lr  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
FIELD = "proc"
ACCESSOR = "fn-own-proc"
INITIAL = "(fn-oproc-initial)"


def _call_arg(node, head):
    """X of `(HEAD X)' (one-argument call), else None."""
    if isinstance(node, lr.Lst) and len(node.items) == 2:
        h = node.items[0]
        if isinstance(h, lr.Atom) and h.low == head:
            return node.items[1]
    return None


def decide(args, top_text):
    """(insertion text, rule) or (None, reason) for the fifteen ARGS."""
    a14, a15 = args[13], args[14]
    if "fn-own-make" in lr.flat(a14).lower() + lr.flat(a15).lower():
        return None, "source-owner-contains-a-construction"
    x15 = _call_arg(a15, "fn-own-refused")
    x14 = _call_arg(a14, "fn-own-node-secret")
    if x15 is not None:
        if x14 is not None and lr.flat(x14) != lr.flat(x15):
            return None, "mixed-source-owners"
        return f"({ACCESSOR} {lr.flat(x15)})", "refused-call"
    if isinstance(a15, lr.Atom) and a15.low == "refused":
        if FIELD in top_text.lower().replace("(", " ").replace(")", " ").split():
            return None, f"name-collision: `{FIELD}' already in the enclosing form"
        return FIELD, "refused-symbol"
    if x14 is not None:
        return f"({ACCESSOR} {lr.flat(x14)})", "node-secret-owner"
    if (isinstance(a14, lr.Atom) and a14.low == "nil"
            and isinstance(a15, lr.Atom) and a15.low == "nil"):
        return INITIAL, "fresh-nil"
    if isinstance(a14, lr.Atom) and isinstance(a15, lr.Atom):
        import re
        m14, m15 = re.fullmatch(r"c(\d+)", a14.low), re.fullmatch(r"c(\d+)", a15.low)
        if m14 and m15 and int(m15.group(1)) == int(m14.group(1)) + 1:
            nxt = f"c{int(m15.group(1)) + 1}"
            if nxt in top_text.lower().replace("(", " ").replace(")", " ").split():
                return None, f"name-collision: `{nxt}' already in the enclosing form"
            return nxt, "numbered-variables"
    return None, f"fifteenth-argument-not-a-carry: {lr.flat(a15)[:70]}"


def transform_text(text, path=None):
    """(new text, report) for one file's TEXT; report: sites, skipped."""
    p = lr.parse(text)
    edits, sites, skipped = [], [], []
    for top in p.forms:
        top_text = p.text[top.start:top.end]
        if "fn-own-make" not in top_text.lower():
            continue
        for m in lr.match("(fn-own-make ?*xs)", [top], head="fn-own-make"):
            args = m.node.items[1:]
            line = p.text.count("\n", 0, m.start) + 1
            site = {"file": path, "line": line}
            if len(args) == 16:
                continue
            if len(args) != 15:
                skipped.append({**site, "arity": len(args), "text": lr.flat(m.node)[:90]})
                continue
            ins, rule = decide(args, top_text)
            if ins is None:
                sites.append({**site, "refused": rule, "text": lr.flat(args[14])[:90]})
                continue
            at = args[14].end
            edits.append((at, at, " " + ins))
            sites.append({**site, "rule": rule})
    return lr.write(p.text, edits), {"sites": sites, "skipped": skipped}


def lemma_texts(files):
    """{lowercase defthm name: its form's text} over FILES."""
    import re
    out = {}
    head = re.compile(r"\(\s*(?:defthm|defthmd)\s+([^\s()]+)", re.IGNORECASE)
    for f in files:
        raw = f.read_bytes().decode("utf-8", "surrogateescape")
        if "defthm" not in raw.lower():
            continue
        try:
            p = lr.parse(raw)
        except lr.ReadError:
            continue
        for top in p.forms:
            for node in _forms_with_heads(top, ("defthm", "defthmd")):
                name = node.items[1]
                if isinstance(name, lr.Atom):
                    out[name.low] = p.text[node.start:node.end]
    return out


def _forms_with_heads(node, heads):
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, lr.Pre):
            stack.append(n.node)
        elif isinstance(n, lr.Lst):
            if (len(n.items) >= 2 and isinstance(n.items[0], lr.Atom)
                    and n.items[0].low in heads):
                yield n
            stack.extend(n.items)


def _binding(node):
    """(name, value) of a two-item list headed by a symbol, else None."""
    if (isinstance(node, lr.Lst) and len(node.items) == 2
            and isinstance(node.items[0], lr.Atom)):
        return node.items[0].low, node.items[1]
    return None


def transform_instances(text, lemmas, path=None):
    """(new text, sites) for the :instance pass over TEXT."""
    p = lr.parse(text)
    edits, sites = [], []
    for top in p.forms:
        for node in _forms_with_heads(top, (":instance",)):
            binds = [b for b in (_binding(i) for i in node.items[2:]) if b]
            names = {n for n, _ in binds}
            if "refused" not in names or FIELD in names:
                continue
            line = p.text.count("\n", 0, node.start) + 1
            site = {"file": path, "line": line, "pass": "instance"}
            refused_item = next(i for i in node.items[2:]
                                if _binding(i) and _binding(i)[0] == "refused")
            value = _binding(refused_item)[1]
            secret = dict(binds).get("node-secret")
            x = _call_arg(value, "fn-own-refused")
            if x is not None:
                ins = f"({FIELD} ({ACCESSOR} {lr.flat(x)}))"
            elif (isinstance(value, lr.Atom) and value.low == "nil"
                  and isinstance(secret, lr.Atom) and secret.low == "nil"):
                ins = f"({FIELD} {INITIAL})"
            else:
                sites.append({**site, "refused": "instance-refused-not-a-carry",
                              "text": lr.flat(refused_item)[:90]})
                continue
            lemma = node.items[1]
            body = lemmas.get(lemma.low) if isinstance(lemma, lr.Atom) else None
            if body is None:
                sites.append({**site, "refused": "instance-lemma-not-found",
                              "text": lr.flat(lemma)[:90]})
                continue
            if FIELD not in body.lower().replace("(", " ").replace(")", " ").split():
                continue
            at = refused_item.end
            edits.append((at, at, " " + ins))
            sites.append({**site, "rule": "instance-binding"})
    return lr.write(p.text, edits), sites


def lisp_files(paths):
    for r in paths:
        r = Path(r)
        if r.is_file():
            yield r
        else:
            # fixtures hold deliberately unconverted text
            yield from sorted(f for f in r.rglob("*.lisp") if "fixtures" not in f.parts)


def run(paths, write):
    report = {"converted": 0, "rules": {}, "refused": [], "skipped": [], "unreadable": [],
              "files": 0}
    files = list(lisp_files(paths))
    lemmas = None
    for f in files:
        raw = f.read_bytes().decode("utf-8", "surrogateescape")
        low = raw.lower()
        if "fn-own-make" not in low and ":instance" not in low:
            continue
        try:
            new, rep = transform_text(raw, str(f))
            if ":instance" in low and "(refused " in low:
                if lemmas is None:
                    lemmas = lemma_texts(files)
                new, more = transform_instances(new, lemmas, str(f))
                rep["sites"] += more
        except (lr.ReadError, lr.EditError) as e:
            report["unreadable"].append({"file": str(f), "reason": str(e)[:120]})
            continue
        for s in rep["sites"]:
            if "refused" in s:
                report["refused"].append(s)
            else:
                report["converted"] += 1
                report["rules"][s["rule"]] = report["rules"].get(s["rule"], 0) + 1
        report["skipped"] += rep["skipped"]
        if new != raw and write:
            f.write_bytes(new.encode("utf-8", "surrogateescape"))
            report["files"] += 1
        elif new != raw:
            report["files"] += 1
    return report


def main(argv):
    write = "--write" in argv
    as_json = "--json" in argv
    paths = [a for a in argv if not a.startswith("--")] or [
        str(ROOT / d) for d in ("books", "host", "tests")]
    rep = run(paths, write)
    if as_json:
        print(json.dumps(rep, indent=1))
    else:
        verb = "converted" if write else "would convert"
        print(f"{verb} {rep['converted']} site(s) in {rep['files']} file(s); rules {rep['rules']}")
        for s in rep["refused"]:
            print(f"REFUSED {s['file']}:{s['line']}: {s['refused']} | {s['text']}")
        for s in rep["unreadable"]:
            print(f"UNREADABLE {s['file']}: {s['reason']}")
        print(f"skipped {len(rep['skipped'])} non-construction fn-own-make list(s):")
        for s in rep["skipped"]:
            print(f"  {s['file']}:{s['line']} arity {s['arity']}: {s['text']}")
    return 1 if rep["refused"] or rep["unreadable"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
