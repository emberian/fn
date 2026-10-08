#!/usr/bin/env python3
"""Give each hazard rule its permanent form (follow-through of hazard_rule_classes.py).

tools/hazard_rule_classes.py --disable kept the census rules as :rewrite rules
for their own book and disabled them at the book's end.  This tool classifies
every theorem of the baseline (planning/hazard-rules-baseline.json) by who
names it, reading the Lisp with tools/lisp_rewrite.py -- never by substring:

  REGISTERED  named by planning/ (proofs, proof-events, teeth, interfaces),
              host/ or tests/acl2/: a keystone or a witness.  Never deleted,
              never made local; its :rewrite class goes (:rule-classes nil)
              when no book enables it.
  DEAD-LOCAL  no event outside the defining form (other than the book-end
              disable) names it, and a later event of its own book does
              (a :use or an :in-theory): made `local' is not possible when an
              exported event names it, so this is :rule-classes nil.
  DEAD-DELETE no event names it anywhere: it exists only as an implicit
              rewrite rule of its own book -> `local', so the book's own
              proofs keep it and the world does not.
  USE-ONLY    other books name it, all by :use / :by / :instance:
              :rule-classes nil.
  TARGETED    another book enables it (enable, :enable, e/d): needs a rule
              whose left-hand side names the function; refused here and
              printed in the residual with the consumers.

Applying a class edits only the defthm form's :rule-classes, or wraps the form
in `(local ...)'; the statement bytes never change.  A theorem whose form is
generated, listed twice, or already local is refused by name.

    tools/hazard_rule_followthrough.py            # print the plan and residual
    tools/hazard_rule_followthrough.py --apply    # edit books, drop names from
                                                  # the book-end disable list
    tools/hazard_rule_followthrough.py --table    # one line per theorem
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import hazard_rule_classes as hc  # noqa: E402
from lisp_rewrite import Atom, Lst, Pre, ReadError, parse, write  # noqa: E402

ROOT = hc.ROOT
BASELINE = "planning/hazard-rules-baseline.json"
USE_KEYS = {":use", ":by"}
ENABLE_KEYS = {":enable"}
DISABLE_KEYS = {":disable"}
REGISTRY = ("planning/proofs.json", "planning/proof-events.json",
            "planning/teeth-obligations.json", "planning/interfaces.json")


def rows_of(baseline):
    doc = json.loads(Path(baseline).read_text())
    names = []
    for key in doc["rows"]:
        n = key.rsplit("|", 1)[0]
        if n not in names:
            names.append(n)
    return names


def source_files(root):
    out = []
    for pat in ("books/**/*.lisp", "host/**/*.lisp", "tests/acl2/**/*.lisp"):
        out += sorted(p for p in root.glob(pat) if p.is_file())
    return out


def _children(node):
    if isinstance(node, Pre):
        return [node.node]
    if isinstance(node, Lst):
        return node.items
    return []


def _walk_ctx(node, chain, hit):
    """Yield (atom, chain) for each symbol atom; chain = ancestors (Lst, child index)."""
    if isinstance(node, Atom):
        yield node, chain
        return
    if isinstance(node, Pre):
        yield from _walk_ctx(node.node, chain, hit)
        return
    for i, c in enumerate(node.items):
        yield from _walk_ctx(c, chain + [(node, i)], hit)


def _kw_before(lst, idx):
    if idx >= 1 and isinstance(lst.items[idx - 1], Atom) and lst.items[idx - 1].text.startswith(":"):
        return lst.items[idx - 1].low
    return None


def context(chain):
    """Role of a reference: def | use | enable | disable | other."""
    for lst, idx in reversed(chain):
        h = hc._head(lst)
        if h in ("defthm", "defthmd") and idx == 1:
            return "def"
        kw = _kw_before(lst, idx)
        if kw in USE_KEYS:
            return "use"
        if kw == ":in-theory":
            return "theory"
        if kw in ENABLE_KEYS:
            return "enable"
        if kw in DISABLE_KEYS:
            return "disable"
        if h == "enable":
            return "enable"
        if h in ("disable", "disable*"):
            return "disable"
        if h == "deftheory" and idx >= 2:
            return "theory"
        if h == "e/d":
            return "enable" if idx == 1 else "disable"
        if h == ":use" and idx >= 1:
            return "use"
    return "other"


def scan(names, root=None):
    """refs[name] = list of (file, role, toplevel-form-head, local?)"""
    root = root or ROOT
    want = set(names)
    refs = {n: [] for n in names}
    unparsed = []
    for f in source_files(root):
        rel = str(f.relative_to(root))
        try:
            forms = parse(f.read_text(errors="surrogateescape")).forms
        except ReadError:
            unparsed.append(rel)
            continue
        for form in forms:
            top = hc._head(form) if isinstance(form, Lst) else None
            is_local = top == "local"
            for atom, chain in _walk_ctx(form, [], None):
                if atom.low in want and atom.kind == "symbol":
                    refs[atom.low].append((rel, context(chain), top, is_local))
    return refs, unparsed


def registered(names, root=None):
    root = root or ROOT
    out = {}
    for rel in REGISTRY:
        p = root / rel
        if not p.exists():
            continue
        t = p.read_text()
        for n in names:
            if re.search(r"(?<![\w-])" + re.escape(n) + r"(?![\w-])", t, re.I):
                out.setdefault(n, []).append(rel)
    return out


def locate_book(name, root=None):
    root = root or ROOT
    hits = []
    pat = re.compile(r"^[ \t]*\((?:local\s+\()?\s*(?:defthm|defthmd)\s+" + re.escape(name) + r"(?=[\s)])",
                     re.I | re.M)
    for f in sorted((root / "books").glob("**/*.lisp")):
        if pat.search(f.read_text(errors="surrogateescape")):
            hits.append(str(f.relative_to(root)))
    return hits


def trigger_of(form):
    """The function call that can trigger FORM as a forward-chaining rule, or why not.

    (implies (F v1 ... vn) CONC), F not a hazard head, the vi distinct variables
    and every variable of the formula among them -> the text of (F v1 ... vn).
    """
    f = form.items[2]
    if not (isinstance(f, Lst) and hc._head(f) == "implies" and len(f.items) == 3):
        raise hc.Refuse("not (implies H C)")
    hyp = f.items[1]
    if not (isinstance(hyp, Lst) and hyp.items and isinstance(hyp.items[0], Atom)):
        raise hc.Refuse("hypothesis is not one function call")
    head = hyp.items[0].low
    if head in PRIMS or head in ("and", "not", "equal"):
        raise hc.Refuse(f"hypothesis is a primitive call ({head})")
    args = hyp.items[1:]
    if not all(isinstance(x, Atom) and x.kind == "symbol" for x in args) or \
            len({x.low for x in args}) != len(args):
        raise hc.Refuse("hypothesis arguments are not distinct variables")
    have = {x.low for x in args}
    def vars_of(n, out):
        if isinstance(n, Atom):
            if n.kind == "symbol" and not n.text.startswith(":") and n.low not in ("t", "nil"):
                out.add(n.low)
        elif isinstance(n, Pre):
            vars_of(n.node, out)
        else:
            for x in n.items[1:]:
                vars_of(x, out)
        return out
    free = vars_of(f.items[2], set()) - have
    if free:
        raise hc.Refuse("conclusion has variables outside the trigger: " + ",".join(sorted(free)))
    return hyp


PRIMS = {"car", "cdr", "consp", "len", "nth", "member-equal", "assoc-equal", "<", "equal", "cons",
         "atom", "endp", "true-listp", "natp", "integerp"}


# A rule no event names can still be an implicit rewrite rule of its own book's
# proofs; deleting it reddens those proofs.  Each name here was found that way
# by a certify (persvati, certify-20261007T222048Z-2806646) and is made local.
IMPLICIT_OWN_USE = {
    "fn-clq-member-of-held-prefix",               # books/cold-line-quanta fn-clq-miss-stores-prefix
    "fn-rv-len-of-vector",                        # books/resource-vector fn-rv-outstanding-after-idling-a-charged-row
    "fn-store-codes-from-groups-member",          # books/store-config fn-store-codes-from-groups-inverts-*
    "fn-bs-keys-belowp-bounds-known-key",         # books/byte-store-invariants fn-bs-apply-writes-preserves-tables
    "fn-ctl-visible-filter-is-subset-of-arts",    # books/control-served fn-ctl-find-held-is-in-raw
    "fn-mpxt-subsetp-member",                     # books/msgid-pages-exec fn-mpxt-put-run-run-member
    "fn-scj-string-msgid-of-member",              # books/served-catalog-join-refresh fn-scj-drop-via-is-keep
    "fn-bs-k8-name-absent-from-list-has-no-entry",  # books/byte-store-record-fence k8-related-view-transaction-lookup-is-fenced
    "fn-retain-release-disjoint-member",          # books/retention-invariants fn-retain-release-preserves-statep
}
# Exported :rule-classes nil, plus a local rewrite twin so the book's own later
# proofs still see the rule (consumers :use the exported one).
LOCAL_TWIN = {
    "fn-member-of-subset",                        # books/node-invariants fn-node-install-stage-preserves-state
    "fn-not-member-of-subset",
}
# A downstream book relies on the exported rule without naming it: only a
# targeted left-hand side (by hand) can retire it.  Left as the stopgap.
IMPLICIT_CONSUMERS = {
    "fn-article-nonempty-true-list-is-consp": "a member of books/article's guard vocabulary theory; books/article-buffer's guards use it through that theory",
    "fn-bs-keys-belowp-excludes-bound": "books/article-buffer (guards of fn-ars-parse-lines) is red once it forward-chains",
    "fn-cpr-config-firstp-has-config": "books/store-checkpoint-open (fn-sco-cpr-prefix-of-later-configs) is red once it forward-chains",
    "fn-nntp-article-idp-is-consp": "books/nntp-search-scope needs it as a rewrite rule; a forward-chaining trigger does not reach it",
    "adt-nth-of-atom": "books/proto/adt-lib and adt-key-lib prove with it, unnamed",
}


def classify(name, book, refs, reg, form_ok=None):
    if name in IMPLICIT_CONSUMERS:
        return "REFUSED", IMPLICIT_CONSUMERS[name]
    own = [r for r in refs if r[0] == book]
    foreign = [r for r in refs if r[0] != book and r[1] != "disable"]
    books_foreign = [r for r in foreign if r[0].startswith("books/")]
    outside = [r for r in foreign if not r[0].startswith("books/")]
    enable_by = sorted({r[0] for r in foreign if r[1] in ("enable", "theory")})
    if enable_by:
        return "TARGETED", enable_by
    others = [r for r in books_foreign if r[1] == "other"]
    if others:
        return "REFUSED", "named in role other by " + ",".join(sorted({r[0] for r in others}))
    if reg or outside:
        return "REGISTERED", sorted(reg) + sorted({r[0] for r in outside})
    if books_foreign:
        return "USE-ONLY", sorted({r[0] for r in books_foreign})
    own_named = [r for r in own if r[1] in ("use", "enable")]
    if any(r[2] not in ("defthm", "defthmd", "local") and r[1] == "enable" for r in own_named):
        return "REFUSED", "an exported event of its own book enables it"
    if own_named:
        return "DEAD-LOCAL", "named inside its own book"
    if name in IMPLICIT_OWN_USE:
        return "DEAD-LOCAL", "an implicit rewrite rule of its own book's proofs"
    return "DEAD-DELETE", "named nowhere"


def analyse(root=None, baseline=None):
    root = root or ROOT
    names = rows_of(baseline or root / BASELINE)
    refs, unparsed = scan(names, root)
    reg = registered(names, root)
    result = {}
    for n in names:
        books = locate_book(n, root)
        if len(books) != 1:
            result[n] = (None, "REFUSED", f"defined in {len(books)} books")
            continue
        cls, why = classify(n, books[0], refs[n], reg.get(n, []))
        result[n] = (books[0], cls, why)
    return result, unparsed


# --------------------------------------------------------------------------
# applying a class


def _is_ws(t):
    return t.strip() == ""


def remove_atom_edit(text, parent, idx):
    """Span deleting item IDX of PARENT, keeping the layout of its neighbours."""
    item = parent.items[idx]
    nxt = parent.items[idx + 1] if idx + 1 < len(parent.items) else None
    if idx == 0:
        if nxt is not None and _is_ws(text[item.end:nxt.start]):
            return (item.start, nxt.start)
        return (item.start, item.end)
    prev = parent.items[idx - 1]
    before = text[prev.end:item.start]
    if not _is_ws(before):
        return (item.start, item.end)
    if "\n" not in before:
        return (prev.end, item.end)
    if nxt is not None and _is_ws(text[item.end:nxt.start]) and "\n" not in text[item.end:nxt.start]:
        return (item.start, nxt.start)
    return (prev.end + before.rfind("\n"), item.end)


def mention_edits(text, forms, names, keep=lambda name, role, top, is_local: False):
    """Spans deleting every enable/disable mention of NAMES in this file."""
    out = []
    for form in forms:
        if not isinstance(form, Lst):
            continue
        for atom, chain in _walk_ctx(form, [], None):
            if atom.kind != "symbol" or atom.low not in names:
                continue
            role = context(chain)
            if role not in ("enable", "disable", "theory"):
                continue
            if keep(atom.low, role, hc._head(form), hc._head(form) == "local" or any(
                    hc._head(l) == "local" for l, _ in chain)):
                continue
            # climb out of a rune wrapper (:rewrite NAME)
            k = len(chain) - 1
            lst, idx = chain[k]
            if hc._head(lst) in (":rewrite", ":definition", ":executable-counterpart") and k > 0:
                lst, idx = chain[k - 1][0], chain[k - 1][1]
                k -= 1
            args = lst.items[1:] if hc._head(lst) in ("enable", "disable") else None
            if args is not None and len(args) == 1 and k >= 1:
                # (in-theory (disable NAME)) alone: drop the form
                par, pidx = chain[k - 1]
                if hc._head(par) == "in-theory" and len(par.items) == 2:
                    if k == 1:
                        out.append(("form",) + delete_span(text, par.start, par.end) + (form,))
                        continue
                    gp, _ = chain[k - 2]
                    if k == 2 and hc._head(gp) == "local" and len(gp.items) == 2:
                        out.append(("form",) + delete_span(text, gp.start, gp.end) + (form,))
                        continue
            out.append(("atom",) + remove_atom_edit(text, lst, idx) + (form,))
    return out


def delete_span(text, start, end):
    """Whole-line deletion when the form owns its lines."""
    ls = text.rfind("\n", 0, start) + 1
    if _is_ws(text[ls:start]):
        start = ls
    le = text.find("\n", end)
    if le != -1 and _is_ws(text[end:le]):
        end = le + 1
        # swallow one blank line left doubled
        if text[end:end + 1] == "\n" and (start == 0 or text[start - 1:start] == "\n"):
            end += 1
    return start, end


def head_comment_start(text, start):
    """Start of the DISABLE_HEAD comment right above a disable block."""
    h = hc.DISABLE_HEAD
    i = text.rfind(h, 0, start)
    if i != -1 and _is_ws(text[i + len(h):start]):
        return i
    return start


def constraint_of(forms, target):
    """The signatured encapsulate holding TARGET, if any: its theorems are constraints."""
    def go(node, enc):
        if node is target:
            return enc
        kids = node.items if isinstance(node, Lst) else [node.node] if isinstance(node, Pre) else []
        here = enc
        if isinstance(node, Lst) and hc._head(node) == "encapsulate" and len(node.items) > 1 \
                and isinstance(node.items[1], Lst) and node.items[1].items:
            here = node
        for k in kids:
            r = go(k, here)
            if r is not False:
                return r
        return False
    for f in forms:
        r = go(f, None)
        if r is not False:
            return r
    return None


def form_edits(text, form, cls):
    name = form.items[1].low
    rc = hc._rule_classes(form)
    if cls in ("DEAD-DELETE", "DEAD-LOCAL") and isinstance(rc, Lst) and \
            any(not hc._is_rewrite(x) for x in rc.items):
        # other classes (:forward-chaining ...) stay: only the :rewrite class goes
        return [hc.edit_for(text, form)]
    if cls in ("REGISTERED", "USE-ONLY") and name in LOCAL_TWIN:
        stmt = text[form.items[2].start:form.items[2].end]
        twin = (f"\n\n(local (defthm {name}-local-rewrite\n  {stmt}\n"
                f"  :hints ((\"Goal\" :by {name}))))")
        return [hc.edit_for(text, form), (form.end, form.end, twin)]
    if cls == "DEAD-DELETE":
        s, e = delete_span(text, form.start, form.end)
        return [(s, e, "")]
    if cls == "DEAD-LOCAL":
        return [(form.start, form.start, "(local "), (form.end, form.end, ")")]
    if cls in ("REGISTERED", "USE-ONLY"):
        return [hc.edit_for(text, form)]
    if cls == "TARGETED":
        trig = trigger_of(form)
        t = text[trig.start:trig.end]
        rc = hc._rule_classes(form)
        new = f":rule-classes ((:forward-chaining :trigger-terms ({t})))"
        items = form.items
        if rc is None:
            return [(items[2].end, items[2].end, "\n " + new)]
        if isinstance(rc, Atom) and rc.low == ":rewrite":
            kw = [x for x in items if isinstance(x, Atom) and x.low == ":rule-classes"][0]
            v = items[items.index(kw) + 1]
            return [(kw.start, v.end, new)]
        raise hc.Refuse(f"rule-classes {text[form.start:form.end][:0]}not read for a targeted rule")
    raise hc.Refuse("class " + cls)


def apply_plan(root, result, only_class=None):
    """-> ({file: [(start,end,repl)]}, residual list).  Reads files, writes nothing."""
    names = {n for n, (b, c, w) in result.items() if c in CLASSES}
    resid = [(b, n, c, w) for n, (b, c, w) in sorted(result.items()) if c not in CLASSES]
    edits, texts, forms_of = {}, {}, {}

    def load(rel):
        if rel not in texts:
            texts[rel] = (root / rel).read_text(errors="surrogateescape")
            forms_of[rel] = parse(texts[rel]).forms
        return texts[rel], forms_of[rel]

    done = {}
    for n, (b, c, w) in sorted(result.items()):
        if c not in CLASSES:
            continue
        text, forms = load(b)
        try:
            form = hc.find_defthm(forms, n)
            if constraint_of(forms, form) is not None:
                raise hc.Refuse("constraint of a signatured encapsulate")
            es = form_edits(text, form, c)
        except hc.Refuse as r:
            resid.append((b, n, c, str(r)))
            names.discard(n)
            continue
        edits.setdefault(b, []).extend((s, e, r, "form") for s, e, r in es)
        done[n] = c
    # classes that remove the :rewrite rune from the world: strip mentions.
    # A mention of a deleted/local/nil rule is an error in ACL2; of a
    # forward-chaining replacement it is only redundant (drop the enables, keep disables off).
    strip = {n for n, c in done.items()}
    files = {b for n, (b, c, w) in result.items() if n in strip}
    for rel in {r for r, *_ in _all_mention_files(root, strip)} | files:
        try:
            text, forms = load(rel)
        except ReadError:
            continue
        def keep(name, role, top, is_local, rel=rel):
            cls = done[name]
            if top == "in-theory":
                return False            # an exported event: the rune it names is gone
            own = rel == result[name][0]
            if role == "theory" and cls != "TARGETED":
                return False            # a deftheory is exported: it cannot name a local rule
            if cls in ("DEAD-LOCAL", "TARGETED"):
                # the rule still exists in its own book (local / forward-chaining)
                return own or (role == "disable" and cls == "TARGETED")
            return False
        for kind, s, e, _form in mention_edits(text, forms, strip, keep):
            edits.setdefault(rel, []).append((s, e, "", kind))
    # an emptied disable block takes its comment with it
    for rel in files:
        text, forms = load(rel)
        for form in forms:
            if isinstance(form, Lst) and hc._head(form) == "in-theory":
                inner = form.items[1] if len(form.items) == 2 else None
                if isinstance(inner, Lst) and hc._head(inner) == "disable":
                    hs = head_comment_start(text, form.start)
                    if hs != form.start:
                        spans = [(s, e) for s, e, r, k in edits.get(rel, []) if s >= form.start and e <= form.end]
                        if any(k == "form" and s == form.start for s, e, r, k in edits.get(rel, [])) or \
                                _all_removed(inner, spans, text):
                            edits[rel] = [x for x in edits[rel] if not (x[0] >= form.start and x[1] <= form.end)]
                            s, e = delete_span(text, hs, form.end)
                            edits[rel].append((s, e, "", "block"))
    out = {}
    for rel, es in edits.items():
        keep, seen = [], []
        for s, e, r, k in sorted(es, key=lambda x: (x[0], -x[1])):
            if (s, e, r) in [x[:3] for x in keep]:
                continue
            if any(_inside(s, e, a, b2) for a, b2 in seen):
                continue
            if s < e:
                seen.append((s, e))
            keep.append((s, e, r))
        out[rel] = _coalesce(keep)
    return out, resid, texts


def _coalesce(edits):
    """Union overlapping pure deletions (two neighbours of one list)."""
    out = []
    for s, e, r in sorted(edits, key=lambda x: (x[0], x[1])):
        if out and r == "" and out[-1][2] == "" and s < out[-1][1]:
            out[-1] = (out[-1][0], max(e, out[-1][1]), "")
        else:
            out.append((s, e, r))
    return out


def _inside(s, e, a, b):
    """Does the edit [s, e) lie in the deleted span [a, b)?  A point edit on a boundary does not."""
    if s == e:
        return a < s < b
    return a <= s and e <= b


def _all_removed(inner, spans, text):
    for x in inner.items[1:]:
        if not any(s <= x.start and x.end <= e for s, e in spans):
            return False
    return True


def _all_mention_files(root, names):
    pat = re.compile("|".join(re.escape(n) for n in names), re.I) if names else None
    for f in source_files(root):
        if pat and pat.search(f.read_text(errors="surrogateescape")):
            yield (str(f.relative_to(root)),)


CLASSES = {"DEAD-DELETE", "DEAD-LOCAL", "REGISTERED", "USE-ONLY", "TARGETED"}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--table", action="store_true")
    ap.add_argument("--apply", action="store_true")
    a = ap.parse_args(argv)
    result, unparsed = analyse()
    if a.table:
        for n, (book, cls, why) in sorted(result.items(), key=lambda kv: (kv[1][1], kv[0])):
            print(f"{cls:11} {book}: {n}: {why}")
        return 0
    edits, resid, texts = apply_plan(ROOT, result)
    for rel, es in sorted(edits.items()):
        print(f"{rel}: {len(es)} edit(s)")
        if a.apply:
            (ROOT / rel).write_text(write(texts[rel], es), errors="surrogateescape")
    for b, n, c, why in resid:
        print(f"REFUSED {b}: {n}: {c}: {why}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
