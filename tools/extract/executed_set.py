#!/usr/bin/env python3
"""tools/extract/executed_set.py -- the executed set of a developer fn-core under
the product's workloads, and the census of what the core carries but never ran
(the measured collapse; CORE-CENSUS-20261010.md).

    executed_set.py run TREE IMAGE CORE OUT [--arm gate|served|load ...] [--jobs N]
    executed_set.py union OUT
    executed_set.py books IMAGE OUT
    executed_set.py census OUT CORE_DIR [--books BOOKS_TSV] [--tree TREE] [--json FILE]

`run` drives CORE (TREE/build/core/fn-core, a developer core) through a wrapper
launcher OUT/bin/fn-core that sets XL_HOOK=executed_set.lisp and FN_XC_OUT=OUT/raw,
so every fn-core process any arm starts records the functions it calls (the
instrument writes OUT/raw/<pid>.txt as it goes; see executed_set.lisp).  Arms:
  gate    the extraction gate's workloads, IMAGE (the developer image) as their
          reference: `--fn model' over TREE/build/extract/check/transcripts,
          `--fn rtc-exercise run 0..4', stateful.py, owner.py, faults_diff.py;
  served  the served node under tests/native_harness.py: SERVED_MODULES, each run
          twice, once with FN_NATIVE_HOST at the wrapper and once with the
          developer selectors' images at it too (a test that needs ACL2's own
          session fails in the second pass and is covered by the first): the
          serving loop, POST and the read commands, TLS (implicit and STARTTLS),
          peering (feeds, pulls, catch-up), the web reader;
  load    GAUNTLET's W1 cell (post-rate/small: closed-loop POSTs beside readers)
          through tools/load/driver.py --fn-core at the wrapper.
Every child's status is recorded in OUT/arms.json; a failing test still counts
for what it ran, and its status is reported, not hidden.

`union` folds OUT/raw into OUT/executed.txt (one name per line, sorted) and
OUT/unobserved.txt, and refuses (exit 1) an absent or empty set: no raw file,
no recorded name, or an instrumented process that wrapped nothing.

`books` writes OUT/books.tsv (`NAME<TAB>BOOK<TAB>fn|thm`): each function and theorem
in IMAGE's world (a developer image's `fn acl2 session') with the book whose
inclusion introduced it, read from the world's include-book-path at its FORMALS or
THEOREM property.

`census` joins the executed set with the static closure CORE_DIR/manifest.tsv
and edges.tsv (core.sh's outputs): every function unit never executed, and the
removable set R, the largest set of never-executed function units such that no
unit outside R references a unit in R (so every static caller of a removable
unit, inlined or local calls included, is itself removable).  Roots, variables,
globals, stobjs, declarations and unobserved names are never in R.  BOOKS_TSV
attributes units to books for the family table; with TREE, the last column counts
removable units whose book no claim names (claimed_books: a path in the claim
registers or specs, or the book of a critical keystone).
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

X = Path(__file__).resolve().parent

SERVED_MODULES = (
    # the serving loop, POST and the read commands
    "tests.test_native_served_differential", "tests.test_native_served_line_stack",
    "tests.test_native_article_quiet", "tests.test_native_article_slots",
    "tests.test_native_over_window", "tests.test_native_over_pins",
    "tests.test_native_post_seal_gate", "tests.test_native_mux",
    "tests.test_native_auth", "tests.test_native_sasl", "tests.test_native_group_access",
    "tests.test_native_operator_walk", "tests.test_native_host_lifecycle",
    "tests.test_native_outside_in",
    # TLS
    "tests.test_native_implicit_tls", "tests.test_native_starttls",
    "tests.test_native_tls_transport", "tests.test_native_tls_reload",
    "tests.test_native_tls_key_exchange", "tests.test_native_tls_handshake_budget",
    "tests.test_native_tls_proxy",
    # peering
    "tests.test_native_peering", "tests.test_native_peer_pull", "tests.test_native_peer_catchup",
    "tests.test_native_peer_by_name", "tests.test_native_peer_invite",
    "tests.test_native_protected_peering", "tests.test_native_peer_round_driver",
    "tests.test_native_feed_tls_read", "tests.test_native_feed_tls_ready",
    # the web reader
    "tests.test_native_web", "tests.test_native_web_progress", "tests.test_native_web_terminal",
)
# the image variables a served pass points at the wrapper (tests/native_harness.py IMAGE_DEFAULTS)
PASS_PRODUCT = ("FN_NATIVE_HOST",)
PASS_DEVELOPER = ("FN_NATIVE_HOST", "FN_NATIVE_DEVELOPER_HOST", "FN_NATIVE_CRASH_HOST",
                  "FN_NATIVE_DEVELOPER_STRIPPED_HOST")
LOAD_CELL = "W1/small"
STAR1 = "ACL2_*1*_ACL2::"
NOT_REMOVABLE_KINDS = ("var", "global", "stobj", "decl", "guard", "attach", "macro",
                       "registry", "struct")


class Refused(Exception):
    pass


# ---------------------------------------------------------------- run

def wrapper(core: Path, out: Path) -> Path:
    """OUT/bin/fn-core: CORE's launcher with the instrument in its environment;
    OUT/bin/fn-core.core names CORE's core (the load driver reads its digest)."""
    b = out / "bin"
    b.mkdir(parents=True, exist_ok=True)
    w = b / "fn-core"
    w.write_text("#!/bin/sh\nXL_HOOK=%s FN_XC_OUT=%s exec %s \"$@\"\n"
                 % (X / "executed_set.lisp", out / "raw", core.resolve()))
    w.chmod(0o755)
    real = Path(str(core.resolve()) + ".core")
    link = b / "fn-core.core"
    if real.is_file() and not link.exists():
        link.symlink_to(real)
    return w


def child(name, argv, log, *, cwd, env=None, timeout=3600):
    t0 = time.time()
    with open(log, "wb") as f:
        try:
            rc = subprocess.run([str(a) for a in argv], cwd=cwd, env=env, stdout=f,
                                stderr=subprocess.STDOUT, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            rc = "timeout"
    return {"name": name, "status": rc, "seconds": round(time.time() - t0, 1), "log": str(log)}


def arm_gate(tree, image, w, out, jobs):
    d = out / "gate"
    d.mkdir(exist_ok=True)
    rows = []
    for chunks in sorted((tree / "build/extract/check/transcripts").glob("*.chunks")):
        rows.append(child("model " + chunks.stem, [w, "--fn", "model", chunks, "-"],
                          d / ("model-%s.log" % chunks.stem), cwd=tree, timeout=600))
    for v in ("0", "1", "2", "3", "4"):
        rows.append(child("rtc-exercise " + v, [w, "--fn", "rtc-exercise", "run", v],
                          d / ("rtc-%s.log" % v), cwd=tree, timeout=600))
    for tool in ("stateful", "owner", "faults_diff"):
        rows.append(child(tool, ["python3", X / (tool + ".py"), image, w, d / tool],
                          d / (tool + ".log"), cwd=tree, timeout=5400))
    if not any(r["name"].startswith("model ") for r in rows):
        raise Refused("gate arm: no transcripts under build/extract/check (run check.sh first)")
    return rows


def arm_served(tree, image, w, out, jobs):
    d = out / "served"
    d.mkdir(exist_ok=True)
    work = []
    for label, names in (("product", PASS_PRODUCT), ("developer", PASS_DEVELOPER)):
        env = dict(os.environ, **{n: str(w) for n in names})
        for m in SERVED_MODULES:
            if not (tree / (m.replace(".", "/") + ".py")).is_file():
                raise Refused("served arm: no module %s in %s" % (m, tree))
            work.append(("%s %s" % (label, m), ["python3", "-m", "unittest", m],
                         d / ("%s-%s.log" % (label, m.split(".")[-1])), env))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = [ex.submit(child, n, a, l, cwd=tree, env=e, timeout=3600) for n, a, l, e in work]
        return [f.result() for f in futs]


def arm_load(tree, image, w, out, jobs):
    d = out / "load"
    return [child("load " + LOAD_CELL,
                  ["python3", "-m", "tools.load.driver", "run", "--cell", LOAD_CELL,
                   "--fn-core", w, "--label", "executed-set", "--out", d / "result"],
                  out / "load.log", cwd=tree, timeout=7200)]


ARMS = {"gate": arm_gate, "served": arm_served, "load": arm_load}


def run(args):
    tree, out = Path(args.tree).resolve(), Path(args.out).resolve()
    image, core = Path(args.image).resolve(), Path(args.core).resolve()
    for p in (image, core):
        if not os.access(p, os.X_OK):
            raise Refused("not executable: %s" % p)
    (out / "raw").mkdir(parents=True, exist_ok=True)
    w = wrapper(core, out)
    arms = json.loads((out / "arms.json").read_text()) if (out / "arms.json").is_file() else {}
    for a in args.arm or list(ARMS):
        print("executed-set: arm %s" % a, flush=True)
        arms[a] = ARMS[a](tree, image, w, out, args.jobs)
        (out / "arms.json").write_text(json.dumps(arms, indent=1) + "\n")
        bad = [r for r in arms[a] if r["status"] != 0]
        print("executed-set: arm %s: %d children, %d nonzero" % (a, len(arms[a]), len(bad)), flush=True)
    return union(out)


# ---------------------------------------------------------------- union

def union(out: Path) -> int:
    raw = Path(out) / "raw"
    txt = sorted(raw.glob("*.txt")) if raw.is_dir() else []
    if not txt:
        raise Refused("no executed set: %s holds no <pid>.txt" % raw)
    names, unobserved, wrapped, procs = set(), {}, [], 0
    for f in txt:
        procs += 1
        names.update(l.strip() for l in f.read_text().splitlines() if l.strip())
    for f in sorted(raw.glob("*.wrapped")):
        n = int(f.read_text().split()[0])
        if n == 0:
            raise Refused("process %s wrapped no function" % f.stem)
        wrapped.append(n)
    for f in sorted(raw.glob("*.unobserved")):
        lines = f.read_text().splitlines()
        for i, l in enumerate(lines):
            if l and not l.startswith(";;"):
                unobserved.setdefault(l.strip(), lines[i + 1][3:] if i + 1 < len(lines) else "")
    if not names:
        raise Refused("empty executed set: %d processes recorded no call" % procs)
    if not wrapped:
        raise Refused("no instrumented process reported its wrapped count")
    (out / "executed.txt").write_text("".join(n + "\n" for n in sorted(names)))
    (out / "unobserved.txt").write_text("".join("%s\t%s\n" % kv for kv in sorted(unobserved.items())))
    summary = {"processes": procs, "executed": len(names), "unobserved": len(unobserved),
               "wrapped_min": min(wrapped), "wrapped_max": max(wrapped)}
    (out / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print("executed-set: %(executed)d names executed over %(processes)d processes; "
          "%(unobserved)d unobserved; wrapped %(wrapped_min)d..%(wrapped_max)d" % summary)
    return 0


# ---------------------------------------------------------------- books

BOOKS_WALK = r"""
(let ((path nil) (seen (make-hash-table :test 'equal)) (n 0))
  (with-open-file (o (sb-ext:posix-getenv "FN_XC_BOOKS") :direction :output :if-exists :supersede)
    (dolist (trip (reverse (w *the-live-state*)))
      (cond ((and (eq (car trip) 'include-book-path) (eq (cadr trip) 'global-value))
             (setq path (cddr trip)))
            ((and (member (cadr trip) '(formals theorem)) (car path)
                  (not (gethash (cons (car trip) (cadr trip)) seen)))
             (setf (gethash (cons (car trip) (cadr trip)) seen) t)
             (incf n)
             (let ((b (car path)))
               (format o "~A~C~A~C~A~%"
                       (let ((*package* (find-package :keyword))) (prin1-to-string (car trip)))
                       #\Tab (if (consp b) (cdr b) b)
                       #\Tab (if (eq (cadr trip) 'formals) "fn" "thm")))))))
  (format t "~&BOOKS-DONE ~D~%" n))
"""


def books(args):
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    tsv, walk = out / "books.tsv", out / "books-walk.lisp"
    walk.write_text(BOOKS_WALK)
    env = dict(os.environ, FN_XC_BOOKS=str(tsv), ACL2_CUSTOMIZATION="NONE",
               SBCL_USER_ARGS="--control-stack-size 64MB")
    p = subprocess.run([args.image, "--fn", "acl2", "session"], input=(
        ':q\n(load "%s")\n(sb-ext:exit :code 0 :abort t)\n' % walk).encode(),
        env=env, capture_output=True, timeout=1800)
    done = re.search(rb"BOOKS-DONE (\d+)", p.stdout)
    if not done or int(done.group(1)) == 0 or not tsv.is_file():
        raise Refused("books: the world walk wrote nothing (status %s): %s"
                      % (p.returncode, p.stdout[-400:].decode(errors="replace")))
    print("executed-set: %s functions attributed to books in %s" % (done.group(1).decode(), tsv))
    return 0


# ---------------------------------------------------------------- census

def unit_of(name: str) -> str:
    """The manifest unit id of an instrument name (KEYWORD-printed symbol)."""
    if name.startswith(STAR1):
        return "star1:ACL2::" + name[len(STAR1):]
    return "raw:" + name


def read_manifest(path: Path):
    kinds = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        uid = line.split("\t", 1)[0]
        kinds[uid] = uid.split(":", 1)[0]
    return kinds


def read_edges(path: Path):
    roots, edges = set(), {}
    for line in path.read_text().splitlines():
        if line.startswith("#root\t"):
            roots.add(line.split("\t", 1)[1])
        elif line and not line.startswith("#"):
            uid, _, rest = line.partition("\t")
            edges[uid] = rest.split()
    return roots, edges


def removable(kinds, roots, edges, executed, unobserved):
    """The largest R among never-executed function units closed under callers."""
    never = {u for u, k in kinds.items() if k in ("raw", "star1")
             and u not in executed and u not in unobserved and u not in roots}
    callers = defaultdict(set)
    for src, tgts in edges.items():
        for t in tgts:
            callers[t].add(src)
    r = set(never)
    work = list(r)
    while work:
        u = work.pop()
        if u not in r:
            continue
        if any(c not in r and c != u for c in callers.get(u, ())):
            r.discard(u)
            for t in edges.get(u, ()):
                if t in r:
                    work.append(t)
    return never, r


def family(uid, books):
    name = uid.split("::", 1)[-1]
    book = books.get(name)
    if book:
        key = book_key(book)
        return ("host/" if key.startswith("host/") else "") + Path(key).name.split("-")[0]
    if name.startswith("FNN-"):
        return "host/native"
    return "unattributed"


CLAIM_REGISTERS = ("planning/proofs.json", "planning/critical-evidence.json",
                   "planning/critical-owed.json", "planning/requirements.json")


def book_key(book: str) -> str:
    """books/x/y.lisp, /abs/tree/books/x/y or (:FN . "books/x/y") -> books/x/y"""
    m = re.search(r'"([^"]+)"', book)
    path = (m.group(1) if m else book).strip()
    parts = path.split("/")
    at = max((i for i, p in enumerate(parts) if p in ("books", "host")), default=None)
    if at is None:
        return path
    key = "/".join(parts[at:])
    return key[:-5] if key.endswith(".lisp") else key


def claimed_books(tree: Path, thm_book) -> set:
    """Books a claim names: by path in the claim registers and specs/*.md, or as the
    book holding a critical keystone (planning/critical-base.json, critical-owed.json)."""
    named = set()
    texts = [tree / p for p in CLAIM_REGISTERS] + sorted((tree / "specs").glob("*.md"))
    for t in texts:
        if t.is_file():
            named.update(m for m in re.findall(r"((?:books|host)/[\w./-]+?)\.lisp", t.read_text()))
    for reg in ("planning/critical-base.json", "planning/critical-owed.json"):
        f = tree / reg
        if not f.is_file():
            continue
        entries = json.loads(f.read_text()).get("entries", {})
        for name in (entries if isinstance(entries, dict) else [e.get("name") for e in entries]):
            b = thm_book.get("ACL2::" + str(name).upper())
            if b:
                named.add(book_key(b))
    return named


def census(args):
    out, cd = Path(args.out), Path(args.core_dir)
    exe = out / "executed.txt"
    if not exe.is_file() or not exe.read_text().strip():
        raise Refused("census needs a non-empty %s (run `union')" % exe)
    executed = {unit_of(n) for n in exe.read_text().split()}
    unobserved = {unit_of(l.split("\t")[0]) for l in (out / "unobserved.txt").read_text().splitlines() if l}
    kinds = read_manifest(cd / "manifest.tsv")
    roots, edges = read_edges(cd / "edges.tsv")
    books, thm_book = {}, {}
    if args.books:
        for l in Path(args.books).read_text().splitlines():
            parts = l.split("\t")
            if len(parts) >= 2:
                kind = parts[2] if len(parts) > 2 else "fn"
                (books if kind == "fn" else thm_book).setdefault(parts[0], parts[1])
    claimed = claimed_books(Path(args.tree), thm_book) if args.tree else None
    never, r = removable(kinds, roots, edges, executed, unobserved)
    fns = {u for u, k in kinds.items() if k in ("raw", "star1")}
    fam = defaultdict(Counter)
    for u in fns:
        f = family(u, books)
        fam[f]["static"] += 1
        fam[f]["executed"] += u in executed
        fam[f]["never"] += u in never
        fam[f]["removable"] += u in r
    per_book = defaultdict(Counter)
    for u in fns:
        b = books.get(u.split("::", 1)[-1], "")
        per_book[b]["core"] += 1
        per_book[b]["removable"] += u in r
    if claimed is not None:
        for u in r:
            b = books.get(u.split("::", 1)[-1], "")
            if b and book_key(b) not in claimed:
                fam[family(u, books)]["removable_unclaimed"] += 1
    doc = {"functions": len(fns), "executed": len(fns & executed), "never": len(never),
           "removable": sorted(r), "never_roots": sorted(roots & (fns - executed - unobserved)),
           "families": {f: dict(c) for f, c in fam.items()},
           "books": {b: dict(c, claimed=(None if claimed is None else book_key(b) in claimed))
                     for b, c in per_book.items() if b}}
    if args.json:
        Path(args.json).write_text(json.dumps(doc, indent=1) + "\n")
    print("| family | static fns | executed | never | removable | removable, book unclaimed |")
    print("|---|---|---|---|---|---|")
    for f, c in sorted(fam.items(), key=lambda kv: -kv[1]["never"]):
        print("| %s | %d | %d | %d | %d | %s |" % (f, c["static"], c["executed"], c["never"], c["removable"],
                                                 c["removable_unclaimed"] if claimed is not None else "-"))
    print("| **all** | %d | %d | %d | %d | %s |" % (
        len(fns), doc["executed"], len(never), len(r),
        sum(c["removable_unclaimed"] for c in fam.values()) if claimed is not None else "-"))
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("tree"); r.add_argument("image"); r.add_argument("core"); r.add_argument("out")
    r.add_argument("--arm", action="append", choices=sorted(ARMS))
    r.add_argument("--jobs", type=int, default=4)
    u = sub.add_parser("union")
    u.add_argument("out")
    k = sub.add_parser("books")
    k.add_argument("image"); k.add_argument("out")
    c = sub.add_parser("census")
    c.add_argument("out"); c.add_argument("core_dir")
    c.add_argument("--books"); c.add_argument("--json")
    c.add_argument("--tree", help="the tree whose claim registers name books (the unclaimed column)")
    a = p.parse_args(argv)
    try:
        if a.cmd == "run":
            return run(a)
        if a.cmd == "union":
            return union(Path(a.out))
        if a.cmd == "books":
            return books(a)
        return census(a)
    except Refused as e:
        print("executed-set: REFUSED: %s" % e, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
