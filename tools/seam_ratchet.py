#!/usr/bin/env python3.12
"""Shrink-only ratchet on the list/array seam in executable ACL2/Lisp code.

    python3.12 tools/seam_ratchet.py [--base REV] [--json] [--head-root DIR]

Census definition (see build/spans/c3/seam-census.md):
  files       books/**/*.lisp and host/**/*.lisp, minus test files (basename
              contains "-test", "-tests" or starts with "test-"; --include-tests
              keeps them).
  executable  a call form inside the body of a top-level (or progn /
              encapsulate / with-output nested) definition whose head is one of
              DEF_HEADS.  Not counted: defthm and every other event, (local ...)
              forms, comments, strings, quoted data, (declare ...), the :logic
              arm of mbe, define's keyword options and everything after ///,
              defun-nx / defund-nx (non-executable).
  generators  books/def-span-scan.lisp is not counted: its library loops over
              constrained functions (fn-dss-find, -fold, -equal, -copy,
              -stream, which every instance reaches by :functional-instance)
              and its instance templates are the span loop, the converted
              form this ratchet drives the seam toward; a per-octet
              fn-octets-get there is the loop's read, not a list seam.
              GENERATORS names the file; a new generator joins it only with
              that same reason.
  occurrence  one list form whose head symbol (package prefix stripped,
              case-folded) is coerce, fn-octets-list or fn-octets-get.
  function    one definition containing at least one such call.
  family      native if the path is under host/native/; else by the first
              dash-separated segment of the basename: bp/bpsec -> bp, web ->
              web, store/pagestore -> store, wire -> wire; else other.
"""
import argparse, json, re, subprocess, sys
from collections import Counter
from pathlib import Path

OPS = ("coerce", "fn-octets-list", "fn-octets-get")
RATCHETED = ("coerce", "fn-octets-list")
FAMILIES = ("bp", "web", "native", "store", "wire", "other")
DEF_HEADS = {"defun", "defund", "defun-inline", "defund-inline", "define",
             "defun-sk", "defund-sk", "defun$", "defabbrev"}
DEFAULT_BASE = "4b22a49bc"
FIRST_SEG = {"bp": "bp", "bpsec": "bp", "web": "web", "store": "store",
             "pagestore": "store", "wire": "wire"}


class Str(str):
    """A string literal (never a symbol)."""


class _Mark:
    def __init__(self, kind):
        self.kind = kind        # "'" quote, "`" backquote, "," unquote


def _add(cur, x):
    """Append a completed form, folding pending reader-prefix markers."""
    while cur and isinstance(cur[-1], _Mark):
        m = cur.pop()
        x = [{"'": "quote", "`": "backquote", ",": "unquote"}[m.kind], x]
    cur.append(x)


def read_forms(src):
    """Parse Lisp source into nested lists; atoms are str, strings are Str,
    a quoted form is ["quote", form], a backquoted one ["backquote", form]
    and a comma (or ,@) form inside it ["unquote", form]."""
    i, n = 0, len(src)
    stack, cur = [], []
    while i < n:
        c = src[i]
        if c in " \t\r\n\f":
            i += 1
        elif c == ";":
            while i < n and src[i] != "\n":
                i += 1
        elif c == "#" and src.startswith("#|", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("|#", i):
                    depth, i = depth - 1, i + 2
                elif src.startswith("#|", i):
                    depth, i = depth + 1, i + 2
                else:
                    i += 1
        elif c == "(":
            stack.append(cur)
            cur = []
            i += 1
        elif c == ")":
            if stack:
                done, cur = cur, stack.pop()
                _add(cur, done)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            _add(cur, Str(src[i + 1:j]))
            i = j + 1
        elif c in "'`,":
            j = i + 1
            if c == "," and j < n and src[j] in "@.":
                j += 1
            cur.append(_Mark(c))
            i = j
        elif c == "#" and src.startswith("#\\", i):
            j = i + 3
            while j < n and src[j] not in " \t\r\n\f()\";":
                j += 1
            _add(cur, "#char")
            i = j
        else:
            j = i
            buf = []
            while j < n and src[j] not in " \t\r\n\f()\";":
                if src[j] == "|":
                    k = src.find("|", j + 1)
                    k = n if k < 0 else k
                    buf.append(src[j + 1:k])
                    j = k + 1
                else:
                    buf.append(src[j])
                    j += 1
            if j == i:
                j = i + 1
            else:
                _add(cur, "".join(buf))
            i = j
    while stack:
        done, cur = cur, stack.pop()
        _add(cur, done)
    return [x for x in cur if not isinstance(x, _Mark)]


def sym(x):
    if isinstance(x, str) and not isinstance(x, Str):
        s = x.lower()
        if ":" in s and not s.startswith(":"):
            s = s.rsplit(":", 1)[1]
        return s
    return None


def head(form):
    return sym(form[0]) if isinstance(form, list) and form else None


def count_calls(node, out):
    """Count seam call forms in an expression, honoring quote / mbe / declare
    (a backquoted template counts as the code it is)."""
    if not isinstance(node, list) or not node:
        return
    h = head(node)
    if h == "quote":
        return
    if h in ("backquote", "unquote"):
        count_calls(node[1], out)
        return
    if h == "declare":
        return
    if h == "mbe":
        args = node[1:]
        for k in range(0, len(args) - 1, 2):
            if sym(args[k]) == ":exec":
                count_calls(args[k + 1], out)
        return
    if h in OPS:
        out[h] += 1
    for sub in node:
        count_calls(sub, out)


def define_body(form):
    """Executable parts of a (define name formals opts... body... [/// events])."""
    parts = []
    rest = form[3:]
    k = 0
    while k < len(rest):
        x = rest[k]
        if sym(x) == "///":
            break
        if isinstance(x, str) and not isinstance(x, Str) and x.startswith(":"):
            k += 2
            continue
        parts.append(x)
        k += 1
    return parts


def defun_body(form):
    return form[3:]


def walk_defs(forms, out):
    """Yield (name, line-less form) for every executable definition."""
    for f in forms:
        if not isinstance(f, list) or not f:
            continue
        h = head(f)
        if h in ("local", "quote"):
            continue
        if h in DEF_HEADS:
            out.append(f)
        elif h in ("defthm", "defthmd", "defmacro", "defconst", "defstub",
                   "defun-nx", "defund-nx", "in-theory", "include-book",
                   "defxdoc", "defsection-doc"):
            continue
        else:
            walk_defs(f[1:], out)


def census_text(src, path, include_tests=False):
    """Return list of dicts: one per function containing >=1 seam call."""
    funcs = []
    defs = []
    walk_defs(read_forms(src), defs)
    for d in defs:
        h = head(d)
        name = d[1] if len(d) > 1 and isinstance(d[1], str) else "?"
        parts = define_body(d) if h == "define" else defun_body(d)
        c = Counter()
        for p in parts:
            count_calls(p, c)
        if c:
            funcs.append({"file": path, "name": name, "family": family(path),
                          "line": def_line(src, name), "ops": dict(c)})
    return funcs


def def_line(src, name):
    """1-based line of the first (def-head NAME in src, or 0 (reporting only)."""
    m = re.search(r"\(\s*(?:%s)\s+\|?%s\|?[\s)]" % ("|".join(map(re.escape, DEF_HEADS)),
                                                   re.escape(name)), src, re.I)
    return src.count("\n", 0, m.start()) + 1 if m else 0


def family(path):
    p = path.replace("\\", "/")
    if p.startswith("host/native/"):
        return "native"
    base = p.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    return FIRST_SEG.get(base.split("-")[0].split(".")[0], "other")


def is_test(path):
    b = path.rsplit("/", 1)[-1]
    return "-test" in b or b.startswith("test-")


GENERATORS = ("books/def-span-scan.lisp",)


def wanted(path, include_tests):
    return (path.endswith(".lisp") and path.split("/")[0] in ("books", "host")
            and path not in GENERATORS
            and (include_tests or not is_test(path)))


def git(*a, cwd):
    return subprocess.run(["git", *a], cwd=cwd, check=True, capture_output=True,
                          timeout=300).stdout


def file_source(cwd, rev, path):
    if rev is None:
        return (Path(cwd) / path).read_text(errors="replace")
    return git("show", f"{rev}:{path}", cwd=cwd).decode(errors="replace")


def list_files(cwd, rev):
    if rev is None:
        rev = "HEAD"
    return git("ls-tree", "-r", "--name-only", rev, cwd=cwd).decode().splitlines()


def census(cwd, rev, include_tests=False):
    """Census of the committed tree at rev (None => HEAD); never the working
    tree, never a checkout.  Blobs are streamed through git cat-file --batch."""
    rev = rev or "HEAD"
    paths = sorted(p for p in list_files(cwd, rev) if wanted(p, include_tests))
    req = "".join(f"{rev}:{p}\n" for p in paths).encode()
    out = subprocess.run(["git", "cat-file", "--batch"], cwd=cwd, input=req,
                         check=True, capture_output=True, timeout=600).stdout
    funcs, pos = [], 0
    for p in paths:
        eol = out.index(b"\n", pos)
        size = int(out[pos:eol].split()[2])
        body = out[eol + 1:eol + 1 + size].decode(errors="replace")
        pos = eol + 1 + size + 1
        funcs += census_text(body, p)
    return summarize(funcs)


def summarize(funcs):
    ops = {o: {f: 0 for f in FAMILIES} for o in OPS}
    nf = {f: 0 for f in FAMILIES}
    for fn in funcs:
        nf[fn["family"]] += 1
        for o, k in fn["ops"].items():
            ops[o][fn["family"]] += k
    return {"functions": len(funcs), "functions_by_family": nf,
            "occurrences": {o: sum(v.values()) for o, v in ops.items()},
            "occurrences_by_family": ops, "detail": funcs}


def render(title, c):
    lines = [f"== {title} ==",
             f"functions with >=1 seam call: {c['functions']}",
             f"{'':16}" + "".join(f"{f:>8}" for f in FAMILIES) + f"{'total':>8}",
             f"{'functions':16}" + "".join(f"{c['functions_by_family'][f]:>8}" for f in FAMILIES)
             + f"{c['functions']:>8}"]
    for o in OPS:
        lines.append(f"{o:16}" + "".join(f"{c['occurrences_by_family'][o][f]:>8}" for f in FAMILIES)
                     + f"{c['occurrences'][o]:>8}")
    return "\n".join(lines)


def check(head_c, base_c):
    """Names of ratcheted operators whose HEAD count exceeds the base count."""
    return [o for o in RATCHETED if head_c["occurrences"][o] > base_c["occurrences"][o]]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", default=DEFAULT_BASE)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--include-tests", action="store_true")
    ap.add_argument("--list", metavar="FAMILY", choices=FAMILIES,
                    help="also list HEAD's seam functions of one family (file:line)")
    ap.add_argument("--repo", default=str(Path(__file__).resolve().parent.parent))
    a = ap.parse_args(argv)
    head_c = census(a.repo, None, a.include_tests)
    base_c = census(a.repo, a.base, a.include_tests)
    bad = check(head_c, base_c)
    if a.json:
        slim = lambda c: {k: v for k, v in c.items() if k != "detail"}
        print(json.dumps({"base_rev": a.base, "base": slim(base_c), "head": slim(head_c),
                          "head_functions": head_c["detail"], "grew": bad}, indent=1))
    else:
        print(render(f"BASE {a.base}", base_c))
        print(render("HEAD", head_c))
        for o in RATCHETED:
            print(f"{o}: base {base_c['occurrences'][o]} head {head_c['occurrences'][o]}")
        if a.list:
            for f in sorted(head_c["detail"], key=lambda f: (f["file"], f["line"])):
                if f["family"] == a.list:
                    ops = " ".join(f"{o}={k}" for o, k in sorted(f["ops"].items()))
                    print(f"{f['file']}:{f['line']} {f['name']} {ops}")
        print("RATCHET " + ("FAIL: grew " + ", ".join(bad) if bad else "OK (shrink-only held)"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
