#!/usr/bin/env python3
"""The per-function differential: candidates, vectors, and the report.

  fcheck.py gen IR POOL-VECTORS... --out CANDS --per N --seed S
      candidates for every stobj-free, state-free extracted defun: random
      small values shaped by the guard's conjuncts about each formal, drawn
      also from the quoted constants of the extracted code and from the
      results of earlier rounds' vectors (so a structured recognizer can be
      met by a value an extracted constructor built);
      also writes CANDS.manifest.json: each candidate file and its count;
  fcheck.py scheme --cands CANDS.manifest.json --ir IR --out DATA
      the vectors ACL2 wrote (CANDS.NNN.vec for every candidate file, each
      ending in fcheck.lisp's completion trailer), as a Scheme data file for
      fcheck-main.scm, every vector numbered (its case ID); writes
      DATA.manifest.json: the IDs, each ID's function, DATA's SHA-256;
  fcheck.py report IR CHICKEN-LOG --manifest DATA.manifest.json
                   --exit-status N [--json OUT]
      the acceptance: every ID of the manifest run exactly once and agreeing,
      both markers present, the program exited 0; coverage: functions with a
      vector, agreeing, disagreeing, uncovered.
Each subcommand fails closed: it prints `fcheck: FAIL REASON' and exits 1 on
anything it cannot account for (a missing or truncated file, a count that
does not add up, zero vectors), and a JSON it writes carries "status".
ACL2 decides guard satisfaction and computes every expected value
(tools/extract/fcheck.lisp); this file only proposes inputs and counts.
"""
import argparse
import hashlib
import json
import os
import random
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from chicken import scm_datum, conjuncts, NIL, T, SHIMS, INLINE  # noqa: E402

YNIL, YT = ["y", NIL], ["y", T]


def lisp_codes(s):
    return "(" + " ".join(str(ord(c)) for c in s) + ")"


def enc(d):
    """A JSON datum -> ACL2 text in fcheck.lisp's decode language."""
    if isinstance(d, int):
        return str(d)
    t = d[0]
    if t == "r":
        return "(:r %d %d)" % (d[1], d[2])
    if t == "ch":
        return "(:c %d)" % d[1]
    if t == "s":
        return "(:s %s)" % lisp_codes(d[1])
    if t == "y":
        if d[1] == NIL:
            return "nil"
        pkg, name = d[1].split("::", 1)
        return '(:y "%s" %s)' % (pkg, lisp_codes(name))
    if t == "L":
        return "(:l (%s) %s)" % (" ".join(enc(e) for e in d[1]), enc(d[2]))
    raise ValueError(d)


def lst(xs):
    return ["L", list(xs), YNIL] if xs else YNIL


def walk_quotes(t, out):
    if t[0] == "q":
        out.append(t[1])
    elif t[0] == "c":
        for a in t[2]:
            walk_quotes(a, out)
    elif t[0] == "l":
        walk_quotes(t[2], out)
        for a in t[3]:
            walk_quotes(a, out)


def size(d, limit=400):
    n, stack = 0, [d]
    while stack and n <= limit:
        x = stack.pop()
        n += 1
        if isinstance(x, list) and x[0] == "L":
            stack.extend(x[1])
            stack.append(x[2])
    return n


class Gen:
    def __init__(self, rng, pool):
        self.r = rng
        self.pool = pool

    def nat(self):
        r = self.r.random()
        if r < 0.6:
            return self.r.randint(0, 12)
        return self.r.randint(0, 300)

    def wide(self):
        # only where the guard names a width: a recursion on a nat of 2^34
        # measures the host's heap and stack, not the function
        return self.r.randint(0, 1 << 32) if self.r.random() < 0.2 else self.nat()

    def integer(self):
        n = self.nat()
        return -n if self.r.random() < 0.3 else n

    def octet(self):
        return self.r.randint(0, 255)

    def char(self):
        r = self.r.random()
        return ["ch", self.r.randint(32, 126) if r < 0.8 else self.r.randint(0, 255)]

    def string(self):
        n = self.r.randint(0, 8)
        return ["s", "".join(chr(self.char()[1]) for _ in range(n))]

    def octets(self):
        r = self.r.random()
        if r < 0.5:
            text = self.r.choice([b"GROUP fn.letters", b"STAT", b"QUIT", b"LIST ACTIVE fn.*",
                                  b"ARTICLE 1", b"<reader@example.invalid>", b"fn.letters",
                                  b"Message-ID: <a@b>", b"", b"\r\n", b"HEAD", b"Subject: x"])
            return lst(list(text))
        return lst([self.octet() for _ in range(self.r.randint(0, 10))])

    def any(self, depth=0):
        r = self.r.random()
        if r < 0.35 and self.pool:
            x = self.r.choice(self.pool)
            # a pool integer is a count somewhere; keep counts small
            return x if not isinstance(x, int) or abs(x) < (1 << 12) else self.nat()
        if r < 0.5:
            return self.nat()
        if r < 0.6:
            return self.r.choice([YNIL, YT])
        if r < 0.7:
            return self.string()
        if r < 0.8:
            return self.octets()
        if r < 0.85:
            return self.char()
        if depth < 2:
            return lst([self.any(depth + 1) for _ in range(self.r.randint(0, 3))])
        return YNIL

    def for_conjuncts(self, cs):
        """A generator from the recognizer names about one formal."""
        names = [c[1].split("::", 1)[1] for c in cs if c[0] == "c"]
        text = " ".join(names)
        if "UNSIGNED-BYTE-P" in names:
            return self.wide
        if any(n in ("NATP", "POSP") for n in names) or "INDEX" in text:
            return self.nat
        if "INTEGERP" in names or "SIGNED-BYTE-P" in names:
            return self.integer
        if any("OCTETP" in n or "BYTEP" in n for n in names):
            return self.octet
        if any("OCTET-LIST" in n or "OCTETS" in n or "BYTE-LIST" in n for n in names):
            return self.octets
        if "STRINGP" in names:
            return self.string
        if "CHARACTERP" in names:
            return self.char
        if "CHARACTER-LISTP" in names:
            return lambda: lst([self.char() for _ in range(self.r.randint(0, 6))])
        if "BOOLEANP" in names:
            return lambda: self.r.choice([YNIL, YT])
        return self.any


def mentions(t, v):
    if t[0] == "v":
        return t[1] == v
    if t[0] == "q":
        return False
    if t[0] == "c":
        return any(mentions(a, v) for a in t[2])
    return any(mentions(a, v) for a in t[3])


def eligible(f):
    return (f["kind"] == "defun"
            and f.get("class") in ("common-lisp-compliant", "ideal")
            and not any(f["stobjs_in"]) and not any(f["stobjs_out"]))


def cmd_gen(a):
    ir = json.load(open(a.ir))
    rng = random.Random(a.seed)
    pool = []
    for f in ir["functions"]:
        if f["kind"] == "defun":
            qs = []
            walk_quotes(f["body"], qs)
            pool.extend(q for q in qs if not isinstance(q, int) and size(q) < 60)
    by_fn = {}
    for path in a.vectors:
        for line in open(path):
            v = json.loads(line)
            if size(v["result"]) < 200:
                pool.append(v["result"])
                by_fn.setdefault(v["fn"], []).append(v["args"])
            for x in v["args"]:
                if size(x) < 200:
                    pool.append(x)
    # dedupe the pool
    seen, uniq = set(), []
    for p in pool:
        k = json.dumps(p)
        if k not in seen:
            seen.add(k)
            uniq.append(p)
    g = Gen(rng, uniq)
    out = []
    n_fns = 0
    only = set(json.load(open(a.only))["uncovered"]) if a.only else None
    for f in ir["functions"]:
        if not eligible(f) or (only is not None and f["name"] not in only):
            continue
        n_fns += 1
        cs = conjuncts(f["guard"])
        gens = [g.for_conjuncts([c for c in cs if mentions(c, v)]) for v in f["formals"]]
        for _ in range(a.per):
            args = [gen() for gen in gens]
            out.append("(%s (%s))" % (enc(["y", f["name"]]), " ".join(enc(x) for x in args)))
        # mutate arguments that already met the guard (earlier rounds)
        for prev in by_fn.get(f["name"], [])[:a.per]:
            args = list(prev)
            i = rng.randrange(len(args)) if args else 0
            if args:
                args[i] = gens[i]()
            out.append("(%s (%s))" % (enc(["y", f["name"]]), " ".join(enc(x) for x in args)))
    if not out:
        fail("gen: no candidates (%d eligible functions)" % n_fns)
    parts = [out[i:i + a.split] for i in range(0, len(out), a.split)]
    files = {}
    for k, part in enumerate(parts):
        path = "%s.%03d" % (a.out, k)
        with open(path, "w") as h:
            h.write("(\n" + "\n".join(part) + "\n)\n")
        files[os.path.basename(path)] = len(part)
    with open(a.out + ".manifest.json", "w") as h:
        json.dump({"status": "complete", "candidates": len(out), "eligible_functions": n_fns,
                   "files": files}, h, indent=1)
    print("files %d;" % len(parts), end=" ")
    print("candidates %d for %d eligible functions; pool %d" % (len(out), n_fns, len(uniq)))


def fail(reason):
    print("fcheck: FAIL " + reason)
    sys.exit(1)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


TRAILER_KEYS = ("done", "candidates", "ok", "guard_false", "error")


def read_vec(path, want):
    """The vectors of one file fcheck.lisp wrote, checked against its trailer
    and against WANT, the candidate count gen wrote for its input."""
    if not os.path.exists(path):
        fail("scheme: missing vector file %s" % path)
    vectors, trailer = [], None
    with open(path) as h:
        for k, line in enumerate(h, 1):
            if trailer is not None:
                fail("scheme: %s: line %d follows the completion trailer" % (path, k))
            if not line.endswith("\n"):
                fail("scheme: %s: line %d is truncated" % (path, k))
            try:
                v = json.loads(line)
            except ValueError:
                fail("scheme: %s: line %d is not JSON" % (path, k))
            if isinstance(v, dict) and "done" in v:
                trailer = v
            elif isinstance(v, dict) and set(v) == {"fn", "args", "result"} and isinstance(v["args"], list):
                vectors.append(v)
            else:
                fail("scheme: %s: line %d is neither a vector nor the trailer" % (path, k))
    if trailer is None:
        fail("scheme: %s: no completion trailer (ACL2 did not finish the file)" % path)
    if any(not isinstance(trailer.get(key), int) for key in TRAILER_KEYS):
        fail("scheme: %s: malformed trailer %r" % (path, trailer))
    if trailer["candidates"] != want:
        fail("scheme: %s: ACL2 read %d candidates, gen wrote %d" % (path, trailer["candidates"], want))
    if trailer["ok"] + trailer["guard_false"] + trailer["error"] != want:
        fail("scheme: %s: ok %d + guard-false %d + error %d is not %d candidates"
             % (path, trailer["ok"], trailer["guard_false"], trailer["error"], want))
    if trailer["ok"] != len(vectors):
        fail("scheme: %s: trailer says %d vectors, the file holds %d" % (path, trailer["ok"], len(vectors)))
    return vectors, trailer


def cmd_scheme(a):
    ir = json.load(open(a.ir))
    nout = {f["name"]: max(1, len(f["stobjs_out"])) for f in ir["functions"]}
    cands = json.load(open(a.cands))
    if cands.get("status") != "complete" or not cands.get("files"):
        fail("scheme: candidate manifest %s is not complete" % a.cands)
    if sum(cands["files"].values()) != cands.get("candidates"):
        fail("scheme: candidate manifest %s does not add up" % a.cands)
    here = os.path.dirname(os.path.abspath(a.cands))
    fns, per_file = [], {}
    totals = {"ok": 0, "guard_false": 0, "error": 0}
    with open(a.out, "w") as h:
        for name in sorted(cands["files"]):
            path = os.path.join(here, name)
            if not os.path.exists(path):
                fail("scheme: missing candidate file %s" % path)
            vectors, trailer = read_vec(path + ".vec", cands["files"][name])
            per_file[name + ".vec"] = {"vectors": len(vectors), "sha256": sha256_file(path + ".vec")}
            for key in totals:
                totals[key] += trailer[key]
            for v in vectors:
                h.write("(%d %s (%s) %s %d)\n" % (len(fns), scm_datum(["s", v["fn"]]),
                                                  " ".join(scm_datum(x) for x in v["args"]),
                                                  scm_datum(v["result"]), nout.get(v["fn"], 1)))
                fns.append(v["fn"])
    if not fns:
        fail("scheme: zero vectors (every candidate was refused by its guard or erred)")
    json.dump({"status": "complete", "vectors": len(fns), "fns": fns, "sha256": sha256_file(a.out),
               "data": os.path.basename(a.out), "files": per_file, "candidates": cands["candidates"],
               **totals}, open(a.out + ".manifest.json", "w"))
    print("vectors %d from %d candidates (guard-false %d, error %d)"
          % (len(fns), cands["candidates"], totals["guard_false"], totals["error"]))


VERDICTS = ("AGREE", "DIFFER", "RAISE", "HANG")


def judge(log_path, manifest, exit_status):
    """The acceptance of one fcheck run: (reasons, per-function results).
    REASONS is empty exactly when the run accounts for every case of the
    manifest once, in a complete output, with a zero exit and no divergence."""
    reasons = []
    n = manifest["vectors"]
    fns = manifest["fns"]
    if exit_status < 0:
        reasons.append("the fcheck program was killed by signal %d" % -exit_status)
    elif exit_status != 0:
        reasons.append("the fcheck program exited %d" % exit_status)
    if n <= 0 or len(fns) != n:
        reasons.append("the manifest holds no vectors")
    seen = {}
    res = {}
    begin = complete = None
    bad_lines = []
    with open(log_path, errors="replace") as h:
        lines = h.read().split("\n")
    truncated = lines and lines[-1] != ""
    if lines and lines[-1] == "":
        lines.pop()
    for k, line in enumerate(lines, 1):
        parts = line.split("\t")
        if line == "FCHECK-BEGIN":
            if begin is not None or seen:
                bad_lines.append((k, "FCHECK-BEGIN out of place"))
            begin = k
        elif parts[0] == "FCHECK-COMPLETE":
            if complete is not None:
                bad_lines.append((k, "a second FCHECK-COMPLETE"))
            complete = (k, parts[1] if len(parts) > 1 else "")
        elif parts[0] in VERDICTS and len(parts) >= 3:
            if complete is not None:
                bad_lines.append((k, "a verdict after FCHECK-COMPLETE"))
            try:
                cid = int(parts[1])
            except ValueError:
                bad_lines.append((k, "case id %r is not a number" % parts[1]))
                continue
            if not 0 <= cid < n:
                bad_lines.append((k, "case id %d is not in the manifest" % cid))
                continue
            if cid in seen:
                bad_lines.append((k, "duplicate case id %d (first at line %d)" % (cid, seen[cid])))
                continue
            seen[cid] = k
            if parts[2] != fns[cid]:
                bad_lines.append((k, "case %d is %s in the output, %s in the manifest" % (cid, parts[2], fns[cid])))
            r = res.setdefault(fns[cid], {"AGREE": 0, "DIFFER": 0, "RAISE": 0, "HANG": 0, "first": None})
            r[parts[0]] += 1
            if parts[0] != "AGREE" and not r["first"]:
                r["first"] = [str(cid)] + parts[3:]
        else:
            bad_lines.append((k, "unrecognized line %r" % line[:80]))
    if truncated:
        reasons.append("the output is truncated (its last line has no newline)")
    if begin is None:
        reasons.append("no FCHECK-BEGIN marker")
    if complete is None:
        reasons.append("no FCHECK-COMPLETE marker (the program did not finish)")
    elif complete[1] != str(n):
        reasons.append("FCHECK-COMPLETE counts %s vectors, the manifest %d" % (complete[1], n))
    elif complete[0] != len(lines):
        reasons.append("output follows FCHECK-COMPLETE")
    for k, why in bad_lines[:5]:
        reasons.append("line %d: %s" % (k, why))
    if len(bad_lines) > 5:
        reasons.append("%d more bad lines" % (len(bad_lines) - 5))
    missing = n - len(seen)
    if missing > 0:
        first = next(i for i in range(n) if i not in seen)
        reasons.append("%d of %d cases have no verdict (first: case %d, %s)" % (missing, n, first, fns[first]))
    divergent = {name: r for name, r in res.items() if r["DIFFER"] or r["RAISE"] or r["HANG"]}
    for name, r in list(divergent.items())[:3]:
        kind = next(v for v in VERDICTS[1:] if r[v])
        reasons.append("%s %s (case %s)" % (kind, name, r["first"][0]))
    if len(divergent) > 3:
        reasons.append("%d more divergent functions" % (len(divergent) - 3))
    return reasons, res, len(seen)


def cmd_report(a):
    ir = json.load(open(a.ir))
    total = len(ir["functions"])
    defuns = [f for f in ir["functions"] if f["kind"] == "defun"]
    elig = [f["name"] for f in defuns if eligible(f)]
    manifest = json.load(open(a.manifest))
    reasons = []
    if manifest.get("status") != "complete":
        reasons.append("the vector manifest is not complete")
    data = os.path.join(os.path.dirname(os.path.abspath(a.manifest)), manifest.get("data", ""))
    if not os.path.isfile(data) or sha256_file(data) != manifest.get("sha256"):
        reasons.append("the vector data %s is not the file the manifest names (SHA-256)" % data)
    more, res, executed = judge(a.log, manifest, a.exit_status)
    reasons += more
    covered = [n for n in elig if res.get(n, {}).get("AGREE")]
    differ = {n: r for n, r in res.items() if r["DIFFER"] or r["RAISE"] or r["HANG"]}
    uncovered = sorted(set(elig) - set(covered))
    status = "FAIL" if reasons else "PASS"
    out = {
        "status": status,
        "reasons": reasons,
        "fcheck_exit_status": a.exit_status,
        "manifest_vectors": manifest.get("vectors"),
        "executed_vectors": executed,
        "extracted_functions": total,
        "defuns": len(defuns),
        "eligible_stobj_and_state_free": len(elig),
        "covered_with_agreeing_vectors": len(covered),
        "uncovered_count": len(uncovered),
        "vectors": sum(r["AGREE"] + r["DIFFER"] + r["RAISE"] + r["HANG"] for r in res.values()),
        "agree": sum(r["AGREE"] for r in res.values()),
        "functions_with_disagreement": differ,
        "uncovered": uncovered,
        "not_eligible": sorted(f["name"] for f in defuns if not eligible(f)),
    }
    print("defuns %d; eligible %d; covered %d (%.1f%%); UNCOVERED %d (not checked; listed in the JSON); "
          "vectors %d of %d executed, agree %d; disagreeing functions %d"
          % (len(defuns), len(elig), len(covered), 100.0 * len(covered) / max(1, len(elig)),
             len(uncovered), executed, manifest.get("vectors", 0), out["agree"], len(differ)))
    for n, r in list(differ.items())[:20]:
        print("  DIFFER", n, r)
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)
    if reasons:
        fail("report: " + "; ".join(reasons))
    print("fcheck: PASS")


def main():
    p = argparse.ArgumentParser()
    sp = p.add_subparsers(dest="cmd", required=True)
    g = sp.add_parser("gen")
    g.add_argument("ir")
    g.add_argument("vectors", nargs="*")
    g.add_argument("--out", required=True)
    g.add_argument("--per", type=int, default=30)
    g.add_argument("--seed", type=int, default=1)
    g.add_argument("--split", type=int, default=1000)
    g.add_argument("--only", help="a report JSON: generate only for its uncovered functions")
    s = sp.add_parser("scheme")
    s.add_argument("--cands", required=True, help="the CANDS.manifest.json gen wrote")
    s.add_argument("--ir", required=True)
    s.add_argument("--out", required=True)
    r = sp.add_parser("report")
    r.add_argument("ir")
    r.add_argument("log")
    r.add_argument("--manifest", required=True, help="the DATA.manifest.json scheme wrote")
    r.add_argument("--exit-status", type=int, required=True, help="the fcheck program's exit status")
    r.add_argument("--json")
    a = p.parse_args()
    {"gen": cmd_gen, "scheme": cmd_scheme, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    main()
