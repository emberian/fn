#!/usr/bin/env python3
"""The per-function differential: candidates, vectors, and the report.

  fcheck.py gen IR POOL-VECTORS... --out CANDS --per N --seed S
      candidates for every stobj-free, state-free extracted defun: random
      small values shaped by the guard's conjuncts about each formal, drawn
      also from the quoted constants of the extracted code and from the
      results of earlier rounds' vectors (so a structured recognizer can be
      met by a value an extracted constructor built);
  fcheck.py scheme VECTORS... --ir IR --out DATA
      the vectors ACL2 wrote, as a Scheme data file for fcheck-main.scm;
  fcheck.py report IR CHICKEN-LOG --vectors V... [--json OUT]
      coverage: functions with a vector, agreeing, disagreeing.
ACL2 decides guard satisfaction and computes every expected value
(tools/extract/fcheck.lisp); this file only proposes inputs and counts.
"""
import argparse
import json
import random
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from chicken import scm_datum, conjuncts, NIL, T, SHIMS  # noqa: E402

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
    return (f["kind"] == "defun" and f["name"] not in SHIMS
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
    for f in ir["functions"]:
        if not eligible(f):
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
    parts = [out[i:i + a.split] for i in range(0, len(out), a.split)]
    for k, part in enumerate(parts):
        with open("%s.%03d" % (a.out, k), "w") as h:
            h.write("(\n" + "\n".join(part) + "\n)\n")
    print("files %d;" % len(parts), end=" ")
    print("candidates %d for %d eligible functions; pool %d" % (len(out), n_fns, len(uniq)))


def cmd_scheme(a):
    ir = json.load(open(a.ir))
    nout = {f["name"]: max(1, len(f["stobjs_out"])) for f in ir["functions"]}
    n = 0
    with open(a.out, "w") as h:
        for path in a.vectors:
            for line in open(path):
                v = json.loads(line)
                h.write("(%s (%s) %s %d)\n" % (scm_datum(["s", v["fn"]]),
                                              " ".join(scm_datum(x) for x in v["args"]),
                                              scm_datum(v["result"]), nout.get(v["fn"], 1)))
                n += 1
    print("vectors", n)


def cmd_report(a):
    ir = json.load(open(a.ir))
    total = len(ir["functions"])
    defuns = [f for f in ir["functions"] if f["kind"] == "defun" and f["name"] not in SHIMS]
    elig = [f["name"] for f in defuns if eligible(f)]
    res = {}
    for line in open(a.log):
        parts = line.rstrip("\n").split("\t")
        if parts[0] in ("AGREE", "DIFFER", "RAISE"):
            r = res.setdefault(parts[1], {"AGREE": 0, "DIFFER": 0, "RAISE": 0, "first": None})
            r[parts[0]] += 1
            if parts[0] != "AGREE" and not r["first"]:
                r["first"] = parts[2:] if len(parts) > 2 else None
    covered = [n for n in elig if res.get(n, {}).get("AGREE")]
    differ = {n: r for n, r in res.items() if r["DIFFER"] or r["RAISE"]}
    out = {
        "extracted_functions": total,
        "defuns": len(defuns),
        "eligible_stobj_and_state_free": len(elig),
        "covered_with_agreeing_vectors": len(covered),
        "vectors": sum(r["AGREE"] + r["DIFFER"] + r["RAISE"] for r in res.values()),
        "agree": sum(r["AGREE"] for r in res.values()),
        "functions_with_disagreement": differ,
        "uncovered": sorted(set(elig) - set(covered)),
        "not_eligible": sorted(f["name"] for f in defuns if not eligible(f)),
    }
    print("defuns %d; eligible %d; covered %d (%.1f%%); vectors %d, agree %d; disagreeing functions %d"
          % (len(defuns), len(elig), len(covered), 100.0 * len(covered) / max(1, len(elig)),
             out["vectors"], out["agree"], len(differ)))
    for n, r in list(differ.items())[:20]:
        print("  DIFFER", n, r)
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


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
    s = sp.add_parser("scheme")
    s.add_argument("vectors", nargs="+")
    s.add_argument("--ir", required=True)
    s.add_argument("--out", required=True)
    r = sp.add_parser("report")
    r.add_argument("ir")
    r.add_argument("log")
    r.add_argument("--json")
    a = p.parse_args()
    {"gen": cmd_gen, "scheme": cmd_scheme, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    main()
