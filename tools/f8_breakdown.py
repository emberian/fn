#!/usr/bin/env python3
"""The heap reservation itemised by term, from the model (F8; lane f8-reservation).

    python3 tools/f8_breakdown.py [--host persvati] [--profile small|synth-1m|FORM]
        [--core FILE:DYNAMIC | --core FILE --solve-figure MB] [--action run]
        [--observed OCTETS:RECORDS] [--connections 32] [--nursery 67108864]
        [--curve CURVE.json] [--floor FLOOR.json] [--image-dynamic OCTETS]
        [--at N] [--json OUT]

Every number in the MODEL column is ACL2's: books/heap-breakdown.lisp
`fn-heap-breakdown' evaluated in a proof_repl session over that book (the
session is started on BOX if it is not live and stopped afterwards unless
--keep).  KEYSTONE `fn-heap-breakdown-sums-to-the-reservation': the terms add
up to exactly the reservation the host is handed (for --action init, or run
unobserved at init's connections, `init''s number:
fn-heap-breakdown-is-inits-reservation), so the table cannot drift from the
figure.  No arithmetic on the model happens here beyond adding MiB columns.

CORE is the launcher's image observation (FILE . DYNAMIC): the core file's
octets and the dynamic space in use at the probe's start.  The probe does not
print DYNAMIC; --solve-figure MB finds the least DYNAMIC whose :run figure
over --observed is the heap MB the launcher printed (a bisection, each step
ACL2's figure).

MEASURED (optional): --curve is tools/fundamentals/f8_curve.py's JSON (live
heap after a full collection at 0 and N posts, the garbage before it, the
process's resident set and threads), --floor is tools/fundamentals/floor.py's
(the F8 row's run on the production image), --image-dynamic the production
image's own dynamic content (ROOM at start).  Terms are measured in groups,
since the process does not separate them: the state's four terms together
(live(N) - live(0)), the collector's (garbage before the collection), the
image outside the heap (resident less anonymous at start), the threads
(their count).  The curve's fit (live heap and resident set against N, least
squares over the points >= 1,000) extrapolates to --at N with the model
stated: linear in N at the curve's article shape.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MIB = 1048576
SESSION = "f8-breakdown"
PROFILES = {
    "small": "(fn-bs-profile-resolve *fn-heap-small-request* nil)",
    # init-reservation-2026-09-28's SYNTH_1M (fitness): T 2^20, H 2.8e9, R 196,608, A 32,768, G 16, K 65,536
    "synth-1m": "(fn-bs-profile-resolve (list :development (list (cons *fn-bs-pf-max-transactions* 1048576) "
                "(cons *fn-bs-pf-max-history-octets* 2800000000) (cons *fn-bs-pf-max-record-octets* 196608) "
                "(cons *fn-bs-pf-max-article-octets* 32768) (cons *fn-bs-pf-max-groups-per-article* 16) "
                "(cons *fn-bs-pf-max-open-suffix* 65536))) nil)",
    # f8_curve.py's store: T 131,072, H 512 MiB, the small preset's R, G and suffix
    "curve": "(fn-bs-profile-resolve (list :development (list (cons *fn-bs-pf-max-transactions* 131072) "
             "(cons *fn-bs-pf-max-history-octets* 536870912) (cons *fn-bs-pf-max-record-octets* 196608) "
             "(cons *fn-bs-pf-max-groups-per-article* 16) (cons *fn-bs-pf-max-open-suffix* 128))) nil)",
}
GROUPS = [("image-dynamic", ["IMAGE-DYNAMIC"]),
          ("state", ["STATE-HISTORY", "STATE-HANDLES", "STATE-RECORDS"]),
          ("open", ["OPEN-CHUNK-LISTS", "OPEN-SUFFIX-VECTORS", "OPEN-PER-RECORD"]),
          ("request", ["INFLIGHT-LISTS", "OCTET-BUFFERS", "ARTICLES"]),
          ("collector", ["COLLECTOR-ROOM", "MEGABYTE-ROUNDING"]),
          ("image-outside", ["IMAGE-OUTSIDE-HEAP"]),
          ("threads", ["THREAD-STACKS", "THREAD-RUNTIME"])]


def repl(args, *rest, check=True):
    cmd = [sys.executable, str(ROOT / "tools/proof_repl.py"), *rest]
    if args.host:
        cmd += ["--host", args.host]
    p = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if check and p.returncode != 0:
        raise SystemExit("f8_breakdown: proof_repl %s failed:\n%s" % (rest[0], p.stdout[-2000:]))
    return p.stdout


def lisp_obs(observed):
    if not observed:
        return "nil"
    o, _, n = observed.partition(":")
    return "'(%d . %d)" % (int(o), int(n)) if n else str(int(o))


def evaluate(args, core, form_tail):
    out = repl(args, "send", SESSION, "(let ((p %s) (core '(%d . %d))) %s)" % (
        args.profile_form, core[0], core[1], form_tail), "--full")
    return out


def breakdown(args, core):
    obs = lisp_obs(args.observed)
    out = evaluate(args, core, "(list :figure-mb (fn-heap-mb-of (fn-heap-operation-figure-octets :%s p core %d %s)) "
                   ":init-octets (fn-heap-init-reservation-octets p core %d) "
                   ":terms (fn-heap-breakdown :%s p core %d %s %d))"
                   % (args.action, args.nursery, obs, args.nursery, args.action, args.nursery, obs, args.connections))
    terms = [(k, int(v)) for k, v in re.findall(r"\(:([A-Z-]+)\s*\.\s*(\d+)\)", out)]
    fig = re.search(r":FIGURE-MB\s+(\d+)", out)
    init = re.search(r":INIT-OCTETS\s+(\d+)", out)
    if not terms or not fig:
        raise SystemExit("f8_breakdown: unexpected ACL2 answer:\n" + out[-2000:])
    return terms, int(fig.group(1)), int(init.group(1)) if init else None


def solve_dynamic(args, file_octets, target_mb):
    lo, hi = 0, file_octets
    obs = lisp_obs(args.observed)
    def fig(d):
        out = evaluate(args, (file_octets, d), "(list :fig (fn-heap-mb-of (fn-heap-operation-figure-octets :%s p core %d %s)))"
                       % (args.action, args.nursery, obs))
        return int(re.findall(r":FIG\s+(\d+)", out)[-1])
    if fig(hi) < target_mb:
        raise SystemExit("f8_breakdown: no DYNAMIC within the file reaches %d MB" % target_mb)
    while hi - lo > 65536:
        mid = (lo + hi) // 2
        if fig(mid) >= target_mb:
            hi = mid
        else:
            lo = mid
    return hi


def fit(points):
    n = len(points)
    sx = sum(x for x, _ in points); sy = sum(y for _, y in points)
    sxx = sum(x * x for x, _ in points); sxy = sum(x * y for x, y in points)
    b = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    return (sy - b * sx) / n, b


def measured(args):
    m = {}
    if args.image_dynamic:
        m["image-dynamic"] = args.image_dynamic
    if args.floor:
        f = json.loads(Path(args.floor).read_text())
        st = f.get("start") or {}
        if st.get("rss_kib") and st.get("anonymous_kib") is not None:
            m["image-outside"] = (st["rss_kib"] - st["anonymous_kib"]) * 1024
        m["floor"] = {k: f.get(k) for k in ("figure_line", "figure_line_after", "init", "after_1000", "reopen_post_floor")}
    if args.curve:
        c = json.loads(Path(args.curve).read_text())
        pts = {int(k): v for k, v in c["points"].items()}
        live0 = pts[0]["heap"]["dynamic-usage-after-gc"]
        rows = []
        for n in sorted(pts):
            h, pr = pts[n]["heap"], pts[n]["proc"]
            rows.append({"n": n, "live": h["dynamic-usage-after-gc"], "state": h["dynamic-usage-after-gc"] - live0,
                         "garbage": h["dynamic-usage"] - h["dynamic-usage-after-gc"],
                         "rss": pr.get("rss_kib", 0) * 1024, "anon": pr.get("anonymous_kib", 0) * 1024,
                         "hwm": pr.get("hwm_kib", 0) * 1024, "threads": pr.get("threads")})
        big = [r for r in rows if r["n"] >= 1000]
        a_live, b_live = fit([(r["n"], r["live"]) for r in big])
        a_rss, b_rss = fit([(r["n"], r["rss"]) for r in big])
        a_st, b_st = fit([(r["n"], r["state"]) for r in big])
        m["curve"] = {"rows": rows, "flags": c.get("flags"), "octets": c.get("octets"),
                      "fit_live": [a_live, b_live], "fit_rss": [a_rss, b_rss], "fit_state": [a_st, b_st],
                      "at": args.at, "live_at": a_live + b_live * args.at, "rss_at": a_rss + b_rss * args.at,
                      "state_at": a_st + b_st * args.at, "status": c.get("status"), "figure_after": c.get("figure_after"),
                      "reopen": c.get("reopen")}
        at = min(pts, key=lambda n: abs(n - 1000)) if 1000 not in pts else 1000
        m["state"] = pts[at]["heap"]["dynamic-usage-after-gc"] - live0
        m["collector"] = pts[at]["heap"]["dynamic-usage"] - pts[at]["heap"]["dynamic-usage-after-gc"]
        m["threads-count"] = pts[at]["proc"].get("threads")
    return m


def mib(x):
    return "%.1f" % (x / MIB)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--host", default="persvati")
    ap.add_argument("--profile", default="small")
    ap.add_argument("--core", required=True, help="FILE:DYNAMIC octets, or FILE with --solve-figure")
    ap.add_argument("--solve-figure", type=int, default=None, metavar="MB")
    ap.add_argument("--action", default="run")
    ap.add_argument("--observed", default=None, help="OCTETS:RECORDS the probe observed (default: unobserved)")
    ap.add_argument("--connections", type=int, default=32)
    ap.add_argument("--nursery", type=int, default=64 * MIB)
    ap.add_argument("--curve"); ap.add_argument("--floor")
    ap.add_argument("--image-dynamic", type=int, default=None)
    ap.add_argument("--at", type=int, default=1000000)
    ap.add_argument("--json", default=None)
    ap.add_argument("--keep", action="store_true", help="leave the session running")
    args = ap.parse_args()
    args.profile_form = PROFILES.get(args.profile, args.profile)
    status = repl(args, "status", SESSION, check=False)
    started = False
    if ", live," not in status:
        repl(args, "start", SESSION, "books/heap-breakdown", "--certify-missing")
        started = True
    try:
        f, _, d = args.core.partition(":")
        if args.solve_figure is not None:
            d = solve_dynamic(args, int(f), args.solve_figure)
        core = (int(f), int(d))
        terms, fig_mb, init_octets = breakdown(args, core)
    finally:
        if started and not args.keep:
            repl(args, "stop", SESSION, check=False)
    total = sum(v for _, v in terms)
    meas = measured(args)
    doc = {"profile": args.profile, "core": core, "action": args.action, "observed": args.observed,
           "connections": args.connections, "nursery": args.nursery, "figure_mb": fig_mb,
           "total_octets": total, "init_reservation_octets": init_octets, "terms": terms, "measured": meas}
    print("# %s, action %s, observed %s, core %d:%d, nursery %d" % (args.profile, args.action, args.observed or "none",
                                                                  core[0], core[1], args.nursery))
    print("# heap figure %d MB; reservation %s MiB (sum of the terms)%s" % (
        fig_mb, mib(total), "; init's reservation %s MiB" % mib(init_octets) if init_octets is not None else ""))
    print("%-22s %10s %6s" % ("term", "MiB", "share"))
    for k, v in terms:
        print("%-22s %10s %5.1f%%" % (k.lower(), mib(v), 100.0 * v / total))
    if meas:
        print("\n%-15s %10s %14s" % ("group", "model MiB", "measured MiB"))
        tv = dict(terms)
        for g, ks in GROUPS:
            mv = meas.get(g)
            extra = ""
            if g == "threads" and meas.get("threads-count") is not None:
                extra = "  (%s threads measured, %d reserved)" % (meas["threads-count"],
                                                                (tv["THREAD-STACKS"] // MIB))
            print("%-15s %10s %14s%s" % (g, mib(sum(tv.get(k, 0) for k in ks)), mib(mv) if isinstance(mv, int) else "-", extra))
        c = meas.get("curve")
        if c:
            print("\n# curve (%s, %s-octet articles): n, live MiB, state MiB, garbage MiB, VmRSS MiB, anonymous MiB, threads"
                  % (c["flags"], c["octets"]))
            for r in c["rows"]:
                print("%7d %9s %9s %9s %9s %9s %4s" % (r["n"], mib(r["live"]), mib(r["state"]), mib(r["garbage"]),
                                                     mib(r["rss"]), mib(r["anon"]), r["threads"]))
            print("# fit (least squares, n >= 1000; linear in n at this article shape):")
            print("#   live  = %s MiB + %.0f B x n  -> %s MiB at n = %d" % (mib(c["fit_live"][0]), c["fit_live"][1], mib(c["live_at"]), c["at"]))
            print("#   state = %s MiB + %.0f B x n  -> %s MiB at n = %d" % (mib(c["fit_state"][0]), c["fit_state"][1], mib(c["state_at"]), c["at"]))
            print("#   VmRSS = %s MiB + %.0f B x n  -> %s MiB at n = %d" % (mib(c["fit_rss"][0]), c["fit_rss"][1], mib(c["rss_at"]), c["at"]))
    if args.json:
        Path(args.json).write_text(json.dumps(doc, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
