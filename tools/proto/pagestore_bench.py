#!/usr/bin/env python3
"""The page-store prototype's bench and crash campaign (lane proto-pagestore,
2026-09-27; planning/evidence/proto-pagestore-2026-09-27.md).

Runs ON hbox (Linux).  From the laptop:

    python3 tools/proto/pagestore_bench.py ship          # rsync the tree to hbox
    ssh hbox python3 /tank/fn/scratch/proto-pagestore/tree/tools/proto/pagestore_bench.py build
    ssh hbox python3 .../pagestore_bench.py q1|q2|q4|cut-map|q3 [--out DIR]

`build` loads books/proto/pagestore.lisp from source in the w28 ACL2 (its
include closure's certificates come from the proof REPL tree), loads
host/native/proto-pagestore.lisp and saves one image
(/tank/fn/scratch/proto-pagestore/fnps-image.core) under swarm-build.  Every
command after that is one process of that image under
`systemd-run --user --scope -p MemoryMax=24G`, fed `:q` and one
`(fnps-main ...)` form; it prints `FNPS-JSON {...}` lines, which this tool
parses.  The process-death campaign (q3) kills the snapshot at every cut the
book names (*pgs-snapshot-cuts*; FNPS_CUT=name[:k], exit 77) and opens the
store in a fresh process: it must land on the last complete commit, with the
image digest of that commit.  Never touches /tank/fn/node.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import random
import shutil
import statistics
import subprocess
import sys
import time

ROOT = Path("/tank/fn/scratch/proto-pagestore")
TREE = ROOT / "tree"
CORE = ROOT / "fnps-image.core"
REPL_BOOKS = Path("/tank/fn/gates/proto-pagestore-repl/books")
SBCL = "/tank/fn/sbcl/bin/sbcl"
ACL2_CORE = "/tank/fn/acl2-8.7/saved_acl2.core"
DYN = "16000"
NVME = Path("/var/tmp/proto-pagestore")        # ext4 on /dev/nvme0n1p4
ZFS = ROOT / "data"                            # tank (ZFS)
LANE = Path(__file__).resolve().parents[2]


def sbcl_argv(core):
    return [SBCL, "--tls-limit", "16384", "--dynamic-space-size", DYN,
            "--control-stack-size", "64", "--disable-ldb", "--core", str(core),
            "--end-runtime-options", "--no-userinit", "--eval", "(acl2::sbcl-restart)"]


def ship(_a):
    subprocess.run(["rsync", "-a", "--delete", "--exclude", "build/", "--exclude", ".git",
                    "--include", "books/***", "--include", "host/***", "--include", "tools/***",
                    "--exclude", "*", f"{LANE}/", f"hbox:{TREE}/"], check=True)
    print("shipped", LANE, "->", TREE)


def build(_a):
    books = TREE / "books"
    for f in REPL_BOOKS.glob("sha256*"):
        if f.suffix in (".cert", ".fasl", ".port"):
            shutil.copy2(f, books / f.name)
    script = f"""(set-cbd "{TREE}/books/proto/")
(ld "pagestore.lisp")
:q
(load "{TREE}/host/native/proto-pagestore.lisp")
(save-exec "{ROOT}/fnps-image" "proto-pagestore")
"""
    log = ROOT / "build.log"
    with open(log, "w") as out:
        p = subprocess.run(["swarm-build"] + sbcl_argv(ACL2_CORE), input=script, text=True,
                           stdout=out, stderr=subprocess.STDOUT, cwd=TREE)
    text = log.read_text()
    bad = [l for l in text.splitlines() if "ACL2 Error" in l or "debugger invoked" in l]
    print("build rc", p.returncode, "core", CORE.exists(), "errors", bad[:5])
    return 0 if CORE.exists() and not bad else 1


def lisp_str(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def run(args, env=None, timeout=3600, strace=None):
    """One image process: returns (rc, [json records], raw output)."""
    form = "(fnps-main (list " + " ".join(lisp_str(a) for a in args) + "))"
    argv = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=24G"]
    if strace:
        argv += ["strace", "-f", "-c", "-o", strace, "-e", "trace=fsync,fdatasync"]
    argv += sbcl_argv(CORE)
    e = dict(os.environ)
    e.update(env or {})
    p = subprocess.run(argv, input=f":q\n{form}\n", text=True, capture_output=True,
                       timeout=timeout, env=e)
    recs = []
    for line in p.stdout.splitlines():
        i = line.find("FNPS-JSON ")
        if i >= 0:
            recs.append(json.loads(line[i + len("FNPS-JSON "):]))
    return p.returncode, recs, p.stdout + p.stderr


def ev(recs, name):
    return [r for r in recs if r.get("event") == name]


def drop_caches():
    subprocess.run(["sudo", "-n", "sh", "-c", "sync; echo 3 > /proc/sys/vm/drop_caches"], check=True)


def out_dir(a):
    d = Path(a.out)
    d.mkdir(parents=True, exist_ok=True)
    return d


def append(path, rec):
    with open(path, "a") as f:
        f.write(json.dumps(rec) + "\n")


# ---------------------------------------------------------------------------

def q1(a):
    d = out_dir(a)
    res = d / "q1.jsonl"
    for fsname, base in (("nvme-ext4", NVME), ("zfs", ZFS)):
        for n in [int(x) for x in a.sizes.split(",")]:
            store = str(base / f"q1-{n}")
            shutil.rmtree(store, ignore_errors=True)
            rc, recs, raw = run(["init", store, str(n)])
            init = ev(recs, "init")
            append(res, {"fs": fsname, "n": n, "phase": "init", "rc": rc, "init": init})
            if rc != 0 or not init:
                print(raw[-3000:]); return 1
            # A second commit of one appended page, so a lazy open checks
            # only the pages its own commit wrote (the realistic steady state).
            rc, recs, raw = run(["mutate", store, "main", "append", "1", "2"])
            append(res, {"fs": fsname, "n": n, "phase": "second-commit", "rc": rc,
                         "commit": ev(recs, "commit")})
            du = subprocess.run(["du", "-sb", store], capture_output=True, text=True).stdout.split()[0]
            append(res, {"fs": fsname, "n": n, "phase": "size", "bytes": int(du)})
            for mode in ("eager", "lazy"):
                for temp in ("cold", "warm"):
                    for i in range(a.runs):
                        if temp == "cold" and fsname != "zfs":
                            drop_caches()
                        rc, recs, raw = run(["open", store, "main", mode])
                        o = ev(recs, "open"); fr = ev(recs, "first-request")
                        append(res, {"fs": fsname, "n": n, "mode": mode, "temp": temp, "run": i,
                                     "rc": rc, "open": o[0] if o else None,
                                     "first": fr[0] if fr else None})
                        print(fsname, n, mode, temp, i, rc,
                              o and o[0].get("ms-total"), fr and fr[0]["requests"].get("ms-lookup-seq"),
                              flush=True)
            if not a.keep:
                shutil.rmtree(store, ignore_errors=True)
    return 0


def q2(a):
    d = out_dir(a)
    res = d / "q2.jsonl"
    base = NVME if a.fs == "nvme" else ZFS
    for kind in ("random", "append"):
        for fs_ in ((1,) if a.inline else (1, 2)):
            store = str(base / f"q2-{kind}-{fs_}")
            shutil.rmtree(store, ignore_errors=True)
            rc, recs, raw = run(["init", store, str(a.n)] + (["inline"] if a.inline else []))
            if rc != 0:
                print(raw[-3000:]); return 1
            for count in [int(x) for x in a.counts.split(",")]:
                for i in range(a.runs):
                    st = str(d / f"strace-{kind}-{fs_}-{count}-{i}.txt") if i == 0 else None
                    rc, recs, raw = run(["mutate", store, "main", kind, str(count), str(fs_)],
                                        strace=st)
                    c = ev(recs, "commit")
                    rec = {"fs": a.fs, "layout": "inline" if a.inline else "root-file", "kind": kind, "fsyncs": fs_, "count": count, "run": i,
                           "rc": rc, "commit": c[0]["commit"] if c else None}
                    if st and Path(st).exists():
                        rec["strace"] = Path(st).read_text()
                    append(res, rec)
                    print(kind, fs_, count, i, rc, c and c[0]["commit"].get("ms-total"), flush=True)
                    if rc != 0:
                        print(raw[-3000:]); return 1
            shutil.rmtree(store, ignore_errors=True)
    return 0


def q4(a):
    d = out_dir(a)
    res = d / "q4.jsonl"
    store = str(NVME / "q4")
    shutil.rmtree(store, ignore_errors=True)
    steps = []
    def step(name, args, env=None):
        rc, recs, raw = run(args, env=env)
        steps.append({"step": name, "rc": rc, "recs": recs})
        append(res, steps[-1])
        if rc != 0:
            print(raw[-3000:])
        return recs
    step("init", ["init", store, str(a.n)])
    d0 = step("digest-main-0", ["digest", store, "main"])
    for i in range(a.runs):
        step(f"branch-{i}", ["branch", store, "main", f"b{i}"])
    db0 = step("digest-b0-0", ["digest", store, "b0"])
    step("commit-main", ["mutate", store, "main", "random", "100", "2"])
    d1 = step("digest-main-1", ["digest", store, "main"])
    db1 = step("digest-b0-1", ["digest", store, "b0"])
    step("commit-b0", ["mutate", store, "b0", "append", "50", "2"])
    d2 = step("digest-main-2", ["digest", store, "main"])
    db2 = step("digest-b0-2", ["digest", store, "b0"])
    g = lambda r: [x for x in r if x.get("event") == "digest"][0]
    summary = {
        "branch_ms": [x["recs"][-1]["ms-branch"] for x in steps if x["step"].startswith("branch-")],
        "b0_equals_main_at_branch": g(db0)["digest"] == g(d0)["digest"],
        "b0_unchanged_by_main_commit": g(db1)["digest"] == g(db0)["digest"],
        "main_changed": g(d1)["digest"] != g(d0)["digest"],
        "main_unchanged_by_b0_commit": g(d2)["digest"] == g(d1)["digest"],
        "b0_changed": g(db2)["digest"] != g(db1)["digest"],
        "txids": [g(x)["txid"] for x in (d0, db0, d1, db1, d2, db2)],
    }
    append(res, {"summary": summary})
    print(json.dumps(summary))
    shutil.rmtree(store, ignore_errors=True)
    return 0


def host_cut_names():
    src = (TREE / "host/native/proto-pagestore.lisp").read_text()
    import re
    return sorted(set(re.findall(r"\(fnps-at (:[a-z-]+)\)", src)))


def cut_map(a):
    rc, recs, raw = run(["cut-names"])
    book = sorted(ev(recs, "cut-names")[0]["cuts"])
    host = [c[1:] for c in host_cut_names()]
    ok = sorted(book) == sorted(host)
    print(json.dumps({"book": book, "host": host, "equal": ok}))
    return 0 if ok else 1


def q3(a):
    d = out_dir(a)
    res = d / "q3-cuts.jsonl"
    rng = random.Random(a.seed)
    store = str(NVME / "q3")
    shutil.rmtree(store, ignore_errors=True)
    rc, recs, raw = run(["init", store, str(a.n)] + (["inline"] if a.inline else []))
    if rc != 0:
        print(raw[-3000:]); return 1
    rc, recs, raw = run(["digest", store, "main"])
    cur = ev(recs, "digest")[0]
    expected = {cur["txid"]: cur["digest"]}
    cuts = ["begin", "page-written", "table-written", "pages-synced", "record-torn",
            "record-written", "record-synced"]
    after_new = {"record-written", "record-synced"}
    viol = 0
    counts = {}
    refusals = {}
    for i in range(a.cuts):
        name = cuts[i % len(cuts)]
        kind = rng.choice(["random", "append"])
        count = rng.choice([1, 2, 5, 17, 40]) if kind == "random" else rng.choice([1, 3, 8])
        fs_ = 2 if name == "pages-synced" else (1 if a.inline else rng.choice([1, 2]))
        k = 1
        if name == "page-written":
            k = rng.randint(1, 3)
        env = {"FNPS_CUT": f"{name}:{k}", "FNPS_DIGEST": "1", "FNPS_SEED": str(rng.randrange(1 << 30))}
        rc, recs, raw = run(["mutate", store, "main", kind, str(count), str(fs_)], env=env)
        pre = ev(recs, "pre")
        if not pre:
            print(raw[-3000:]); return 1
        new_txid = cur["txid"] + 1
        expected[new_txid] = pre[0]["next-digest"]
        reached = rc == 77
        land_new = (not reached) or name in after_new
        mode = rng.choice(["eager", "lazy"])
        rc2, recs2, raw2 = run(["digest", store, "main", mode])
        o = ev(recs2, "open"); dg = ev(recs2, "digest")
        got = dg[0] if dg else None
        want_txid = new_txid if land_new else cur["txid"]
        ok = got is not None and got["txid"] == want_txid and got["digest"] == expected[want_txid]
        refs = (o[0]["refusals"] or []) if o else []
        if name == "record-torn" and reached:
            ok = ok and any(":commit-torn" in r for r in refs)
        for r in refs:
            parts = r.strip("()").split()
            key = parts[2] if len(parts) > 2 else r
            refusals[key] = refusals.get(key, 0) + 1
        label = f"{name}" + (f":{k}" if name == "page-written" else "")
        c = counts.setdefault(name, {"cuts": 0, "reached": 0, "violations": 0})
        c["cuts"] += 1; c["reached"] += int(reached); c["violations"] += int(not ok)
        viol += int(not ok)
        append(res, {"i": i, "cut": label, "kind": kind, "count": count, "fsyncs": fs_,
                     "rc": rc, "reached": reached, "open_mode": mode, "want_txid": want_txid,
                     "got": got, "refusals": refs, "ok": ok})
        if not ok:
            print("VIOLATION", i, label, raw2[-2000:], flush=True)
        if got:
            cur = got
            if cur["txid"] < new_txid:
                expected.pop(new_txid, None)
        print(i, label, "rc", rc, "landed", got and got["txid"], "ok", ok, flush=True)
    # Damage cases.
    dres = d / "q3-damage.jsonl"
    dmg = {"eager-fallback": 0, "lazy-open-fallback": 0, "lazy-touch-damaged": 0,
           "eager-shared-refused": 0, "violations": 0}
    for j in range(a.damage):
        # A fresh commit T over T-1, both known.
        rc, recs, raw = run(["mutate", store, "main", "random", "5", "2"],
                            env={"FNPS_DIGEST": "1", "FNPS_SEED": str(rng.randrange(1 << 30))})
        prev = cur
        rc, recs, raw = run(["digest", store, "main"])
        cur = ev(recs, "digest")[0]
        expected[cur["txid"]] = cur["digest"]
        # Which pages did T write?  The table says; damage picks by entry txid.
        rc, recs, raw = run(["damage", store, "main", "0"])       # probe page 0 (flip)
        run(["damage", store, "main", "0"])                       # restore
        which = "new" if j % 2 == 0 else "old"
        lp = None
        for cand in range(1, 400):
            rc, recs, raw = run(["damage", store, "main", str(cand)])
            dm = ev(recs, "damage")
            if not dm:
                break
            if (dm[0]["entry-txid"] == cur["txid"]) == (which == "new"):
                lp = cand
                break
            run(["damage", store, "main", str(cand)])             # not this one: restore
        if lp is None:
            continue
        rce, re_, rawe = run(["digest", store, "main", "eager"])
        rcl, rl, rawl = run(["open", store, "main", "lazy", str(lp)])
        oe = ev(re_, "open"); ge = ev(re_, "digest")
        ol = ev(rl, "open"); fl = ev(rl, "first-request")
        rec = {"j": j, "which": which, "lpage": lp, "T": cur["txid"],
               "eager_open": oe[0] if oe else None, "eager_digest": ge[0] if ge else None,
               "lazy_open": ol[0] if ol else None, "lazy_touch": fl[0] if fl else None}
        ok = True
        if which == "new":
            ok = bool(ge) and ge[0]["txid"] == prev["txid"] and ge[0]["digest"] == prev["digest"] \
                and any(":page-damaged" in r for r in (oe[0]["refusals"] or []))
            dmg["eager-fallback"] += int(ok)
            lok = bool(ol) and ol[0].get("txid") == prev["txid"] and \
                any(":page-damaged" in r for r in (ol[0]["refusals"] or []))
            dmg["lazy-open-fallback"] += int(lok)
            ok = ok and lok
        else:
            # A page T did not write is shared with T-1: eager refuses both by
            # name; lazy lands on T and the touch answers :damaged.
            eok = bool(oe) and oe[0].get("landed") is None and \
                sum(":page-damaged" in r for r in (oe[0]["refusals"] or [])) >= 1
            dmg["eager-shared-refused"] += int(eok)
            lok = bool(fl) and fl[0].get("touch-verdict") == ":damaged"
            dmg["lazy-touch-damaged"] += int(lok)
            ok = eok and lok
        rec["ok"] = ok
        for o_ in (oe, ol):
            for r in ((o_[0]["refusals"] or []) if o_ else []):
                parts = r.strip("()").split()
                key = "damage " + (parts[2] if len(parts) > 2 else r)
                refusals[key] = refusals.get(key, 0) + 1
        dmg["violations"] += int(not ok)
        append(dres, rec)
        print("damage", j, which, lp, ok, flush=True)
        run(["damage", store, "main", str(lp)])                   # restore
    summary = {"cuts": a.cuts, "violations": viol, "by_cut": counts, "refusals": refusals,
               "damage": dmg}
    append(d / "q3-summary.jsonl", summary)
    print(json.dumps(summary, indent=1))
    shutil.rmtree(store, ignore_errors=True)
    return 0 if viol == 0 and dmg["violations"] == 0 else 1


def summarize(a):
    """Tables (medians) from the jsonl files in --out; writes summary.md."""
    d = Path(a.out)
    lines = []
    med = lambda xs: round(statistics.median(xs), 1) if xs else None
    q1f = d / "q1.jsonl"
    if q1f.exists():
        rows = [json.loads(l) for l in q1f.read_text().splitlines()]
        sizes = {(r["fs"], r["n"]): r["bytes"] for r in rows if r.get("phase") == "size"}
        lines += ["## Q1 open (ms, median of runs)", "",
                  "| fs | records | MB on disk | mode | cache | commit | table | bulk read | verify | open total | seq lookup | msgid lookup | bg pass | RSS MiB |",
                  "|---|---:|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
        keys = sorted({(r["fs"], r["n"], r["mode"], r["temp"]) for r in rows if "mode" in r},
                      key=lambda k: (k[0], k[1], k[2], k[3]))
        for k in keys:
            rs = [r for r in rows if (r.get("fs"), r.get("n"), r.get("mode"), r.get("temp")) == k
                  and r.get("open")]
            g = lambda f: med([r["open"][f] for r in rs])
            fr = lambda f: med([r["first"]["requests"][f] for r in rs if r.get("first")])
            bg = med([r["first"]["ms-background-pass"] for r in rs if r.get("first")])
            rss = med([r["open"]["rss-kib"] / 1024 for r in rs])
            lines.append(f"| {k[0]} | {k[1]:,} | {sizes.get((k[0], k[1]), 0) / 1e6:.0f} | {k[2]} | {k[3]} | "
                         f"{g('ms-commit')} | {g('ms-table')} | {g('ms-bulk')} | {g('ms-verify')} | "
                         f"{g('ms-total')} | {fr('ms-lookup-seq')} | {fr('ms-lookup-msgid')} | {bg} | {rss} |")
        lines.append("")
    for fsn in ("nvme", "zfs"):
        q2f = d / "q2.jsonl"
        if not q2f.exists():
            break
        rows = [json.loads(l) for l in q2f.read_text().splitlines()]
        allrows = [r for r in rows if r.get("fs") == fsn and r.get("commit")]
        for layout in ("root-file", "inline"):
          rows = [r for r in allrows if r.get("layout", "root-file") == layout]
          if not rows:
            continue
          lines += [f"## Q2 snapshot on {fsn}, {layout} layout (ms, median)", "",
                  "| kind | dirty pages | barriers | plan+digest | page writes | table | sync 1 | record | sync 2 | total | fdatasync calls | write calls | MB written | table pages |",
                  "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
          for kind in ("append", "random"):
              for fs_ in (1, 2):
                  for cnt in sorted({r["count"] for r in rows}):
                      rs = [r["commit"] for r in rows if r["kind"] == kind and r["fsyncs"] == fs_
                            and r["count"] == cnt]
                      if not rs:
                          continue
                      g = lambda f: med([c[f] for c in rs])
                      st = [r.get("strace", "") for r in rows if r["kind"] == kind and r["fsyncs"] == fs_
                            and r["count"] == cnt and r.get("strace")]
                      calls = "-"
                      if st:
                          import re
                          got = {m.group(2): int(m.group(1))
                                 for m in re.finditer(r"^\s*[\d.]+\s+[\d.]+\s+\d+\s+(\d+)\s+(?:\d+\s+)?(f?d?a?t?a?sync)\s*$", st[0], re.M)}
                          calls = f"{rs[0]['syncs']} (strace: {got or 'none'})"
                      else:
                          calls = str(rs[0]['syncs'])
                      lines.append(f"| {kind} | {cnt:,} | {fs_} | {g('ms-plan')} | {g('ms-pages')} | "
                                   f"{g('ms-table')} | {g('ms-sync1')} | {g('ms-record')} | {g('ms-sync2')} | "
                                   f"{g('ms-total')} | {calls} | {rs[0]['runs']} | "
                                   f"{rs[0]['bytes'] / 1e6:.2f} | {rs[0]['table-pages']} |")
          lines.append("")
    out = d / "summary.md"
    out.write_text("\n".join(lines) + "\n")
    print(out.read_text())
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("ship").set_defaults(fn=ship)
    sub.add_parser("build").set_defaults(fn=build)
    for name, fn in (("q1", q1), ("q2", q2), ("q4", q4), ("cut-map", cut_map), ("q3", q3),
                     ("summarize", summarize)):
        p = sub.add_parser(name)
        p.set_defaults(fn=fn)
        p.add_argument("--out", default=str(ROOT / "results"))
        p.add_argument("--runs", type=int, default=3)
        p.add_argument("--n", type=int, default=40000)
        p.add_argument("--sizes", default="40000,1000000,10000000")
        p.add_argument("--counts", default="1,100,10000")
        p.add_argument("--fs", default="nvme")
        p.add_argument("--cuts", type=int, default=210)
        p.add_argument("--damage", type=int, default=12)
        p.add_argument("--seed", type=int, default=931)
        p.add_argument("--keep", action="store_true")
        p.add_argument("--inline", action="store_true",
                       help="root main's slots in page 0 of the page file (one-barrier commits)")
    a = ap.parse_args(argv)
    return a.fn(a) or 0


if __name__ == "__main__":
    sys.exit(main())
