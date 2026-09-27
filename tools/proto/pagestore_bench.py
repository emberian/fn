#!/usr/bin/env python3
"""The page store's bench and crash campaign (lane proto-pagestore,
2026-09-27; the two-level table host of lane arena-store, 2026-09-27:
planning/evidence/arena-store-2026-09-27/).

Runs ON hbox (Linux).  From the laptop:

    python3 tools/proto/pagestore_bench.py ship          # rsync the tree to hbox
    ssh hbox python3 /tank/fn/scratch/arena-store-host/tree/tools/proto/pagestore_bench.py build
    ssh hbox python3 .../pagestore_bench.py q1|q2|q3|q4|cut-map|summarize [--out DIR]

`build` certifies books/pagestore-words, pagestore and pagestore-exec
in the w28 ACL2 (their include closure's sha256 certificates come from the
proof REPL tree), includes pagestore-exec, loads
host/native/proto-pagestore.lisp and saves one image
(/tank/fn/scratch/arena-store-host/fnps-image.core) under swarm-build.
Every command after that is one process of that image under
`systemd-run --user --scope -p MemoryMax=24G`, fed `:q` and one
`(fnps-main ...)` form; it prints `FNPS-JSON {...}` lines, which this tool
parses.  The store layout is the inline one-barrier layout.  The
process-death campaign (q3) kills the snapshot at every cut the book names
(*pgs-snapshot-cuts*; FNPS_CUT=name[:k], exit 77) and opens the store in a
fresh process: it must land on the last complete commit, with the image
digest of that commit; then damage cases (a data page, a table page, the
directory; written by the newest commit or shared with the previous one).
Never touches /tank/fn/node.
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

ROOT = Path("/tank/fn/scratch/arena-store-host")
TREE = ROOT / "tree"
CORE = ROOT / "fnps-image.core"
REPL_BOOKS = Path("/tank/fn/gates/proto-pagestore-repl/books")
SBCL = "/tank/fn/sbcl/bin/sbcl"
ACL2_CORE = "/tank/fn/acl2-8.7/saved_acl2.core"
DYN = "16000"
NVME = Path("/var/tmp/arena-store-host")        # ext4 on /dev/nvme0n1p4
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


BOOKS = ("pagestore-words", "pagestore", "pagestore-exec")


def build(_a):
    books = TREE / "books"
    for f in REPL_BOOKS.glob("sha256*"):
        if f.suffix in (".cert", ".fasl", ".port"):
            shutil.copy2(f, books / f.name)
    log = ROOT / "build.log"
    out = open(log, "w")
    for b in BOOKS:
        for ext in (".cert", ".fasl", ".port"):
            (books / "proto" / (b + ext)).unlink(missing_ok=True)
    for b in BOOKS:
        t0 = time.time()
        script = f"""(set-cbd "{TREE}/books/proto/")
(certify-book "{b}" ? t)
"""
        out.write(f"== certify {b}\n"); out.flush()
        p = subprocess.run(["swarm-build"] + sbcl_argv(ACL2_CORE), input=script, text=True,
                           stdout=out, stderr=subprocess.STDOUT, cwd=TREE)
        ok = (books / "proto" / (b + ".cert")).exists()
        out.write(f"== certify {b} rc {p.returncode} cert {ok} {time.time() - t0:.1f} s\n"); out.flush()
        print("certify", b, "rc", p.returncode, "cert", ok, f"{time.time() - t0:.1f} s", flush=True)
        if not ok:
            return 1
    script = f"""(set-cbd "{TREE}/books/proto/")
(include-book "pagestore-exec")
:q
(load "{TREE}/host/native/proto-pagestore.lisp")
(save-exec "{ROOT}/fnps-image" "arena-store-host")
"""
    CORE.unlink(missing_ok=True)
    out.write("== image\n"); out.flush()
    p = subprocess.run(["swarm-build"] + sbcl_argv(ACL2_CORE), input=script, text=True,
                       stdout=out, stderr=subprocess.STDOUT, cwd=TREE)
    out.close()
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
            rc, recs, raw = run(["mutate", store, "main", "append", "1", "1"])
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
                              o and o[0].get("ms-total"), fr and fr[0].get("ms-to-first-request"),
                              flush=True)
                        if rc != 0 or not fr:
                            print(raw[-3000:]); return 1
            if not a.keep:
                shutil.rmtree(store, ignore_errors=True)
    return 0


def q2(a):
    d = out_dir(a)
    res = d / "q2.jsonl"
    base = NVME if a.fs == "nvme" else ZFS
    for kind in ("random", "append"):
        store = str(base / f"q2-{kind}")
        shutil.rmtree(store, ignore_errors=True)
        rc, recs, raw = run(["init", store, str(a.n)])
        if rc != 0:
            print(raw[-3000:]); return 1
        append(res, {"fs": a.fs, "kind": kind, "phase": "init", "init": ev(recs, "init")})
        for count in [int(x) for x in a.counts.split(",")]:
            for i in range(a.runs):
                st = str(d / f"strace-{a.fs}-{kind}-{count}-{i}.txt") if i == 0 else None
                rc, recs, raw = run(["mutate", store, "main", kind, str(count), "1"], strace=st)
                c = ev(recs, "commit")
                rec = {"fs": a.fs, "layout": "inline-2level", "kind": kind, "count": count, "run": i,
                       "rc": rc, "commit": c[0]["commit"] if c else None}
                if st and Path(st).exists():
                    rec["strace"] = Path(st).read_text()
                append(res, rec)
                print(kind, count, i, rc, c and c[0]["commit"].get("ms-total"), flush=True)
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


def refusal_key(r):
    parts = r.strip("()").split()
    return parts[2] if len(parts) > 2 else r


BOOK_CUTS = ["begin", "page-written", "table-written", "dir-written", "record-torn",
             "record-written", "record-synced"]


def q3(a):
    d = out_dir(a)
    res = d / "q3-cuts.jsonl"
    rng = random.Random(a.seed)
    store = str(NVME / "q3")
    shutil.rmtree(store, ignore_errors=True)
    rc, recs, raw = run(["init", store, str(a.n)])
    if rc != 0:
        print(raw[-3000:]); return 1
    rc, recs, raw = run(["digest", store, "main"])
    cur = ev(recs, "digest")[0]
    expected = {cur["txid"]: cur["digest"]}
    after_new = {"record-written", "record-synced"}
    viol = 0
    counts = {}
    refusals = {}
    for i in range(a.cuts):
        name = BOOK_CUTS[i % len(BOOK_CUTS)]
        kind = rng.choice(["random", "append"])
        count = rng.choice([1, 2, 5, 17, 40]) if kind == "random" else rng.choice([1, 3, 8])
        k = 1
        if name == "page-written":
            k = rng.randint(1, 3)
        elif name == "table-written":
            k = rng.choice([1, 1, 2])
        env = {"FNPS_CUT": f"{name}:{k}", "FNPS_DIGEST": "1", "FNPS_SEED": str(rng.randrange(1 << 30))}
        mmode = rng.choice(["eager", "lazy"])
        rc, recs, raw = run(["mutate", store, "main", kind, str(count), "1", mmode], env=env)
        pre = ev(recs, "pre")
        if not pre or not pre[0].get("next-digest"):
            print(raw[-3000:]); return 1
        new_txid = cur["txid"] + 1
        expected[new_txid] = pre[0]["next-digest"]
        reached = rc == 77
        if not reached and rc != 0:
            print(raw[-3000:]); return 1
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
            refusals[refusal_key(r)] = refusals.get(refusal_key(r), 0) + 1
        label = name + (f":{k}" if name in ("page-written", "table-written") else "")
        c = counts.setdefault(name, {"cuts": 0, "reached": 0, "violations": 0})
        c["cuts"] += 1; c["reached"] += int(reached); c["violations"] += int(not ok)
        viol += int(not ok)
        append(res, {"i": i, "cut": label, "kind": kind, "count": count, "mutate_mode": mmode,
                     "rc": rc, "reached": reached, "open_mode": mode, "want_txid": want_txid,
                     "got": got, "refusals": refs, "ok": ok})
        if not ok:
            print("VIOLATION", i, label, raw2[-2000:], flush=True)
        if got:
            if got["txid"] < new_txid:
                expected.pop(new_txid, None)
            cur = got
        print(i, label, "rc", rc, "landed", got and got["txid"], "ok", ok, flush=True)
    # Damage cases.
    dres = d / "q3-damage.jsonl"
    kinds = ["page-new", "page-shared", "table-new", "table-shared", "dir"]
    dmg = {k: {"cases": 0, "ok": 0} for k in kinds}
    dviol = 0

    def damage(what, probe=False):
        rc_, r_, raw_ = run(["damage", store, "main", what] + (["probe"] if probe else []))
        dm_ = ev(r_, "damage")
        if not dm_:
            print(raw_[-2000:])
        return dm_[0] if dm_ else None

    for j in range(a.damage):
        which = kinds[j % len(kinds)]
        # A fresh commit T over T-1, both known.
        mk = ["append", "1"] if which == "table-shared" else ["random", "5"]
        rc, recs, raw = run(["mutate", store, "main", mk[0], mk[1], "1"],
                            env={"FNPS_SEED": str(rng.randrange(1 << 30))})
        com = ev(recs, "commit")
        if rc != 0 or not com:
            print(raw[-3000:]); return 1
        dirty = com[0]["commit"]["lpages"] or []
        npages = com[0]["commit"]["pages"]
        prev = cur
        rc, recs, raw = run(["digest", store, "main"])
        cur = ev(recs, "digest")[0]
        expected[cur["txid"]] = cur["digest"]
        T = cur["txid"]
        if which == "page-new":
            what = str(dirty[0])
        elif which == "page-shared":
            what = str(next(p for p in range(1, npages) if p not in dirty))
        elif which == "table-new":
            what = f"table:{dirty[0] // 341}"
        elif which == "table-shared":
            what = "table:0"
        else:
            what = "dir"
        pr = damage(what, probe=True)
        if pr is None:
            return 1
        new_written = pr["entry-txid"] == T
        if new_written != (which in ("page-new", "table-new", "dir")):
            print("damage target not as intended", which, pr, flush=True)
            append(dres, {"j": j, "which": which, "skipped": pr}); continue
        touch = str(pr["lpage"] if pr["kind"] == "page" else (341 * pr["lpage"] + 1 if pr["kind"] == "table" else 1))
        damage(what)
        rce, re_, rawe = run(["digest", store, "main", "eager"])
        rcl, rl, rawl = run(["open", store, "main", "lazy", touch])
        damage(what)                                              # restore
        rcr, rr, rawr = run(["digest", store, "main", "eager"])
        restored = ev(rr, "digest")
        oe = ev(re_, "open"); ge = ev(re_, "digest")
        ol = ev(rl, "open"); fl = ev(rl, "first-request")
        erefs = (oe[0]["refusals"] or []) if oe else []
        lrefs = (ol[0]["refusals"] or []) if ol else []
        name = {"page": ":page-damaged", "table": ":table-damaged", "dir": ":dir-damaged"}[pr["kind"]]
        if which in ("page-new", "table-new", "dir"):
            # The newest commit wrote it: both modes refuse T by name and
            # land on T-1 with its digest.
            eok = bool(ge) and ge[0]["txid"] == prev["txid"] and ge[0]["digest"] == prev["digest"] \
                and any(name in r for r in erefs)
            lok = bool(ol) and ol[0].get("txid") == prev["txid"] and any(name in r for r in lrefs)
        else:
            # Shared with T-1: eager refuses both slots by name (nothing
            # opens); lazy lands on T and the first touch answers by name.
            eok = bool(oe) and oe[0].get("landed") is None and not ge and \
                sum(name in r for r in erefs) == 2
            lok = bool(ol) and ol[0].get("txid") == T and bool(fl) and \
                name in (fl[0].get("touch-verdict") or "")
        rok = bool(restored) and restored[0]["txid"] == T and restored[0]["digest"] == cur["digest"]
        ok = eok and lok and rok
        dmg[which]["cases"] += 1; dmg[which]["ok"] += int(ok)
        dviol += int(not ok)
        for r in erefs + lrefs:
            refusals["damage " + refusal_key(r)] = refusals.get("damage " + refusal_key(r), 0) + 1
        append(dres, {"j": j, "which": which, "target": pr, "T": T, "prev": prev["txid"],
                      "eager_open": oe[0] if oe else None, "eager_digest": ge[0] if ge else None,
                      "lazy_open": ol[0] if ol else None, "lazy_touch": fl[0] if fl else None,
                      "restored": rok, "eager_ok": eok, "lazy_ok": lok, "ok": ok})
        print("damage", j, which, what, "eager", eok, "lazy", lok, "restored", rok, flush=True)
    summary = {"n": a.n, "cuts": a.cuts, "violations": viol, "by_cut": counts, "refusals": refusals,
               "damage": dmg, "damage_violations": dviol}
    append(d / "q3-summary.jsonl", summary)
    print(json.dumps(summary, indent=1))
    shutil.rmtree(store, ignore_errors=True)
    return 0 if viol == 0 and dviol == 0 else 1


def summarize(a):
    """Tables (medians) from the jsonl files in --out; writes summary.md."""
    import re
    d = Path(a.out)
    lines = []
    med = lambda xs: round(statistics.median(xs), 1) if xs else None
    q1f = d / "q1.jsonl"
    if q1f.exists():
        rows = [json.loads(l) for l in q1f.read_text().splitlines()]
        sizes = {(r["fs"], r["n"]): r["bytes"] for r in rows if r.get("phase") == "size"}
        lines += ["## Q1 open (ms, median of runs)", "",
                  "| fs | records | MB on disk | mode | cache | slots | directory | table pages (n) | data read (n) | data verify | open total | to first request | seq / msgid lookup | bg pass | RSS MiB |",
                  "|---|---:|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
        keys = sorted({(r["fs"], r["n"], r["mode"], r["temp"]) for r in rows if "mode" in r})
        for k in keys:
            rs = [r for r in rows if (r.get("fs"), r.get("n"), r.get("mode"), r.get("temp")) == k
                  and r.get("open")]
            g = lambda f: med([r["open"][f] for r in rs])
            fr = lambda f: med([r["first"]["requests"][f] for r in rs if r.get("first")])
            ttfr = med([r["first"]["ms-to-first-request"] for r in rs if r.get("first")])
            bg = med([r["first"]["ms-background-pass"] for r in rs if r.get("first")])
            rss = med([r["open"]["rss-kib"] / 1024 for r in rs])
            o0 = rs[0]["open"]
            lines.append(f"| {k[0]} | {k[1]:,} | {sizes.get((k[0], k[1]), 0) / 1e6:.0f} | {k[2]} | {k[3]} | "
                         f"{g('ms-slots')} | {g('ms-dir')} | {g('ms-tables')} ({o0['tables-loaded']}) | "
                         f"{g('ms-pages-read')} ({o0['pages-loaded']}) | {g('ms-pages-verify')} | "
                         f"{g('ms-total')} | {ttfr} | {fr('ms-lookup-seq')} / {fr('ms-lookup-msgid')} | {bg} | {rss} |")
        lines.append("")
    q2f = d / "q2.jsonl"
    if q2f.exists():
        allrows = [json.loads(l) for l in q2f.read_text().splitlines()]
        for fsn in ("nvme", "zfs"):
            rows = [r for r in allrows if r.get("fs") == fsn and r.get("commit")]
            if not rows:
                continue
            inits = [r for r in allrows if r.get("fs") == fsn and r.get("phase") == "init"]
            pages = inits[0]["init"][0]["pages"] if inits and inits[0].get("init") else "?"
            lines += [f"## Q2 snapshot on {fsn} (inline, two-level table; store of {pages} pages at init; ms, median)", "",
                      "| kind | dirty pages | table pages written | dir pages | plan (digests + table) | need-table loads | page writes | table writes | dir write | record | fdatasync | total | fdatasync calls | write calls | MB written |",
                      "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
            for kind in ("random", "append"):
                for cnt in sorted({r["count"] for r in rows}):
                    rs = [r["commit"] for r in rows if r["kind"] == kind and r["count"] == cnt]
                    if not rs:
                        continue
                    g = lambda f: med([c[f] for c in rs])
                    st = [r.get("strace", "") for r in rows if r["kind"] == kind and r["count"] == cnt
                          and r.get("strace")]
                    calls = str(rs[0]["syncs"])
                    if st:
                        got = {m.group(2): int(m.group(1))
                               for m in re.finditer(r"^\s*[\d.]+\s+[\d.]+\s+\d+\s+(\d+)\s+(?:\d+\s+)?(f?d?a?t?a?sync)\s*$", st[0], re.M)}
                        calls = f"{rs[0]['syncs']} (strace: {got or 'none'})"
                    lines.append(f"| {kind} | {cnt:,} | {rs[0]['tables-written']} | {rs[0]['dir-pages']} | "
                                 f"{g('ms-plan')} | {g('ms-need')} | {g('ms-pages')} | {g('ms-tables')} | "
                                 f"{g('ms-dir')} | {g('ms-record')} | {g('ms-sync')} | {g('ms-total')} | "
                                 f"{calls} | {rs[0]['writes']} | {rs[0]['bytes'] / 1e6:.2f} |")
            lines.append("")
    q3f = d / "q3-summary.jsonl"
    if q3f.exists():
        sm = json.loads(q3f.read_text().splitlines()[-1])
        lines += [f"## Q3 process death (n = {sm['n']:,} records): {sm['cuts']} cuts, {sm['violations']} violations; damage violations {sm['damage_violations']}", "",
                  "| cut | cuts | reached | violations |", "|---|---:|---:|---:|"]
        for k, v in sm["by_cut"].items():
            lines.append(f"| {k} | {v['cuts']} | {v['reached']} | {v['violations']} |")
        lines += ["", "| damage case | cases | as required |", "|---|---:|---:|"]
        for k, v in sm["damage"].items():
            lines.append(f"| {k} | {v['cases']} | {v['ok']} |")
        lines += ["", "Refusals by name: " + ", ".join(f"{k} {v}" for k, v in sorted(sm["refusals"].items())), ""]
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
        p.add_argument("--sizes", default="40000,1000000")
        p.add_argument("--counts", default="1,100,10000")
        p.add_argument("--fs", default="nvme")
        p.add_argument("--cuts", type=int, default=210)
        p.add_argument("--damage", type=int, default=12)
        p.add_argument("--seed", type=int, default=931)
        p.add_argument("--keep", action="store_true")
    a = ap.parse_args(argv)
    return a.fn(a) or 0


if __name__ == "__main__":
    sys.exit(main())
