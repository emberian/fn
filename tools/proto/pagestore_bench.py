#!/usr/bin/env python3
"""The page store's bench and crash campaign (lane proto-pagestore,
2026-09-27; the two-level table host of lane arena-store, 2026-09-27:
planning/evidence/arena-store-2026-09-27/).

Runs ON hbox (Linux).  From the laptop:

    python3 tools/proto/pagestore_bench.py ship          # rsync the tree to hbox
    ssh hbox python3 /tank/fn/scratch/arena-store-host/tree/tools/proto/pagestore_bench.py build
    ssh hbox python3 .../pagestore_bench.py q1|q2|q3|q4|cut-map|summarize [--out DIR]

`build` certifies books/pagestore-gc, history-pages-import and
history-pages-view with their closure (tools/certify_books.py --incremental
in the w28 ACL2 against the box's certificate cache), includes them, loads
host/native/proto-pagestore.lisp and host/native/proto-history-pages.lisp
(m4, lane arena-store-4: the history image's host) and saves one image
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
SBCL = "/tank/fn/sbcl/bin/sbcl"
ACL2_CORE = "/tank/fn/acl2-8.7/saved_acl2.core"
DYN = "16000"
NVME = Path("/var/tmp/arena-store-host")        # ext4 on /dev/nvme0n1p4
ZFS = ROOT / "data"                            # tank (ZFS)
LANE = Path(__file__).resolve().parents[2]


def sbcl_argv(core, dyn=None):
    return [SBCL, "--tls-limit", "65536", "--dynamic-space-size", dyn or DYN,
            "--control-stack-size", "64", "--disable-ldb", "--core", str(core),
            "--end-runtime-options", "--no-userinit", "--eval", "(acl2::sbcl-restart)"]


def ship(_a):
    # The whole worktree (certify_books reads the registries); certificates
    # are neither sent nor deleted (the box's are installed from its cache).
    subprocess.run(["rsync", "-a", "--delete", "--exclude", "/build/", "--exclude", ".git",
                    "--exclude", "*.cert", "--exclude", "*.fasl", "--exclude", "*.port",
                    "--exclude", "*.certify.log", "--exclude", "__pycache__/",
                    f"{LANE}/", f"hbox:{TREE}/"], check=True)
    print("shipped", LANE, "->", TREE)


# The image's books: the page store's (pagestore-gc includes the rest) and
# the history image's host-called ones (m4).  Certified by the project's
# runner against the box's certificate cache (--incremental: what the cache
# holds at its digest is installed, the rest certified), under swarm-build.
ROOTS = ("books/pagestore-gc", "books/history-pages-import", "books/history-pages-view")
FARM_ACL2 = "/tank/fn/toolchains/w28/acl2-literal-4g"   # tools/farm.py HOSTS["hbox"]
CERT_CACHE = "/tank/fn/certcache"


def build(_a):
    log = ROOT / "build.log"
    out = open(log, "w")
    t0 = time.time()
    env = dict(os.environ, FN_ACL2=FARM_ACL2, FN_CERT_CACHE=CERT_CACHE, FN_CERT_ORIGIN_KIND="run",
               FN_ACL2_TIMEOUT_SECONDS="1800")
    out.write("== certify_books --incremental " + " ".join(ROOTS) + "\n"); out.flush()
    p = subprocess.run(["swarm-build", "python3", "tools/certify_books.py", "--jobs", "8", "--incremental"]
                       + list(ROOTS), stdout=out, stderr=subprocess.STDOUT, cwd=TREE, env=env)
    ok = all((TREE / (r + ".cert")).exists() for r in ROOTS)
    print("certify rc", p.returncode, "certs", ok, f"{time.time() - t0:.1f} s", flush=True)
    if p.returncode != 0 or not ok:
        out.close()
        return 1
    script = f"""(set-cbd "{TREE}/books/")
(include-book "pagestore-gc")
(include-book "history-pages-import")
(include-book "history-pages-view")
:q
(load "{TREE}/host/native/proto-pagestore.lisp")
(load "{TREE}/host/native/proto-history-pages.lisp")
(save-exec "{ROOT}/fnps-image" "arena-store-host")
"""
    CORE.unlink(missing_ok=True)
    out.write("== image\n"); out.flush()
    env = dict(os.environ, ACL2_BOOK_HASH_ALISTP="NIL", ACL2_CUSTOMIZATION="NONE")
    p = subprocess.run(["swarm-build"] + sbcl_argv(ACL2_CORE), input=script, text=True,
                       stdout=out, stderr=subprocess.STDOUT, cwd=TREE, env=env)
    out.close()
    text = log.read_text()
    bad = [l for l in text.splitlines() if "ACL2 Error" in l or "debugger invoked" in l]
    print("build rc", p.returncode, "core", CORE.exists(), "errors", bad[:5])
    return 0 if CORE.exists() and not bad else 1


def lisp_str(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def run(args, env=None, timeout=3600, strace=None, main="fnps-main", memmax="24G", dyn=None):
    """One image process: returns (rc, [json records], raw output)."""
    form = f"({main} (list " + " ".join(lisp_str(a) for a in args) + "))"
    argv = ["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={memmax}"]
    if strace:
        argv += ["strace", "-f", "-c", "-o", strace, "-e", "trace=fsync,fdatasync"]
    argv += sbcl_argv(CORE, dyn)
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
        if a.reclaim:
            env["FNPS_RECLAIM"] = "1"
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
        rb = ev(recs, "reclaim-before")
        append(res, {"i": i, "cut": label, "kind": kind, "count": count, "mutate_mode": mmode,
                     "reclaim_before": rb[0] if rb else None,
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
    summary = {"n": a.n, "reclaim": a.reclaim, "cuts": a.cuts, "violations": viol, "by_cut": counts, "refusals": refusals,
               "damage": dmg, "damage_violations": dviol}
    append(d / "q3-summary.jsonl", summary)
    print(json.dumps(summary, indent=1))
    shutil.rmtree(store, ignore_errors=True)
    return 0 if viol == 0 and dviol == 0 else 1


def reclaim_smoke(a):
    """Init, then --commits commits with FNPS_RECLAIM=1: the free list, the
    file's pages, and a digest open (mode alternating) after every commit
    landing on that commit's txid with its pre-computed image digest."""
    d = out_dir(a)
    res = d / "reclaim.jsonl"
    rng = random.Random(a.seed)
    store = str(NVME / "reclaim")
    shutil.rmtree(store, ignore_errors=True)
    rc, recs, raw = run(["init", store, str(a.n)])
    if rc != 0:
        print(raw[-3000:]); return 1
    bad = 0
    rc, recs, raw = run(["reclaim", store, "main"])
    append(res, {"step": "reclaim-cmd", "rc": rc, "reclaim": ev(recs, "reclaim")})
    for i in range(a.commits):
        kind = rng.choice(["random", "random", "append"])
        count = rng.choice([1, 5, 40, 100]) if kind == "random" else rng.choice([1, 4, 16])
        rc, recs, raw = run(["mutate", store, "main", kind, str(count), "1", rng.choice(["lazy", "eager"])],
                            env={"FNPS_RECLAIM": "1", "FNPS_DIGEST": "1",
                                 "FNPS_SEED": str(rng.randrange(1 << 30))})
        pre = ev(recs, "pre"); com = ev(recs, "commit")
        rb = ev(recs, "reclaim-before"); ra = ev(recs, "reclaim-after")
        if rc != 0 or not pre or not com:
            print(raw[-3000:]); return 1
        c = com[0]["commit"]
        mode = "eager" if i % 2 == 0 else "lazy"
        rc2, recs2, raw2 = run(["digest", store, "main", mode])
        dg = ev(recs2, "digest")
        ok = bool(dg) and dg[0]["txid"] == c["txid"] and dg[0]["digest"] == pre[0]["next-digest"]
        bad += int(not ok)
        size = os.path.getsize(Path(store) / "pages") // 16384
        rec = {"i": i, "kind": kind, "count": count, "txid": c["txid"], "dirty": c["dirty"],
               "writes": c["writes"], "hwm_after_commit": c["hwm"], "file_pages": size,
               "reclaim_before": rb[0] if rb else None, "reclaim_after": ra[0] if ra else None,
               "open_mode": mode, "landed": dg[0]["txid"] if dg else None, "ok": ok}
        append(res, rec)
        print(i, kind, count, "txid", c["txid"], "file pages", size,
              "freed before", rb and rb[0]["freed"], "free after commit",
              rb and rb[0]["free-after"] - (c["writes"] - 1), "freed after", ra and ra[0]["freed"],
              "ok", ok, flush=True)
    append(res, {"summary": {"commits": a.commits, "violations": bad}})
    shutil.rmtree(store, ignore_errors=True)
    return 0 if bad == 0 else 1


# ---------------------------------------------------------------------------
# m4 (lane arena-store-4): the history image over the page store.

NATIVE_CORE = Path("/tank/fn/scratch/batch-ay/native-n3-9127a2912/tree/build/fn-host-developer.core")
FIXTURES = Path("/tank/fn/scratch/fixtures")
M4 = ROOT / "m4"
EVS = NVME / "m4"


def export(a):
    """The fixture's records through the native image's own open
    (tools/proto/history_export.lisp): a copy of FIXTURES/NAME/store (its
    README: copy, touch writer.lock mode 600, `store COPY
    rebind-filesystem' since fixtures are built on tmpfs), one read-only
    open, each record's `fn-scc-encode' framed into EVS/NAME.evs.  Prints the export line and the process's peak RSS."""
    name = a.fixture
    fx = M4 / "fx" / name
    shutil.rmtree(fx, ignore_errors=True)
    fx.mkdir(parents=True)
    subprocess.run(["cp", "-a", str(FIXTURES / name / "store"), str(fx / "store")], check=True)
    lock = fx / "store" / "writer.lock"
    lock.touch(); os.chmod(lock, 0o600)
    # The fixture was built on tmpfs (README, PKT-579): the copy is rebound.
    rb = subprocess.run([str(NATIVE_CORE.with_suffix("")), "--fn", "store", str(fx / "store"), "rebind-filesystem"],
                        capture_output=True, text=True)
    print("rebind-filesystem rc", rb.returncode, (rb.stdout + rb.stderr).strip()[-300:], flush=True)
    if rb.returncode != 0:
        return 1
    EVS.mkdir(parents=True, exist_ok=True)
    out = EVS / f"{name}.evs"
    log = M4 / f"export-{name}.log"
    env = dict(os.environ, FNHX_ROOT=str(fx / "store"), FNHX_OUT=str(out),
               SBCL_HOME="/tank/fn/sbcl/lib/sbcl/")
    argv = ["/usr/bin/time", "-v", "systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={a.memmax}",
            SBCL, "--tls-limit", "65536", "--dynamic-space-size", a.dyn, "--control-stack-size", "64",
            "--disable-ldb", "--core", str(NATIVE_CORE), "--noinform", "--end-runtime-options",
            "--no-userinit", "--eval", f'(load "{TREE}/tools/proto/history_export.lisp")',
            "--eval", "(acl2::sbcl-restart)", "--disable-debugger", "--end-toplevel-options"]
    t0 = time.time()
    with open(log, "w") as f:
        p = subprocess.run(argv, stdin=subprocess.DEVNULL, stdout=f, stderr=subprocess.STDOUT, env=env)
    text = log.read_text(errors="replace")
    lines = [l for l in text.splitlines() if "FNHX-JSON" in l or "Maximum resident" in l]
    print("export rc", p.returncode, f"{time.time() - t0:.1f} s", "log", log)
    print("\n".join(lines))
    return p.returncode


def frames(path, upto):
    """The events file's first UPTO frames as hex (the harness's oracle:
    the octets the export wrote are the octets a record must read back)."""
    out = []
    with open(path, "rb") as f:
        while len(out) < upto:
            h = f.read(8)
            if len(h) < 8:
                break
            out.append(f.read(int.from_bytes(h, "little")).hex().upper())
    return out


def hp_run(args, env=None, **kw):
    return run(args, env=env, main="fnhp-main", **kw)


HDR = ("n", "lens", "starts", "np")


def hdr(rec):
    return {k: rec.get(k) for k in HDR}


def hp_reopen(store, salt, mode, want_n, fr):
    """Reopen: the header, records 0 and -1 in hex, the image digest."""
    rc, recs, raw = hp_run(["open", store, str(salt), mode, "0", "-1"],
                           env={"FNPS_DIGEST": "1", "FNHP_HEX": "1"})
    o = ev(recs, "hp-open")
    got = o[0] if o else None
    rs = ev(recs, "hp-record"); dg = ev(recs, "digest")
    return rc, got, rs, (dg[0] if dg else None), raw


def records_ok(rs, n, fr):
    """Records 0 and n-1 read back as the export's frames."""
    if n == 0:
        return not rs
    return {r["i"] for r in rs} == {0, n - 1} and \
        all(r["result"] == "ok" and r["enc-hex"] == fr[r["i"]] for r in rs)


def hp_cuts(a):
    """The history image's process-death campaign (m4).  (1) The import:
    a fresh store, --n0 events imported and committed with FNPS_CUT at
    every cut of *pgs-snapshot-cuts*; reopened, the store holds no history
    (the cut preceded the record) or exactly the import's (ACL2's header
    answer, its image digest, records 0 and n-1 as exported).  (2) Appends:
    one store of --n events, then --cuts appends of 1..60 events killed at
    each cut in turn; reopened, the header answer, the digest and the
    records are the last complete commit's: the old history or the new,
    nothing else."""
    d = out_dir(a)
    res = d / "hp-cuts.jsonl"
    rng = random.Random(a.seed)
    evs = a.evs
    salt = a.salt
    fr = frames(evs, a.n + a.cuts * 60 + 1)
    after_new = {"record-written", "record-synced"}
    viol = 0
    counts = {}

    def tally(kind, name, reached, ok):
        c = counts.setdefault(kind + ":" + name, {"cuts": 0, "reached": 0, "violations": 0})
        c["cuts"] += 1; c["reached"] += int(reached); c["violations"] += int(not ok)

    # (1) import cuts.
    for i in range(a.import_cuts):
        name = BOOK_CUTS[i % len(BOOK_CUTS)]
        k = rng.randint(1, 3) if name == "page-written" else (rng.choice([1, 2]) if name == "table-written" else 1)
        store = str(NVME / "hp-imp")
        shutil.rmtree(store, ignore_errors=True)
        n0 = rng.choice([1, 7, 40, 200])
        rc, recs, raw = hp_run(["import", store, evs, str(salt), "64", str(n0)],
                               env={"FNPS_CUT": f"{name}:{k}", "FNPS_DIGEST": "1"})
        pre = ev(recs, "hp-pre")
        reached = rc == 77
        if not pre or (rc not in (0, 77)):
            print(raw[-3000:]); return 1
        land_new = (not reached) or name in after_new
        mode = rng.choice(["eager", "lazy"])
        rc2, got, rs, dg, raw2 = hp_reopen(store, salt, mode, n0, fr)
        if land_new:
            ok = bool(got) and got["landed"] and hdr(got) == hdr(pre[0]) and dg is not None \
                and dg["digest"] == pre[0]["next-digest"] and records_ok(rs, n0, fr)
        else:
            ok = bool(got) and not got["landed"]
        tally("import", name, reached, ok)
        viol += int(not ok)
        append(res, {"phase": "import", "i": i, "cut": f"{name}:{k}", "n0": n0, "rc": rc, "reached": reached,
                     "open_mode": mode, "want": "new" if land_new else "none", "got": got,
                     "digest": dg, "records": [(r["i"], r["result"], r["enc-len"]) for r in rs], "ok": ok})
        if not ok:
            print("VIOLATION import", i, name, raw2[-2000:], flush=True)
        print("import", i, f"{name}:{k}", "n0", n0, "rc", rc, "landed", got and got.get("landed"), "ok", ok, flush=True)
    # (2) append cuts.
    store = str(NVME / "hp-app")
    shutil.rmtree(store, ignore_errors=True)
    rc, recs, raw = hp_run(["import", store, evs, str(salt), "256", str(a.n)], env={"FNPS_DIGEST": "1"})
    pre = ev(recs, "hp-pre"); imp = ev(recs, "hp-import")
    if rc != 0 or not pre or not imp:
        print(raw[-3000:]); return 1
    cur = {"txid": imp[0]["commit"]["txid"], "hdr": hdr(pre[0]), "digest": pre[0]["next-digest"]}
    for i in range(a.cuts):
        name = BOOK_CUTS[i % len(BOOK_CUTS)]
        k = rng.randint(1, 3) if name == "page-written" else (rng.choice([1, 1, 2]) if name == "table-written" else 1)
        count = rng.choice([1, 1, 3, 17, 60])
        n = cur["hdr"]["n"]
        amode = rng.choice(["eager", "lazy"])
        rc, recs, raw = hp_run(["append", store, evs, str(n), str(count), str(salt), amode],
                               env={"FNPS_CUT": f"{name}:{k}", "FNPS_DIGEST": "1"})
        pre = ev(recs, "hp-pre")
        reached = rc == 77
        if not pre or not pre[0].get("next-digest") or rc not in (0, 77):
            print(raw[-3000:]); return 1
        new = {"txid": cur["txid"] + 1, "hdr": hdr(pre[0]), "digest": pre[0]["next-digest"]}
        land_new = (not reached) or name in after_new
        want = new if land_new else cur
        mode = rng.choice(["eager", "lazy"])
        rc2, got, rs, dg, raw2 = hp_reopen(store, salt, mode, want["hdr"]["n"], fr)
        ok = bool(got) and got["landed"] and got["txid"] == want["txid"] and hdr(got) == want["hdr"] \
            and dg is not None and dg["digest"] == want["digest"] and records_ok(rs, want["hdr"]["n"], fr)
        tally("append", name, reached, ok)
        viol += int(not ok)
        grew = new["hdr"]["np"] != cur["hdr"]["np"]
        append(res, {"phase": "append", "i": i, "cut": f"{name}:{k}", "count": count, "append_mode": amode,
                     "rc": rc, "reached": reached, "open_mode": mode, "want": "new" if land_new else "old",
                     "relocated": grew, "want_hdr": want["hdr"], "got": got, "digest_ok": bool(dg) and dg["digest"] == want["digest"],
                     "records": [(r["i"], r["result"], r["enc-len"]) for r in rs], "ok": ok})
        if not ok:
            print("VIOLATION append", i, name, raw2[-2000:], flush=True)
        if got and got.get("landed") and got["txid"] in (cur["txid"], new["txid"]):
            cur = want if ok else cur
        print("append", i, f"{name}:{k}", "count", count, "rc", rc, "landed", got and got.get("txid"),
              "n", got and got.get("n"), "grew", grew, "ok", ok, flush=True)
    summary = {"evs": evs, "n": a.n, "import_cuts": a.import_cuts, "append_cuts": a.cuts,
               "violations": viol, "by_cut": counts,
               "relocating_appends": sum(1 for l in res.read_text().splitlines()
                                         if json.loads(l).get("relocated"))}
    append(d / "hp-cuts-summary.jsonl", summary)
    print(json.dumps(summary, indent=1))
    shutil.rmtree(store, ignore_errors=True)
    shutil.rmtree(str(NVME / "hp-imp"), ignore_errors=True)
    return 0 if viol == 0 else 1


def hp_measure(a):
    """One matched measurement of the history image on the page store (m4):
    per fixture, the import of every exported event (one commit), the open
    (page store open + fn-hp-x-header) lazy with the page cache dropped and
    then warm, and eager warm, records 0 and N/2 through fn-hp-records-at
    (fills included), the RSS after open and after the reads.  Before the
    opens, the commit of 1,000 appended events and then of 1 (so the lazy
    open verifies what a one-event commit wrote, as q1).  One run each; every command line is in
    the jsonl."""
    d = out_dir(a)
    res = d / "hp-measure.jsonl"
    for name in a.fixtures.split(","):
        evs = str(EVS / f"{name}.evs")
        store = str(NVME / f"hp-{name}")
        shutil.rmtree(store, ignore_errors=True)
        kw = {"memmax": a.memmax, "dyn": a.dyn, "timeout": 4 * 3600}

        def step(label, args, env=None, cold=False):
            if cold:
                drop_caches()
            t0 = time.time()
            rc, recs, raw = hp_run(args, env=env, **kw)
            rec = {"fixture": name, "step": label, "argv": args, "env": env or {}, "cold": cold,
                   "rc": rc, "wall_s": round(time.time() - t0, 2), "recs": recs}
            append(res, rec)
            print(name, label, "rc", rc, f"wall {rec['wall_s']} s", flush=True)
            if rc != 0:
                print(raw[-3000:])
            return rc, recs

        rc, recs = step("import", ["import", store, evs, str(a.salt), "4096"])
        if rc != 0:
            return 1
        imp = ev(recs, "hp-import")[0]
        n = imp["n"]
        # The commits, then the opens: the last commit is the 1-event one,
        # so a lazy open verifies the pages that commit wrote (q1's steady
        # state), not the import's every page.
        step("append-1000", ["append", store, evs, "0", "1000", str(a.salt), "lazy"])
        step("append-1", ["append", store, evs, "1000", "1", str(a.salt), "lazy"])
        n += 1001
        for label, cold in (("open-cold", True), ("open-warm", False)):
            step(label, ["open", store, str(a.salt), "lazy", "0", str(n // 2)], cold=cold)
        step("open-eager-warm", ["open", store, str(a.salt), "eager", "0", str(n // 2)])
        du = subprocess.run(["du", "-sb", store], capture_output=True, text=True).stdout.split()[0]
        append(res, {"fixture": name, "step": "size", "bytes": int(du)})
        if not a.keep:
            shutil.rmtree(store, ignore_errors=True)
    return 0


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
                     ("reclaim-smoke", reclaim_smoke), ("summarize", summarize)):
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
        p.add_argument("--commits", type=int, default=10)
        p.add_argument("--seed", type=int, default=931)
        p.add_argument("--keep", action="store_true")
        p.add_argument("--reclaim", action="store_true", help="FNPS_RECLAIM=1 on every commit")
    p = sub.add_parser("hp-cuts")
    p.set_defaults(fn=hp_cuts)
    p.add_argument("--out", default=str(M4 / "results"))
    p.add_argument("--evs", default=str(EVS / "syn100k-2k.evs"))
    p.add_argument("--salt", type=int, default=0)
    p.add_argument("--n", type=int, default=1000)
    p.add_argument("--cuts", type=int, default=70)
    p.add_argument("--import-cuts", type=int, default=21)
    p.add_argument("--seed", type=int, default=928)
    p = sub.add_parser("hp-measure")
    p.set_defaults(fn=hp_measure)
    p.add_argument("--out", default=str(M4 / "results"))
    p.add_argument("--fixtures", default="syn100k-2k,syn1m-2k")
    p.add_argument("--salt", type=int, default=0)
    p.add_argument("--memmax", default="80G")
    p.add_argument("--dyn", default="32000")
    p.add_argument("--keep", action="store_true")
    p = sub.add_parser("export")
    p.set_defaults(fn=export)
    p.add_argument("fixture")
    p.add_argument("--memmax", default="24G")
    p.add_argument("--dyn", default="20000")
    a = ap.parse_args(argv)
    return a.fn(a) or 0


if __name__ == "__main__":
    sys.exit(main())
