#!/usr/bin/env python3
"""Power loss under the page store (lane proto-pagestore, 2026-09-27; the
two-level table host of lane arena-store, 2026-09-27).

The rig is tools/power_loss.py's (lane power-loss): dm-log-writes over loop
devices whose images live in /dev/shm, ext4 with barriers on the mapped
device, every write/flush/FUA logged in completion order; a cut replays the
log to an entry position P and keeps, of the writes after the last flush
before P, none (`flush`), all (`prefix`), a seeded subset (`subset`) or
4096-octet pieces (`torn`).  This file imports rig_up / rig_down / mark /
parse_log / index / choose_cuts / build_image from it and supplies the page
store's workload and oracle.  It runs on hbox (sudo -n for losetup, dmsetup,
mount, e2fsck; the store runs as the invoking user) with the saved image of
tools/proto/pagestore_bench.py `build`.

Workload (phase `inline`: the inline one-barrier layout, root main's slots
in page 0 of the page file, ONE fdatasync per commit; the two-level table:
a commit writes its data pages, the touched table pages, the directory run
and the record): `init` (txid 1), then K commits of seeded random or append
dirty sets, opened lazily or eagerly.  Before a commit starts the client
writes the mark `try-L-N` (txid N may land from here on); after the
commit's process exits 0 -- its fdatasync returned -- it writes `ack-L-N`
(txid N durable).  The expected image digest of every txid is recorded
when it is computed (FNPS_DIGEST, before the commit writes).

Oracle at a cut: the image mounts, `e2fsck -fn` is clean, and an eager open
of the store lands on a txid T with
    last ack before the cut  <=  T  <=  last try before the cut
and T's recorded image digest.  A record that did not land whole is refused
by name (:commit-torn) or its missing pages are (:page-damaged,
:table-damaged, :dir-damaged, :dir-unloaded) and the open falls back; any
other landing is a violation.  Before ack-1 (the store is being created)
the store may be absent or refuse to open (nothing was acknowledged).
Controls (the rig's teeth): the device just after ack-N's mark, judged as
if N+1 were acknowledged: the oracle must report every one (N+1's writes
all follow the mark).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import random
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import power_loss as pl          # noqa: E402  (the lane power-loss rig)
import pagestore_bench as pb     # noqa: E402

pl.DM = "fn-pgs-power-loss"      # our own mapped device name


def ns(**kw):
    return argparse.Namespace(**kw)


def run(args, env=None):
    return pb.run(args, env=env, timeout=600)


def workload(a):
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    mnt = Path(rig["mnt"])
    wl = work / "workload.jsonl"
    wl.write_text("")
    rng = random.Random(a.seed)

    def log(**rec):
        pl.out_line(wl, **rec)

    for layout, fsyncs in (("inline", "1"),):
        store = mnt / ("s-" + layout)
        pl.mark("phase:" + layout)
        pl.mark("try-%s-1" % layout)
        rc, recs, raw = run(["init", str(store), str(a.n)])
        if rc != 0:
            raise SystemExit("init failed: " + raw[-2000:])
        pl.mark("ack-%s-1" % layout)
        rc, recs, raw = run(["digest", str(store), "main"])
        d = pb.ev(recs, "digest")[0]
        log(layout=layout, txid=1, digest=d["digest"], tag="init")
        for i in range(a.commits):
            kind = rng.choice(["random", "random", "append"])
            count = rng.choice([1, 3, 20, 100]) if kind == "random" else rng.choice([1, 4, 16])
            txid = i + 2
            pl.mark("try-%s-%d" % (layout, txid))
            mode = rng.choice(["lazy", "eager"])
            rc, recs, raw = run(["mutate", str(store), "main", kind, str(count), fsyncs, mode],
                                env={"FNPS_DIGEST": "1", "FNPS_SEED": str(rng.randrange(1 << 30))})
            pre = pb.ev(recs, "pre"); com = pb.ev(recs, "commit")
            if rc != 0 or not pre or not pre[0].get("next-digest") or not com \
                    or com[0]["commit"]["txid"] != txid:
                raise SystemExit("commit failed: " + raw[-2000:])
            pl.mark("ack-%s-%d" % (layout, txid))
            c = com[0]["commit"]
            log(layout=layout, txid=txid, digest=pre[0]["next-digest"], kind=kind, count=count,
                mode=mode, syncs=c["syncs"], dirty=c["dirty"], tables=c["tables-written"],
                tag="commit")
        print(layout, "done", flush=True)
    pl.mark("end")
    log(tag="done")


def check(image_mnt, store, want_lo, want_hi, expected, before_ack1, violations, rec):
    if not store.exists():
        rec["store"] = "absent"
        if not before_ack1:
            violations.append("store-absent-after-ack")
        return
    rc, recs, raw = run(["digest", str(store), "main", "eager"])
    o = pb.ev(recs, "open"); d = pb.ev(recs, "digest")
    rec["refusals"] = (o[0]["refusals"] or []) if o else []
    if not d:
        rec["landed"] = None
        rec["open_rc"] = rc
        if o is None or not o:
            rec["open_error"] = raw[-400:]
        if not before_ack1:
            violations.append("no-commit-opens-after-ack")
        return
    t = d[0]["txid"]
    rec["landed"] = t
    if not (want_lo <= t <= want_hi):
        violations.append("landed-%d-outside-%d..%d" % (t, want_lo, want_hi))
    elif d[0].get("digest") is None or expected.get(t) != d[0]["digest"]:
        violations.append("digest-mismatch-at-%d" % t)


def cuts(a):
    work = Path(a.work)
    rig = json.loads((work / "rig.json").read_text())
    idx = json.loads((work / "index.json").read_text())
    L = pl.parse_log(rig["log"])
    ents, ss = L["entries"], L["sectorsize"]
    marks = [tuple(x) for x in idx["marks"]]
    wl = [json.loads(l) for l in (work / "workload.jsonl").read_text().splitlines()]
    expected = {}
    for r in wl:
        if r.get("tag") in ("init", "commit"):
            expected.setdefault(r["layout"], {})[r["txid"]] = r["digest"]
    tries, acks = {}, {}
    for i, t in marks:
        for pre, dst in (("try-", tries), ("ack-", acks)):
            if t.startswith(pre):
                lay, n = t[len(pre):].rsplit("-", 1)
                dst.setdefault(lay, []).append((i, int(n)))
    plan = {"inline": a.per_phase}
    chosen = pl.choose_cuts(ents, marks, plan, a.seed)
    crng = random.Random(a.seed + 1)
    controls = {}
    for lay in ("inline",):
        ak = acks.get(lay, [])
        cands = [(at, n) for at, n in ak if any(m == n + 1 for _, m in ak)]
        for at, n in crng.sample(cands, min(a.controls, len(cands))):
            controls[at + 1] = (lay, n + 1)
            chosen.append((at + 1, "control-" + lay, "flush", crng.randrange(1 << 30)))
    chosen.sort()
    base = work / "base.img"
    pl.sh("truncate", "-s", "0", base)
    pl.sh("truncate", "-s", str(os.path.getsize(rig["data"])), base)
    base_upto = 0
    img = work / "cut.img"
    mnt = Path(rig["mnt"])
    results = work / "cuts.jsonl"
    results.write_text("")
    logf = open(rig["log"], "rb")
    print("cuts planned: %d" % len(chosen), flush=True)
    for n, (cut, phase, mode, seed) in enumerate(chosen):
        base_upto, tail = pl.build_image(ents, logf, base, base_upto, cut, mode, seed, ss, img)
        lay = phase.split("-", 1)[1] if phase.startswith("control-") else phase
        ak = [m for i, m in acks.get(lay, []) if i < cut]
        tr = [m for i, m in tries.get(lay, []) if i < cut]
        lo = max(ak) if ak else 0
        hi = max(tr) if tr else 0
        if phase.startswith("control-"):
            lo = controls[cut][1]
        rec = {"cut": cut, "phase": phase, "mode": mode, "seed": seed, "acked": lo,
               "attempted": hi, "durable_upto": tail["durable_upto"], "tail": tail["tail"],
               "kept": len(tail["kept"])}
        violations = []
        loop = pl.sudo("losetup", "--show", "-f", img, stdout=subprocess.PIPE, text=True).stdout.strip()
        try:
            r = pl.sudo("mount", "-t", "ext4", loop, mnt, check=False, stderr=subprocess.PIPE, text=True)
            if r.returncode:
                rec["fs"] = "mount-failed: " + r.stderr[-300:]
                violations.append("fs-mount")
            else:
                pl.sudo("umount", mnt)
                fsck = pl.sudo("e2fsck", "-fn", loop, check=False, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
                rec["e2fsck"] = fsck.returncode
                if fsck.returncode:
                    rec["e2fsck_out"] = fsck.stdout[-600:]
                pl.sudo("mount", "-t", "ext4", loop, mnt)
                pl.sudo("chown", "-R", "%d:%d" % (os.getuid(), os.getgid()), mnt)
                check(mnt, mnt / ("s-" + lay), lo, hi, expected.get(lay, {}), lo == 0,
                      violations, rec)
        except Exception as e:  # a harness failure is not a verdict
            rec["harness_error"] = repr(e)[-400:]
        finally:
            pl.sudo("umount", mnt, check=False, stderr=subprocess.DEVNULL)
            pl.sudo("losetup", "-d", loop, check=False)
        rec["violations"] = violations
        if phase.startswith("control-"):
            rec["control_caught"] = bool(violations)
        pl.out_line(results, **rec)
        print("%d/%d cut=%d %s %s acked=%d att=%d landed=%s v=%s" % (
            n + 1, len(chosen), cut, phase, mode, lo, hi, rec.get("landed"), violations[:3]),
            flush=True)
    logf.close()


def summary(a):
    rows = [json.loads(l) for l in (Path(a.work) / "cuts.jsonl").read_text().splitlines()]
    out = ["| phase | cuts | violations | flush / prefix / subset / torn | landed = acked | landed > acked (in flight, committed) | before first ack | refusals by name | e2fsck non-zero | harness errors |",
           "| --- | ---: | ---: | --- | ---: | ---: | ---: | --- | ---: | ---: |"]
    for ph in sorted({r["phase"] for r in rows}):
        rs = [r for r in rows if r["phase"] == ph]
        modes = " / ".join(str(sum(r["mode"] == m for r in rs)) for m in ("flush", "prefix", "subset", "torn"))
        refs = {}
        for r in rs:
            for x in r.get("refusals", []):
                p = x.strip("()").split()
                k = p[2] if len(p) > 2 else x
                refs[k] = refs.get(k, 0) + 1
        ctl = ph.startswith("control-")
        v = sum(bool(r["violations"]) for r in rs)
        out.append("| %s | %d | %s | %s | %d | %d | %d | %s | %d | %d |" % (
            ph, len(rs), ("%d caught" % v) if ctl else str(v), modes,
            sum(r.get("landed") == r["acked"] for r in rs),
            sum((r.get("landed") or 0) > r["acked"] for r in rs),
            sum(r["acked"] == 0 for r in rs),
            ", ".join("%s %d" % kv for kv in sorted(refs.items())) or "-",
            sum(bool(r.get("e2fsck")) for r in rs), sum("harness_error" in r for r in rs)))
    text = "\n".join(out) + "\n"
    (Path(a.work) / "summary.md").write_text(text)
    print(text)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("rig-up"); p.add_argument("work")
    p.add_argument("--data-mib", type=int, default=512); p.add_argument("--log-mib", type=int, default=4096)
    p.set_defaults(fn=lambda a: pl.rig_up(Path(a.work), a.data_mib, a.log_mib))
    p = sub.add_parser("rig-down"); p.add_argument("work")
    p.set_defaults(fn=lambda a: pl.rig_down(Path(a.work)))
    p = sub.add_parser("workload"); p.add_argument("work")
    p.add_argument("--n", type=int, default=20000); p.add_argument("--commits", type=int, default=40)
    p.add_argument("--seed", type=int, default=77); p.set_defaults(fn=workload)
    p = sub.add_parser("index"); p.add_argument("work"); p.set_defaults(fn=lambda a: pl.index(a))
    p = sub.add_parser("cuts"); p.add_argument("work")
    p.add_argument("--per-phase", type=int, default=100); p.add_argument("--controls", type=int, default=8)
    p.add_argument("--seed", type=int, default=931); p.set_defaults(fn=cuts)
    p = sub.add_parser("summary"); p.add_argument("work"); p.set_defaults(fn=summary)
    a = ap.parse_args(argv)
    a.fn(a)
    return 0


if __name__ == "__main__":
    sys.exit(main())
