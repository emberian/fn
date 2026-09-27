#!/usr/bin/env python3
"""PKT-686: an interrupted `store reclaim`, then its rerun, with the rerun's
whole output kept (lane power-loss-openbsd-2, 2026-09-27; the rig of
tools/power_loss_openbsd.py).

Per round: a fresh store (the campaign's init flags), the owner, two posting
connections until TARGET acknowledgements, the owner stopped, `retention set
released-by-all-holders`, `store reclaim` cut at a uniform point of
[LO, HI] s, reboot, fsck, `recover` (its line kept: whether a checkpoint
survived), a copy of the store (`cp -Rp ROOT ROOT.pre-rerun`), then the rerun
with stdout and stderr kept whole, the guest's `ulimit -a`, the heap figure
the launcher chose (`fn heap`), and dmesg's tail.  A failing rerun keeps the
copy for a second rerun under a different heap (--heap-retry MB).

  python3 power_loss_openbsd_reclaim.py --fn BIN NAME ROUNDS SEED [--target N]
"""
import argparse, json, random, shlex, subprocess, sys, threading, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import power_loss_openbsd as P

ap = argparse.ArgumentParser()
ap.add_argument("--base", default="/tank/fn/scratch/power-loss-openbsd")
ap.add_argument("--fn", required=True)
ap.add_argument("name")
ap.add_argument("rounds", type=int)
ap.add_argument("seed", type=int)
ap.add_argument("--target", type=int, default=1600)
ap.add_argument("--lo", type=float, default=0.5)
ap.add_argument("--hi", type=float, default=7.0)
ap.add_argument("--heap-retry", type=int, default=1800)
ap.add_argument("--no-cut", action="store_true",
                help="the control: the first reclaim runs to completion (no cut, no rerun)")
a = ap.parse_args()
P.FN = FN = a.fn
B = Path(a.base)
cfg = json.loads((B / a.name / "cfg.json").read_text())
vm = P.VM(B, cfg)
vm.boots = 700
rng = random.Random(a.seed)
out = B / a.name / "reclaim686"
out.mkdir(exist_ok=True)
flags = "--max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-article-octets 8192 --max-groups-per-article 16 --max-open-suffix 16"


def op(ep, verb, timeout=1800, env=""):
    return vm.ssh("cd /var/pl && %s %s operator /var/pl/%s.toml %s" % (env, FN, ep, verb), timeout=timeout)


for k in range(a.rounds):
    ep = ("n%03d" if a.no_cut else "q%03d") % (a.seed * 100 + k)
    rec = {"k": k, "ep": ep, "t0": P.now()}
    vm.start()
    vm.ssh("fsck -y /dev/rsd1a >/dev/null 2>&1; mount /dev/sd1a /pl; rm -rf /pl/q*; printf %s > /var/pl/%s.toml; sync"
           % (shlex.quote(P.cfg_text(ep)), ep))
    rec["init"] = op(ep, "init " + flags + " fn.test")[0]
    host = str(Path(FN).parent.parent / "libexec" / "fn" / "fn-host")
    # the launcher's own probe (packaging/fn): the heap figure a reclaim gets
    rec["heap"] = vm.ssh("cd /var/pl && env SBCL_USER_ARGS='--dynamic-space-size 512' %s --fn heap -- operator /var/pl/%s.toml store reclaim 2>&1; ulimit -a | grep -i data"
                         % (host, ep))[1].strip()
    of = open(out / ("%s.owner.out" % ep), "wb")
    ef = open(out / ("%s.owner.err" % ep), "wb")
    p = vm.popen("cd /var/pl && echo $$ > /var/pl/owner.pid && exec %s operator /var/pl/%s.toml run" % (FN, ep), of, ef)
    t0 = time.time()
    while b"LISTENING" not in (out / ("%s.owner.out" % ep)).read_bytes() and time.time() - t0 < 180:
        time.sleep(0.2)
    state = {"lock": threading.Lock(), "next": [0, 0], "acks": 0}
    stop = threading.Event()
    log = out / ("%s.oracle.jsonl" % ep)
    ths = [threading.Thread(target=P.poster, args=(cfg["nntp"], ep, t, state, stop, log, 7, random.Random(rng.random())),
                            daemon=True) for t in (0, 1)]
    for t in ths:
        t.start()
    t0 = time.time()
    while state["acks"] < a.target and time.time() - t0 < 900:
        time.sleep(0.5)
    stop.set()
    for t in ths:
        t.join(timeout=60)
    rec["acks"], rec["post_wall"] = state["acks"], round(time.time() - t0, 1)
    vm.ssh("kill -TERM $(cat /var/pl/owner.pid)")
    p.wait(timeout=600)
    rec["retention"] = op(ep, "retention set released-by-all-holders")[0]
    rec["status_before"] = [l for l in op(ep, "status")[1].splitlines() if l.startswith(("checkpoint", "transactions", "pack"))]
    if a.no_cut:
        t0 = time.time()
        c, so, se = op(ep, "store reclaim")
        rec["control_wall"] = round(time.time() - t0, 1)
        (out / ("%s.control.txt" % ep)).write_text(so + "\n--stderr--\n" + se)
        rec["control"] = [c, (so + se).count("reclaimed <"),
                          [l for l in (so + se).splitlines() if not l.startswith("reclaimed <")][:8]]
        vm.shutdown()
        P.append(out / "rounds.jsonl", **rec)
        print(json.dumps(rec)[:1500])
        sys.stdout.flush()
        continue
    pr = vm.popen("cd /var/pl && exec %s operator /var/pl/%s.toml store reclaim" % (FN, ep),
                  open(out / ("%s.reclaim1.txt" % ep), "wb"), subprocess.STDOUT)
    d = rng.uniform(a.lo, a.hi)
    time.sleep(d)
    rec["cut_after"], rec["reclaim_done_before_cut"] = round(d, 2), pr.poll()
    vm.kill()
    pr.wait()
    vm.start()
    rec["fsck"] = vm.ssh("fsck -y /dev/rsd1a 2>&1 | tail -3")[1][-200:]
    vm.ssh("mount /dev/sd1a /pl")
    c, so, se = op(ep, "recover")
    rec["recover"] = [c, (so + se)[-300:]]
    vm.ssh("cp -Rp /pl/%s /pl/%s.pre-rerun && sync" % (ep, ep))
    t0 = time.time()
    c, so, se = op(ep, "store reclaim")
    rec["rerun_wall"] = round(time.time() - t0, 1)
    (out / ("%s.rerun.txt" % ep)).write_text(so + "\n--stderr--\n" + se)
    rec["rerun"] = [c, (so + se).count("reclaimed <"),
                    [l for l in (so + se).splitlines() if not l.startswith("reclaimed <")][:8]]
    if c:
        rec["dmesg"] = vm.ssh("dmesg | tail -5")[1]
        vm.ssh("rm -rf /pl/%s.try2 && cp -Rp /pl/%s.pre-rerun /pl/%s.try2 && sed 's|/pl/%s\"|/pl/%s.try2\"|' /var/pl/%s.toml > /var/pl/%s.try2.toml"
               % (ep, ep, ep, ep, ep, ep, ep))
        # the same store state, rerun with a larger heap: the frozen launcher
        # in the installed tree ignores SBCL_USER_ARGS, so call the image's
        # launcher directly (libexec/fn/fn-host)
        c2, so2, se2 = vm.ssh("cd /var/pl && env SBCL_USER_ARGS='--dynamic-space-size %d' %s --fn operator /var/pl/%s.try2.toml store reclaim"
                              % (a.heap_retry, host, ep), timeout=1800)
        (out / ("%s.rerun-heap%d.txt" % (ep, a.heap_retry))).write_text(so2 + "\n--stderr--\n" + se2)
        rec["rerun_heap_retry"] = [a.heap_retry, c2, [l for l in (so2 + se2).splitlines() if not l.startswith("reclaimed <")][:6]]
    else:
        vm.ssh("rm -rf /pl/%s.pre-rerun" % ep)
    vm.shutdown()
    P.append(out / "rounds.jsonl", **rec)
    print(json.dumps(rec)[:1500])
    sys.stdout.flush()
