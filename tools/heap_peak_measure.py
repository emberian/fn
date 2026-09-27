#!/usr/bin/env python3
"""The least heap each offline operation of a store needs (PKT-686).

    python3 tools/heap_peak_measure.py --image IMAGE --work DIR --articles N
        [--octets L] [--ops reclaim,compact,recover,open] [--lo MB] [--hi MB]
        [--step MB] [--profile-flag FLAG ...] --json OUT

One scratch store, initialised through the operator verb under the power-loss
rig's small profile (lane power-loss-openbsd 9.1: the small preset's fields
with a 16-record open suffix), N articles of about L octets POSTed to one
`operator run` over NNTP at the launcher's own figure (`IMAGE --fn heap --
operator CONFIG run', books/heap-figure.lisp), then the owner is killed
(SIGKILL: the state a power cut leaves, as the rig's recover found it).  The
killed store is kept; for each operation a copy of it is made and the
operation run with SBCL's `--dynamic-space-size MB' (SBCL_USER_ARGS, which
the image launcher splices last), bisecting for the least MB at which the
operation exits 0:

  recover   `operator CONFIG recover' on the killed store
  open      `operator CONFIG run' to its LISTENING line, then SIGTERM
  compact   `operator CONFIG store compact' (after recover at a large heap)
  reclaim   `operator CONFIG retention set released-by-all-holders', then
            `store reclaim' (after recover at a large heap): compaction
            first, then the reclaiming pack

A probe that fails for any reason other than heap exhaustion stops the
search for that operation and is reported with its output.  The JSON holds
every probe (MB, exit code, seconds, whether SBCL printed `Heap exhausted',
the operation's own report lines), the store's octets on disk and its
history octets as `status' prints them, and the launcher's figure.  A
measurement: it decides nothing.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
import rep_measure as rep  # noqa: E402
from tests.native_process import wait_for_announcement  # noqa: E402

# The rig's profile (planning/evidence/power-loss-openbsd-2026-09-26.md 9.1).
RIG_FLAGS = ["--max-transactions", "16384", "--max-history-octets", "8388608",
             "--max-record-octets", "196608", "--max-article-octets", "8192",
             "--max-groups-per-article", "16", "--max-open-suffix", "16"]
EXHAUSTED = (b"Heap exhausted", b"HEAP-EXHAUSTED", b"exhausted during garbage collection")


def environment(heap_mb=None):
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    if heap_mb is not None:
        env["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % heap_mb
    else:
        env.pop("SBCL_USER_ARGS", None)
    return env


def write_config(work: Path, store: Path, port: int) -> Path:
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "control.sock"),
                      encoding="ascii")
    return config


def op(image, config, words, heap_mb, timeout=3600):
    started = time.perf_counter()
    r = subprocess.run([str(image), "--fn", "operator", str(config)] + words,
                       env=environment(heap_mb), stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout)
    return r.returncode, time.perf_counter() - started, r.stdout


def figure(image, config, words):
    r = subprocess.run([str(image), "--fn", "heap", "--", "operator", str(config)] + words,
                       env=environment(2048), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return r.stdout.decode("ascii", "replace").strip()


def status_lines(image, config, heap_mb):
    rc, _dt, out = op(image, config, ["status"], heap_mb)
    return rc, [l for l in out.decode("ascii", "replace").splitlines()
                if l.split() and l.split()[0] in ("transactions", "pack-chain", "checkpoint",
                                                  "history", "headroom", "open", "heap")
                or "open=" in l or "history" in l]


def copy_store(kept: Path, work: Path, label: str):
    trial = work / ("trial-" + label)
    if trial.exists():
        shutil.rmtree(trial)
    trial.mkdir()
    store = trial / "store"
    shutil.copytree(kept, store, symlinks=True)
    return trial, write_config(trial, store, m.free_port())


def run_open(image, config, heap_mb, timeout=3600):
    """`operator CONFIG run' to its LISTENING line (then SIGTERM), or to its
    death; the output goes to a file so a death's report is kept whole."""
    started = time.perf_counter()
    log = Path(str(config) + ".run.out")
    with open(log, "wb") as out:
        proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"],
                                env=environment(heap_mb), stdout=out, stderr=subprocess.STDOUT)
        while True:
            text = log.read_bytes()
            if b"LISTENING " in text:
                dt = time.perf_counter() - started
                proc.send_signal(signal.SIGTERM)
                proc.wait(timeout=600)
                return 0, dt, log.read_bytes()
            if proc.poll() is not None or time.perf_counter() - started > timeout:
                if proc.poll() is None:
                    proc.kill()
                proc.wait()
                return proc.returncode or -9, time.perf_counter() - started, log.read_bytes()
            time.sleep(0.2)


def probe(image, kept, work, operation, heap_mb, big_mb):
    trial, config = copy_store(kept, work, "%s-%d" % (operation, heap_mb))
    pre = []
    if operation in ("compact", "reclaim"):
        pre.append(op(image, config, ["recover"], big_mb)[0])
    if operation == "reclaim":
        pre.append(op(image, config, ["retention", "set", "released-by-all-holders"], big_mb)[0])
    if any(pre):
        return {"mb": heap_mb, "setup_failed": pre}
    if operation == "recover":
        rc, dt, out = op(image, config, ["recover"], heap_mb)
    elif operation == "open":
        rc, dt, out = run_open(image, config, heap_mb)
    elif operation == "compact":
        rc, dt, out = op(image, config, ["store", "compact"], heap_mb)
    else:
        rc, dt, out = op(image, config, ["store", "reclaim"], heap_mb)
    exhausted = any(k in out for k in EXHAUSTED)
    lines = [l for l in out.decode("ascii", "replace").splitlines()
             if not l.startswith("reclaimed <")][:12]
    shutil.rmtree(trial)
    return {"mb": heap_mb, "rc": rc, "seconds": round(dt, 2), "heap_exhausted": exhausted,
            "lines": lines}


def bisect(image, kept, work, operation, lo, hi, step, big_mb, log):
    probes = []
    top = probe(image, kept, work, operation, hi, big_mb)
    probes.append(top)
    log(operation, top)
    if top.get("rc") != 0:
        return {"least_mb": None, "probes": probes}
    good, bad = hi, lo
    while good - bad > step:
        mid = (good + bad) // 2
        p = probe(image, kept, work, operation, mid, big_mb)
        probes.append(p)
        log(operation, p)
        if p.get("rc") == 0:
            good = mid
        elif p.get("heap_exhausted"):
            bad = mid
        else:
            return {"least_mb": None, "stopped": p, "probes": probes}
    return {"least_mb": good, "probes": probes}


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--image", required=True)
    p.add_argument("--work", required=True)
    p.add_argument("--articles", type=int, required=True)
    p.add_argument("--octets", type=int, default=2048)
    p.add_argument("--ops", default="recover,open,compact,reclaim")
    p.add_argument("--lo", type=int, default=400)
    p.add_argument("--hi", type=int, default=4096)
    p.add_argument("--step", type=int, default=16)
    p.add_argument("--big", type=int, default=8192, help="MB for setup steps")
    p.add_argument("--json", required=True)
    p.add_argument("--at-figure", action="store_true",
                   help="run each operation once at the launcher's own figure for it "
                        "(`IMAGE --fn heap -- operator CONFIG VERB...') instead of bisecting")
    a = p.parse_args()
    image = Path(a.image).resolve()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    port = m.free_port()
    config = write_config(work, store, port)
    out = {"image": str(image), "launcher_sha256": m.digest(image),
           "core_sha256": m.digest(str(image) + ".core"), "articles": a.articles,
           "octets": a.octets, "flags": RIG_FLAGS,
           "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    rc, _dt, text = op(image, config, ["init"] + RIG_FLAGS + ["fn.test"], a.big)
    out["init"] = text.decode("ascii", "replace")
    if rc != 0:
        raise SystemExit("init failed rc=%d: %s" % (rc, out["init"][-400:]))
    fig = figure(image, config, ["run"])
    out["figure_run"] = fig
    out["figure_reclaim"] = figure(image, config, ["store", "reclaim"])
    fig_mb = int(fig.split("heap=", 1)[1].split()[0]) if fig.startswith("heap=") else a.big
    out["figure_mb"] = fig_mb
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"],
                            env=environment(fig_mb), stdout=subprocess.PIPE,
                            stderr=open(work / "owner.stderr", "wb"))
    wait_for_announcement(proc, b"LISTENING ")
    started = time.perf_counter()
    c = m.Conn(port)
    for i in range(a.articles):
        rep.post(c, i, a.octets)
    c.close()
    out["post_seconds"] = round(time.perf_counter() - started, 1)
    proc.kill()
    proc.wait()
    kept = work / "kept"
    shutil.copytree(store, kept, symlinks=True)
    out["store_octets"] = sum(f.stat().st_size for f in kept.rglob("*") if f.is_file())
    trial, tconfig = copy_store(kept, work, "status")
    op(image, tconfig, ["recover"], a.big)
    out["status_after_recover"] = status_lines(image, tconfig, a.big)
    shutil.rmtree(trial)
    results = {}

    def log(operation, probe_result):
        print("%s %s" % (operation, json.dumps(probe_result)), flush=True)

    words_of = {"recover": ["recover"], "open": ["run"], "compact": ["store", "compact"],
                "reclaim": ["store", "reclaim"]}
    for operation in a.ops.split(",") if a.at_figure else []:
        line = figure(image, config, words_of[operation])
        mb = int(line.split("heap=", 1)[1].split()[0]) if line.startswith("heap=") else None
        result = probe(image, kept, work, operation, mb, a.big) if mb else {"refused": line}
        result["figure_line"] = line
        results[operation] = result
        log(operation, result)
        out["operations"] = results
        Path(a.json).write_text(json.dumps(out, indent=1))
    for operation in [] if a.at_figure else a.ops.split(","):
        results[operation] = bisect(image, kept, work, operation, a.lo, a.hi, a.step, a.big, log)
        print("== %s least_mb=%s (figure %d MB)" % (operation, results[operation]["least_mb"], fig_mb),
              flush=True)
        out["operations"] = results
        Path(a.json).write_text(json.dumps(out, indent=1))
    out["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    Path(a.json).write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
