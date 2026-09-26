"""Time the 20,000-article chain fixture's open, and the served path at N.

    python3 fixture_open.py FIXTURE SCRATCH [K]

Run from the tree root of an image's tree (it imports pack-chain-open's
chain_fixture and tools/msgid_measure).  Copies FIXTURE/store into SCRATCH
(the fixture is never opened in place), times `store recover` (peak RSS by
/usr/bin/time -v), then `operator CONFIG run` to LISTENING (VmHWM then), then
on that owner: K greetings each on a fresh socket, GROUP, K OVER and K
ARTICLE by number spread over the group, K STAT; then the stop.  Then the
REOPEN: the store as that owner left it (with the checkpoint its first run
published) is recovered and run again, timed the same way, with K greetings
on the reopened owner.  Prints one JSON line.  Seconds are wall; every read is a command written and its reply
read on an open loopback socket.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, os.getcwd())
sys.path.insert(0, os.path.join(os.getcwd(), "tools"))
sys.path.insert(0, os.path.join(os.getcwd(), "planning/evidence/pack-chain-open-2026-09-26"))
import chain_fixture as cf  # noqa: E402
import msgid_measure as m  # noqa: E402


def multiline(c, command):
    t0 = time.perf_counter()
    first = c.line(command)
    if first[:1] != b"2":
        return time.perf_counter() - t0, first
    while True:
        row = c.readline()
        if row in (b".\r\n", b""):
            break
    return time.perf_counter() - t0, first


def main():
    fixture, scratch = Path(sys.argv[1]), Path(sys.argv[2])
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 16
    scratch.mkdir(parents=True)
    store = scratch / "store"
    import shutil
    shutil.copytree(fixture / "store", store, symlinks=True)
    out = {"fixture": str(fixture), "image_core_sha256": m.digest(str(cf.IMAGE) + ".core")}
    t = time.monotonic()
    run = subprocess.run(["/usr/bin/time", "-v", str(cf.IMAGE), "--fn", "store", str(store),
                          "recover"], cwd=cf.ROOT, env=cf.ENV, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    out["recover_s"] = round(time.monotonic() - t, 2)
    out["recover_exit"] = run.returncode
    out["recover_stdout"] = run.stdout.decode("utf-8", "replace")[-400:]
    peak = re.search(rb"Maximum resident set size \(kbytes\): (\d+)", run.stderr)
    out["recover_peak_kib"] = int(peak.group(1)) if peak else None
    usr = re.search(rb"User time \(seconds\): ([0-9.]+)", run.stderr)
    out["recover_user_s"] = float(usr.group(1)) if usr else None
    config, port = cf.write_config(scratch, store, "time")
    process, seconds, hwm = cf.start_owner(config, 3600)
    out["listening_s"] = round(seconds, 2)
    out["listening_vmhwm_kib"] = hwm
    try:
        greet = []
        for _ in range(k):
            t0 = time.perf_counter()
            c = m.Conn(port)
            greet.append(time.perf_counter() - t0)
            c.close()
        out["greeting"] = m.summary(greet)
        c = m.Conn(port)
        t0 = time.perf_counter()
        group = c.line("GROUP fn.letters")
        out["group_s"] = time.perf_counter() - t0
        out["group_reply"] = group.decode("ascii", "replace").strip()
        high = int(group.split()[3])
        numbers = [1 + (i * (high - 1)) // max(1, k - 1) for i in range(k)]
        over, art, stat = [], [], []
        for n in numbers:
            dt, r = multiline(c, "OVER %d" % n)
            assert r.startswith(b"224"), r
            over.append(dt)
        for n in numbers:
            dt, r = multiline(c, "ARTICLE %d" % n)
            assert r.startswith(b"220"), r
            art.append(dt)
        for n in numbers:
            t0 = time.perf_counter()
            r = c.line("STAT %d" % n)
            assert r.startswith(b"223"), r
            stat.append(time.perf_counter() - t0)
        c.close()
        out["over"] = m.summary(over)
        out["article"] = m.summary(art)
        out["stat"] = m.summary(stat)
    finally:
        t = time.monotonic()
        cf.stop_owner(process)
        out["stop_s"] = round(time.monotonic() - t, 2)
    t = time.monotonic()
    run = subprocess.run(["/usr/bin/time", "-v", str(cf.IMAGE), "--fn", "store", str(store),
                          "recover"], cwd=cf.ROOT, env=cf.ENV, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    out["reopen_recover_s"] = round(time.monotonic() - t, 2)
    out["reopen_recover_stdout"] = run.stdout.decode("utf-8", "replace")[-400:]
    peak = re.search(rb"Maximum resident set size \(kbytes\): (\d+)", run.stderr)
    out["reopen_recover_peak_kib"] = int(peak.group(1)) if peak else None
    process, seconds, hwm = cf.start_owner(config, 3600)
    out["reopen_listening_s"] = round(seconds, 2)
    out["reopen_listening_vmhwm_kib"] = hwm
    try:
        greet = []
        for _ in range(k):
            t0 = time.perf_counter()
            c = m.Conn(port)
            greet.append(time.perf_counter() - t0)
            c.close()
        out["reopen_greeting"] = m.summary(greet)
        c = m.Conn(port)
        t0 = time.perf_counter()
        c.line("GROUP fn.letters")
        out["reopen_group_s"] = time.perf_counter() - t0
        c.close()
    finally:
        cf.stop_owner(process)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
