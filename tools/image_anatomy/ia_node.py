#!/usr/bin/env python3
"""Which pages of a native image a running node touches (lane image-anatomy,
2026-09-26).  Runs ON hbox (Linux /proc).  A measurement only: it decides
nothing a node does.

    ia_node.py run IMAGE WORK --posts N --out DIR [--heap MB]
        a fresh scale-profile store (as tools/runtime_image/node_measure.py);
        the owner started; a residency snapshot (DIR/<stage>.pages) at
        LISTENING+1 s, after 1 POST and after N POSTs of 2,048 octets; VmRSS
        per stage in DIR/run.json.
    ia_node.py stage IMAGE WORK --eval FORM --label L --out DIR [--heap MB]
        the image's own exec line with its `--eval (acl2::sbcl-restart)'
        replaced by FORM (for example "(sleep 30)"), snapshot after 6 s.

A snapshot lists every mapping of /proc/PID/maps and, from
/proc/PID/pagemap (bit 63: present), the resident page ranges inside it:
    M <start> <end> <perms> <path>
    F <first-page-address> <end-address>   resident, clean file page
    R <first-page-address> <end-address>   resident, private (written/anonymous)
Addresses are decimal.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shlex
import struct
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "runtime_image"))
import msgid_measure as m  # noqa: E402
import rep_measure as r    # noqa: E402

PAGE = 4096
OCTETS = 2048
SCALE = ["--profile", "scale", "--max-transactions", "1048576", "--max-article-octets", "4096"]


def snapshot(pid, path):
    maps = Path("/proc/%d/maps" % pid).read_text().splitlines()
    out = []
    total = 0
    with open("/proc/%d/pagemap" % pid, "rb") as pm:
        for line in maps:
            parts = line.split(None, 5)
            lo, hi = (int(x, 16) for x in parts[0].split("-"))
            name = parts[5] if len(parts) > 5 else ""
            out.append("M %d %d %s %s" % (lo, hi, parts[1], name))
            if name == "[vsyscall]":
                continue
            n = (hi - lo) // PAGE
            try:
                pm.seek((lo // PAGE) * 8)
                data = pm.read(n * 8)
            except OSError:
                continue
            # kind 0: absent; 1: present and still the file's page (read,
            # never written: clean, shareable); 2: present and private
            # (written, copied on write, or anonymous).
            run_start, run_kind = None, 0
            count = len(data) // 8
            for i in range(count + 1):
                if i < count:
                    e = struct.unpack_from("<Q", data, i * 8)[0]
                    kind = 0 if not (e >> 63) else (1 if (e >> 61) & 1 else 2)
                else:
                    kind = 0
                if kind != run_kind:
                    if run_kind:
                        out.append("%s %d %d" % ("F" if run_kind == 1 else "R",
                                                 lo + run_start * PAGE, lo + i * PAGE))
                        total += i - run_start
                    run_start, run_kind = i, kind
    Path(path).write_text("\n".join(out) + "\n")
    return total * PAGE // 1024


def status(pid):
    return {"rss_kib": r.status_kib(pid, "VmRSS"), "hwm_kib": r.status_kib(pid, "VmHWM"),
            "vsz_kib": r.status_kib(pid, "VmSize"), "threads": r.status_kib(pid, "Threads")}


RUNTIME_EXTRA = ""


def env_for(heap):
    env = dict(os.environ)
    if heap:
        env["SBCL_USER_ARGS"] = ("--dynamic-space-size %dMB %s" % (heap, RUNTIME_EXTRA)).strip()
    return env


def fresh(image, work, env):
    work.mkdir(parents=True, exist_ok=True)
    for p in ("store", "c.sock"):
        subprocess.run(["rm", "-rf", str(work / p)], check=True)
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"),
                      encoding="ascii")
    res = subprocess.run([str(image), "--fn", "operator", str(config), "init"] + SCALE
                         + ["fn.letters", "fn.test"], env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if res.returncode:
        raise RuntimeError("init rc=%d %r" % (res.returncode, res.stdout[-300:]))
    return config, port


def run(a):
    image, work, out = Path(a.image), Path(a.work), Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    env = env_for(a.heap)
    config, port = fresh(image, work, env)
    doc = {"image": str(image), "heap_mb": a.heap, "posts": a.posts}
    proc, start_s, err = r.start_owner(image, config, env, work / "owner.stderr", timeout=600)
    try:
        doc["start_s"] = round(start_s, 3)
        time.sleep(1.0)
        doc["start"] = status(proc.pid)
        doc["start"]["paged_kib"] = snapshot(proc.pid, out / "start.pages")
        c = m.Conn(port)
        r.post(c, 0, OCTETS)
        doc["after_1"] = status(proc.pid)
        doc["after_1"]["paged_kib"] = snapshot(proc.pid, out / "after_1.pages")
        t0 = time.perf_counter()
        for i in range(1, a.posts):
            r.post(c, i, OCTETS)
        doc["post_s"] = round(time.perf_counter() - t0, 3)
        c.close()
        c = m.Conn(port)
        for i in range(0, a.posts, max(1, a.posts // 50)):
            _, reply, _ = r.timed_multiline(c, "ARTICLE %s" % m.msgid(i))
            if not reply.startswith(b"220"):
                raise RuntimeError("ARTICLE %d: %r" % (i, reply))
        c.close()
        key = "after_%d" % a.posts
        doc[key] = status(proc.pid)
        doc[key]["paged_kib"] = snapshot(proc.pid, out / (key + ".pages"))
    finally:
        r.stop_owner(proc, err)
    doc["owner_rc"] = proc.returncode
    (out / "run.json").write_text(json.dumps(doc, sort_keys=True) + "\n")
    return doc


def stage(a):
    image, out = Path(a.image), Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    text = image.read_text()
    line = next(l for l in text.splitlines() if l.startswith("exec "))
    line = line.replace("${SBCL_USER_ARGS}", env_for(a.heap).get("SBCL_USER_ARGS", ""))
    words = shlex.split(line)[1:]
    i = words.index("--eval")
    words[i + 1] = a.eval
    words = words[:words.index("--end-toplevel-options")] if "--end-toplevel-options" in words else words
    env = dict(os.environ)
    home = re.search(r"SBCL_HOME='([^']*)'", text)
    if home:
        env["SBCL_HOME"] = home.group(1)
    proc = subprocess.Popen(words, env=env, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL)
    try:
        time.sleep(a.wait)
        doc = {"label": a.label, "eval": a.eval, "alive": proc.poll() is None}
        doc.update(status(proc.pid))
        doc["paged_kib"] = snapshot(proc.pid, out / (a.label + ".pages"))
    finally:
        proc.kill()
        proc.wait()
    (out / (a.label + ".json")).write_text(json.dumps(doc, sort_keys=True) + "\n")
    return doc


def main():
    import argparse
    p = argparse.ArgumentParser()
    s = p.add_subparsers(dest="cmd", required=True)
    q = s.add_parser("run")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--posts", type=int, default=1000)
    q.add_argument("--heap", type=int, default=1024)
    q.add_argument("--out", required=True)
    q = s.add_parser("stage")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--eval", required=True)
    q.add_argument("--label", required=True)
    q.add_argument("--heap", type=int, default=1024)
    q.add_argument("--wait", type=float, default=6.0)
    q.add_argument("--out", required=True)
    a = p.parse_args()
    global RUNTIME_EXTRA
    RUNTIME_EXTRA = os.environ.get("IA_RUNTIME_EXTRA", "")
    print(json.dumps({"run": run, "stage": stage}[a.cmd](a), sort_keys=True))


if __name__ == "__main__":
    main()
