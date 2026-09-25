#!/usr/bin/env python3
"""spike-storage: POST ramp.  usage: ramp.py TREE IMAGE WORK N STEP OUTJSONL [BODY_OCTETS]
One owner, POSTs 2 KiB articles, logs wall per STEP posts and owner RSS; stops at N or when a step exceeds a deadline."""
import json, os, signal, subprocess, sys, time
from pathlib import Path
tree, image, work, N, step, outp = sys.argv[1], sys.argv[2], Path(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
body = int(sys.argv[7]) if len(sys.argv) > 7 else 2048
sys.path.insert(0, tree + "/tools"); import msgid_measure as m
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
out = open(outp, "a")
def log(rec): out.write(json.dumps(rec) + "\n"); out.flush()
def article(i):
    head = ("From: s@example.invalid\r\nNewsgroups: fn.test\r\nSubject: spike %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n" % (i, m.msgid(i))).encode()
    line = b"x" * 62 + b"\r\n"
    return head + line * max(1, (body - len(head)) // 64)
work.mkdir(parents=True, exist_ok=True)
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
first = int(os.environ.get("RAMP_FIRST", "0"))
if not store.exists():
    port = m.free_port()
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, port, control))
    r = subprocess.run([image, "--fn", "operator", str(config), "init", "--max-transactions", "1000000", "fn.test"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log({"init": r.returncode, "out": r.stdout.decode()[-400:]})
    assert r.returncode == 0
port = int([l for l in config.read_text().splitlines() if l.startswith("port")][0].split("=")[1])
p = subprocess.Popen([image, "--fn", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
t0 = time.perf_counter(); m.wait_for_announcement(p, b"LISTENING ", timeout=86400)
log({"tag": "owner-open", "first": first, "open_s": round(time.perf_counter() - t0, 3), "rss_kib": m.rss_kib(p.pid)})
c = m.Conn(port); i = first; deadline = float(os.environ.get("RAMP_STEP_DEADLINE", "3600"))
try:
    while i < N:
        ts = time.perf_counter(); worst = 0.0
        for j in range(i, min(N, i + step)):
            a = time.perf_counter()
            assert c.line("POST").startswith(b"340")
            c.stream.write(article(j) + b".\r\n")
            rr = c.readline()
            if not rr.startswith(b"240"): raise SystemExit("POST %d: %r" % (j, rr))
            worst = max(worst, time.perf_counter() - a)
        w = time.perf_counter() - ts; i = min(N, i + step)
        log({"tag": "step", "n": i, "wall_s": round(w, 3), "per_post_ms": round(1000 * w / step, 3), "worst_ms": round(1000 * worst, 1), "rss_kib": m.rss_kib(p.pid)})
        if w > deadline: log({"tag": "stop", "reason": "step deadline"}); break
finally:
    c.close(); p.send_signal(signal.SIGTERM)
    try: p.wait(timeout=3600)
    except Exception: p.kill()
    du = subprocess.run(["du", "-sk", str(store)], stdout=subprocess.PIPE).stdout.decode().split()[0]
    log({"tag": "done", "n": i, "store_kib": int(du)})
