#!/usr/bin/env python3
"""Scratch (rep-octets lane): load N articles of a given payload size through
one NNTP connection of a native image, time every POST, sample RSS at a
quarter and at the end, and optionally profile the last K POSTs through the
image's sprof hook (FN_SPROF_DIR; FN_DPROF=names for call counts).

    load_sized.py TOOLS --image IMG --work DIR --articles N --payload-octets P \
        [--stats K] --json OUT
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, sys.argv.pop(1))
import msgid_measure as m

p = argparse.ArgumentParser()
p.add_argument("--image", required=True); p.add_argument("--work", required=True)
p.add_argument("--articles", type=int, required=True)
p.add_argument("--payload-octets", type=int, default=160)
p.add_argument("--stats", type=int, default=0)
p.add_argument("--json", required=True)
a = p.parse_args()
image = Path(a.image).resolve(); work = Path(a.work); work.mkdir(parents=True)
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
sp = None
if a.stats:
    sp = work / "sprof"; sp.mkdir(); env["FN_SPROF_DIR"] = str(sp)
port = m.free_port()
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
subprocess.run([str(image), "--fn", "store", str(store), "init", "fn.test"], env=env, check=True, stdout=subprocess.PIPE)
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
err = open(work / "owner.stderr", "wb")
proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=err)

HEAD = ("From: rep@example.invalid\r\nNewsgroups: fn.test\r\nSubject: rep %d\r\n"
        "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n")
LINE = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ" [:78] + b"\r\n"

def article(i):
    head = (HEAD % (i, m.msgid(i))).encode("ascii")
    need = max(0, a.payload_octets - len(head))
    body = LINE * (need // len(LINE))
    rest = need - len(body)
    if rest >= 2:
        body += LINE[:rest - 2] + b"\r\n"
    return head + body

out = {"image": str(image), "launcher_sha256": m.digest(image), "core_sha256": m.digest(str(image) + ".core"),
       "articles": a.articles, "payload_octets": a.payload_octets, "article_octets": len(article(0)), "stats": a.stats}
try:
    m.wait_for_announcement(proc, b"LISTENING ")
    c = m.Conn(port)
    load = []
    q = max(1, a.articles // 4)
    started_all = time.perf_counter()
    def post(i):
        t0 = time.perf_counter()
        r = c.line("POST")
        if not r.startswith(b"340"): raise SystemExit("POST %d: %r" % (i, r))
        c.stream.write(article(i) + b".\r\n")
        r = c.readline()
        if not r.startswith(b"240"): raise SystemExit("POST %d body: %r" % (i, r))
        load.append(time.perf_counter() - t0)
    window = a.articles - a.stats if a.stats else a.articles
    for i in range(window):
        post(i)
        if i + 1 == q:
            out["rss_at_quarter_kib"] = m.rss_kib(proc.pid)
    if a.stats:
        (sp / "start").write_text("x"); time.sleep(0.5)
        t0 = time.perf_counter()
        for i in range(window, a.articles):
            post(i)
        out["stats_seconds"] = time.perf_counter() - t0
        (sp / "stop").write_text("x")
        for _ in range(1200):
            if (sp / "done").exists(): break
            time.sleep(0.5)
    out["load_seconds"] = time.perf_counter() - started_all
    c.close()
    out["post_first_quarter"] = m.summary(load[:q])
    out["post_last_quarter"] = m.summary(load[-q:])
    out["rss_after_load_kib"] = m.rss_kib(proc.pid)
    if out.get("rss_at_quarter_kib") and out["rss_after_load_kib"]:
        out["rss_slope_kib_per_article"] = (out["rss_after_load_kib"] - out["rss_at_quarter_kib"]) / max(1, a.articles - q)
    if a.stats and (sp / "dprof.txt").exists():
        out["dprof"] = (sp / "dprof.txt").read_text()
finally:
    proc.terminate()
    try: proc.wait(timeout=60)
    except subprocess.TimeoutExpired: proc.kill()
Path(a.json).write_text(json.dumps(out, indent=1))
print("articles", a.articles, "payload", a.payload_octets, "load_s", round(out.get("load_seconds", 0), 3),
      "last_q_median_ms", round(out["post_last_quarter"]["median_ms"], 3) if "post_last_quarter" in out else None,
      "rss_kib", out.get("rss_after_load_kib"), "slope_kib", round(out.get("rss_slope_kib_per_article", 0), 1))
