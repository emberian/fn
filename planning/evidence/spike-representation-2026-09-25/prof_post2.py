#!/usr/bin/env python3
"""Scratch (spike-representation): load N articles of L octets like rep_measure, then profile the last K POSTs with the sprof hook."""
import argparse, os, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, sys.argv.pop(1))
import msgid_measure as m
import rep_measure as rm

p = argparse.ArgumentParser()
p.add_argument("--image", required=True); p.add_argument("--work", required=True)
p.add_argument("--articles", type=int, required=True); p.add_argument("--stats", type=int, default=48)
p.add_argument("--octets", type=int, default=0)
a = p.parse_args()
image = Path(a.image).resolve(); work = Path(a.work); work.mkdir(parents=True)
sp = work / "sprof"; sp.mkdir()
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
env["FN_SPROF_DIR"] = str(sp)
port = m.free_port()
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
init = [str(image), "--fn", "operator", str(config), "init", "--profile", "default",
        "--max-article-octets", str(max(65536, a.octets * 2)), "fn.test"]
r = subprocess.run(init, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT); assert r.returncode == 0, r.stdout[-300:]
err = open(work / "owner.stderr", "wb")
proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=err)
try:
    m.wait_for_announcement(proc, b"LISTENING ", timeout=3600)
    c = m.Conn(port)
    def post(i):
        assert c.line("POST").startswith(b"340")
        c.stream.write(rm.article(i, a.octets) + b".\r\n")
        assert c.stream.readline().startswith(b"240")
    for i in range(a.articles - a.stats):
        post(i)
    (sp / "start").write_text("x"); time.sleep(0.5)
    t0 = time.perf_counter()
    for i in range(a.articles - a.stats, a.articles):
        post(i)
    el = time.perf_counter() - t0
    (sp / "stop").write_text("x")
    for _ in range(1200):
        if (sp / "done").exists(): break
        time.sleep(0.5)
    c.close()
    print("stats", a.stats, "seconds", el, "per_ms", 1000 * el / a.stats)
finally:
    proc.terminate()
    try: proc.wait(timeout=120)
    except subprocess.TimeoutExpired: proc.kill()
