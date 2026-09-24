#!/usr/bin/env python3
"""Scratch (d24-peer): load N articles like msgid_measure, add a peer, then
profile K rounds of IHAVE <present> / CHECK <present> / CHECK <absent> on one
peer connection."""
import argparse, os, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, sys.argv.pop(1))
import msgid_measure as m

p = argparse.ArgumentParser()
p.add_argument("--image", required=True); p.add_argument("--work", required=True)
p.add_argument("--articles", type=int, required=True); p.add_argument("--rounds", type=int, default=700)
a = p.parse_args()
image = Path(a.image).resolve(); work = Path(a.work); work.mkdir(parents=True)
sp = work / "sprof"; sp.mkdir()
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
env["FN_SPROF_DIR"] = str(sp)
port = m.free_port()
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
subprocess.run([str(image), "--fn", "store", str(store), "init", "fn.test"], env=env, check=True, stdout=subprocess.PIPE)
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
err = open(work / "owner.stderr", "wb")
proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=err)
try:
    m.wait_for_announcement(proc, b"LISTENING ")
    c = m.Conn(port)
    for i in range(a.articles):
        assert c.line("POST").startswith(b"340")
        c.stream.write(m.article(i) + b".\r\n")
        assert c.stream.readline().startswith(b"240")
    c.close()
    dead = m.free_port()
    subprocess.run([str(image), "--fn", "operator", str(config), "peer", "add",
                    "t17peer", "t17peer.example.invalid", "127.0.0.1",
                    str(dead), "fn.*", "fn.*", "127.0.0.1", "true"],
                   env=env, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)
    c = m.Conn(port)
    c.line("MODE STREAM")
    (sp / "start").write_text("x"); time.sleep(0.5)
    t0 = time.perf_counter(); n = 0
    for k in range(a.rounds):
        pid = m.msgid(k % a.articles); aid = "<d24-absent-%d@example.invalid>" % k
        dt, r = c.timed("IHAVE %s" % pid); assert r.startswith(b"435"), r
        dt, r = c.timed("CHECK %s" % pid); assert r.startswith(b"438"), r
        dt, r = c.timed("CHECK %s" % aid); assert r[:3] in (b"238", b"431"), r
        n += 3
    el = time.perf_counter() - t0
    (sp / "stop").write_text("x")
    for _ in range(600):
        if (sp / "done").exists(): break
        time.sleep(0.5)
    c.close()
    print("commands", n, "seconds", el, "per_ms", 1000 * el / n)
finally:
    proc.terminate()
    try: proc.wait(timeout=60)
    except subprocess.TimeoutExpired: proc.kill()
