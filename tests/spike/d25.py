#!/usr/bin/env python3
"""spike-storage: resend a reclaimed article (expect duplicate) and a changed one (expect conflict).
usage: d25.py TREE IMAGE WORK I"""
import os, signal, subprocess, sys
tree, image, work, i = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
sys.path.insert(0, tree + "/tools"); import msgid_measure as m
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ramp_article import article
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"
cfg = os.path.join(work, "fn.toml")
port = int([l for l in open(cfg).read().splitlines() if l.startswith("port")][0].split("=")[1])
p = subprocess.Popen([image, "--fn", "operator", cfg, "run"], env=env, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
m.wait_for_announcement(p, b"LISTENING ", timeout=3600)
c = m.Conn(port)
for tag, body in (("same", article(i)), ("changed", article(i).replace(b"xxxx", b"yyyy", 1))):
    assert c.line("POST").startswith(b"340")
    c.stream.write(body + b".\r\n")
    print("resend-%s %s" % (tag, c.readline().decode().strip()))
r = c.line("ARTICLE %s" % m.msgid(i)); print("article", r.decode().strip())
lines = []
while True:
    l = c.readline()
    if l in (b".\r\n", b""): break
    lines.append(l)
print("article-lines", len(lines), [l.decode().strip() for l in lines if l.startswith(b"FN-Reclaimed")])
r = c.line("GROUP fn.test"); print("group", r.decode().strip())
c.close(); p.send_signal(signal.SIGTERM); p.wait(timeout=600)
