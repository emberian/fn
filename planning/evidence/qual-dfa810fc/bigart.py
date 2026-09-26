#!/usr/bin/env python3
"""qual-dfa810fc: the served ARTICLE of a large article on a 4 MiB profile (bounds_join's red).
For each image and size: a fresh store (`init --max-article-octets 4194304 fn.test`), one owner,
POST the article (tests.test_native_bounds_join.article), ARTICLE it back, then STAT on a new
connection; the owner's exit and last stderr lines.  Usage: bigart.py WORK IMAGE[=label] ... -- SIZES"""
import os, signal, socket, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, os.getcwd())
from tests.test_native_bounds_join import article, NntpClient
work = Path(sys.argv[1]); work.mkdir(parents=True, exist_ok=False)
i = sys.argv.index("--"); images = sys.argv[2:i]; sizes = [int(x) for x in sys.argv[i + 1:]]
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for k in [k for k in env if k.startswith("FN_NATIVE_")]:
    env.pop(k)
def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0)); return s.getsockname()[1]
for spec in images:
    img, _, label = spec.partition("=")
    for n in sizes:
        d = work / ("%s-%d" % (label, n)); d.mkdir()
        port = free_port()
        cfg = d / "fn.toml"
        cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (d / "store", port, d / "c.sock"))
        r = subprocess.run([img, "--fn", "operator", str(cfg), "init", "--max-article-octets", "4194304", "fn.test"], env=env, capture_output=True)
        err = open(d / "owner.err", "wb")
        o = subprocess.Popen([img, "--fn", "operator", str(cfg), "run"], env=env, stdout=subprocess.PIPE, stderr=err)
        while not o.stdout.readline().startswith(b"LISTENING"):
            pass
        mid = "<big-%d@example.invalid>" % n
        data = article(mid, n)
        c = NntpClient(port)
        t0 = time.time(); rep = c.post(data); tp = time.time() - t0
        try:
            t0 = time.time(); st, stored = c.article(mid); ta = time.time() - t0
            ok = stored is not None and stored.endswith(data.split(b"\r\n\r\n", 1)[1])
        except Exception as e:
            st, ok, ta = ("EXC %r" % e).encode(), False, time.time() - t0
        try:
            c.close()
        except Exception:
            pass
        time.sleep(0.5)
        alive = o.poll() is None
        if alive:
            o.send_signal(signal.SIGTERM)
        try:
            o.wait(60)
        except subprocess.TimeoutExpired:
            o.kill(); o.wait()
        tail = (d / "owner.err").read_bytes().decode("utf-8", "replace").strip().splitlines()[-3:]
        print("%-9s size=%-8d post=%s (%.2fs) article=%s identical=%s (%.2fs) owner-alive-after=%s exit=%s | %s" % (
            label, n, rep[:24], tp, st.decode("ascii", "replace").strip()[:30], ok, ta, alive, o.returncode, " / ".join(tail)[:220]), flush=True)
