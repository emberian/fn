"""greet.py STORE_SRC SCRATCH K -- run from an image tree root: copy STORE_SRC, start the owner
(chain_fixture.start_owner: operator CONFIG run to LISTENING), K greetings each on a fresh socket, stop."""
import json, os, shutil, sys, time
from pathlib import Path
sys.path.insert(0, os.getcwd()); sys.path.insert(0, os.path.join(os.getcwd(), "tools"))
sys.path.insert(0, os.path.join(os.getcwd(), "planning/evidence/pack-chain-open-2026-09-26"))
import chain_fixture as cf, msgid_measure as m
src, scratch, k = Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3])
scratch.mkdir(parents=True)
store = scratch / "store"; shutil.copytree(src, store, symlinks=True)
out = {"store": str(src), "image_core_sha256": m.digest(str(cf.IMAGE) + ".core")}
config, port = cf.write_config(scratch, store, "greet")
import subprocess, select
started = time.monotonic()
proc = subprocess.Popen([str(cf.IMAGE), "--fn", "operator", str(config), "run"], cwd=cf.ROOT, env=cf.ENV,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
buf = b""; lines = []
while True:
    if b"LISTENING " in buf: break
    if not select.select([proc.stdout], [], [], 3600)[0]: raise SystemExit("no LISTENING")
    ch = os.read(proc.stdout.fileno(), 4096)
    if not ch: raise SystemExit("owner ended: " + proc.stderr.read()[-3000:].decode("utf-8", "replace"))
    buf += ch
seconds = time.monotonic() - started
out["owner_stdout_before_listening"] = buf.decode("utf-8", "replace")[-600:]
out["listening_s"] = round(seconds, 2)
try:
    for rnd in ("warm", "measured"):
        g = []
        for _ in range(k):
            t0 = time.perf_counter(); c = m.Conn(port); g.append(time.perf_counter() - t0); c.close()
        out["greeting_" + rnd] = m.summary(g)
finally:
    cf.stop_owner(proc)
err = (scratch / "greet.stderr") 
print(json.dumps(out))
