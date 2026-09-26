import os, sys, time, subprocess
from pathlib import Path
T = Path(sys.argv[1]); work = Path(sys.argv[2]); out = Path(sys.argv[3]); base = int(sys.argv[4]); k = int(sys.argv[5])
sys.path.insert(0, str(T / "tools")); sys.path.insert(0, str(T))
import rep_measure as r
import msgid_measure as m
out.mkdir(parents=True, exist_ok=True)
for n in ("start", "stop", "done", "flat.txt", "graph.txt"):
    try: (out / n).unlink()
    except FileNotFoundError: pass
port = m.free_port()
config = work / "fn.toml"
text = config.read_text().splitlines()
config.write_text("\n".join(("port = %d" % port) if l.startswith("port =") else l for l in text) + "\n")
env = dict(os.environ, FN_PROF_LOAD=str(Path(__file__).parent / "alloc.lisp"), FN_ALLOC_DIR=str(out))
proc, t, err = r.start_owner(T / "build/fn-host-developer-prof", config, env, out / "owner.stderr")
c = m.Conn(port); c.readline() if False else None
times = []
(out / "start").write_text("1")
time.sleep(0.5)
for i in range(k):
    times.append(r.post(c, base + i, 2048))
(out / "stop").write_text("1")
while not (out / "done").exists(): time.sleep(0.1)
print("posts", k, "median_ms", sorted(times)[k // 2] * 1000)
c.close(); r.stop_owner(proc, err)
