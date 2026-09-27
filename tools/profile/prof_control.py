#!/usr/bin/env python3
"""Profile the owner's live control quanta (lane control-quanta, 2026-09-27).

    python3 prof_control.py IMAGE STORE_DIR OUT_DIR [ROUNDS]

IMAGE is a profiling image (tools/profile/build_native_profile.sh).  STORE_DIR
is copied to OUT_DIR/store and served by one owner with FN_PROF_OUT set; for
ROUNDS rounds (default 3) each of `group create' and `control grant' runs
once under the CPU profiler and once under the allocation profiler; each
report lands in OUT_DIR/prof.N.txt, and OUT_DIR/prof.json lists every op
with its client wall time and report file.  Idle: nothing else talks to the
owner.
"""
import json, os, shutil, socket, subprocess, sys, time
from pathlib import Path

image, src, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 3
if out.exists():
    shutil.rmtree(out)
out.mkdir(parents=True)
shutil.copytree(src, out / "store", symlinks=True)
for junk in ("writer.lock",):
    (out / "store" / junk).unlink(missing_ok=True)
s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
cfg = out / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
               '[log]\npath = "%s"\n' % (out / "store", port, out / "control.sock", out / "service.log"))
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
env.pop("ACL2_SYSTEM_BOOKS", None)
prof = str(out / "prof")
owner = subprocess.Popen([str(image), "--fn", "operator", str(cfg), "run"], env=dict(env, FN_PROF_OUT=prof),
                         stdout=subprocess.PIPE, stderr=open(out / "owner.stderr", "wb"))
t0 = time.time()
line = b""
while b"LISTENING" not in line:
    line = owner.stdout.readline()
    if not line and owner.poll() is not None:
        sys.exit("owner exited %s" % owner.returncode)
open_s = time.time() - t0
records, n = [], [0]


def native(*words):
    t = time.perf_counter()
    r = subprocess.run([str(image), "--fn", *map(str, words)], env=env, capture_output=True, timeout=900)
    return r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace").strip()[-200:], time.perf_counter() - t


def profiled(kind, mode, *words):
    Path(prof + ".start").write_text(mode + "\n")
    while Path(prof + ".start").exists():
        time.sleep(0.02)
    rc, tail, dt = native(*words)
    Path(prof + ".stop").write_text("")
    n[0] += 1
    rep = Path("%s.%d.txt" % (prof, n[0]))
    while not rep.exists():
        time.sleep(0.05)
    head = rep.read_text().splitlines()[0]
    records.append({"kind": kind, "mode": mode, "rc": rc, "client_s": round(dt, 3), "report": rep.name,
                    "head": head, "tail": tail})
    print(kind, mode, rc, "%.3f s" % dt, head, flush=True)


try:
    for i in range(rounds):
        for mode in ("cpu", "alloc"):
            g = "fn.prof%d%s" % (i, mode)
            profiled("group-create", mode, "operator", cfg, "group", "create", g)
            profiled("control-grant", mode, "operator", cfg, "control", "grant", (bytes([0xA1 + i]) * 32).hex(),
                     "keys", "fn.test")
finally:
    owner.terminate()
    try:
        owner.wait(60)
    except subprocess.TimeoutExpired:
        owner.kill()
(out / "prof.json").write_text(json.dumps({"image": str(image), "source": str(src), "open_s": open_s,
                                           "ops": records}, indent=1))
