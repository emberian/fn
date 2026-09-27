#!/usr/bin/env python3
"""Idle control-quantum timing (lane control-quanta, 2026-09-27; SCN-181).

    python3 control_quanta.py IMAGE STORE_DIR OUT_DIR [ROUNDS]

Copies STORE_DIR to OUT_DIR/store, serves it with one owner (IMAGE, a
developer image) and, with nothing else talking to it, runs ROUNDS (default
3) of `operator group create' then `operator control grant'.  For each op it
records the client's wall time and exit code, then polls `operator health'
until one answers: HOLD_S, from the op's start to that answer, bounds the
owner's control quantum even when the op's own 10 s client deadline expired
(exit 3); the health page's control row (hold-max-ms) is kept beside it.
Writes OUT_DIR/quanta.json.
"""
import json, os, re, shutil, socket, subprocess, sys, time
from pathlib import Path

image, src, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 3
if out.exists():
    shutil.rmtree(out)
out.mkdir(parents=True)
shutil.copytree(src, out / "store", symlinks=True)
(out / "store" / "writer.lock").unlink(missing_ok=True)
s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
cfg = out / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
               '[log]\npath = "%s"\n' % (out / "store", port, out / "control.sock", out / "service.log"))
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
env.pop("ACL2_SYSTEM_BOOKS", None)
owner = subprocess.Popen([str(image), "--fn", "operator", str(cfg), "run"], env=env,
                         stdout=subprocess.PIPE, stderr=open(out / "owner.stderr", "wb"))
t0 = time.time()
line = b""
while b"LISTENING" not in line:
    line = owner.stdout.readline()
    if not line and owner.poll() is not None:
        sys.exit("owner exited %s" % owner.returncode)
open_s = time.time() - t0


def native(*words):
    t = time.perf_counter()
    r = subprocess.run([str(image), "--fn", *map(str, words)], env=env, capture_output=True, timeout=900)
    return r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace"), time.perf_counter() - t


def control_row(text):
    for ln in text.splitlines():
        if "control" in ln and "hold-max-ms" in ln:
            return ln.strip()
    return None


ops = []
try:
    rc, text, dt = native("operator", cfg, "health")
    baseline = {"rc": rc, "client_s": round(dt, 3), "control_row": control_row(text)}
    for i in range(rounds):
        for kind, words in (("group-create", ("group", "create", "fn.cq%d" % i)),
                            ("control-grant", ("control", "grant", (bytes([0xA1 + i]) * 32).hex(),
                                               "keys", "fn.test"))):
            start = time.perf_counter()
            rc, text, dt = native("operator", cfg, *words)
            polls = 0
            while True:
                polls += 1
                hrc, htext, _ = native("operator", cfg, "health")
                if hrc == 0:
                    break
            hold = time.perf_counter() - start
            rec = {"kind": kind, "rc": rc, "client_s": round(dt, 3), "hold_s": round(hold, 3),
                   "health_polls": polls, "tail": text.strip()[-120:], "control_row": control_row(htext)}
            ops.append(rec)
            print(json.dumps(rec), flush=True)
finally:
    owner.terminate()
    try:
        owner.wait(120)
    except subprocess.TimeoutExpired:
        owner.kill()
(out / "quanta.json").write_text(json.dumps({"image": str(image), "source": str(src), "open_s": open_s,
                                             "baseline_health": baseline, "ops": ops}, indent=1))
