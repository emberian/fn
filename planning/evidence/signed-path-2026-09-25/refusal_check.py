#!/usr/bin/env python3
"""Scratch (signed-path): a signed POST whose composite is past the profile's R.
usage: refusal_check.py TREE IMAGE WORK KEYDIR CARRIED..."""
import os, socket, subprocess, sys, time
from pathlib import Path
tree, image, work, keys = Path(sys.argv[1]), Path(sys.argv[2]).resolve(), Path(sys.argv[3]), Path(sys.argv[4])
carried = [Path(x) for x in sys.argv[5:]]
sys.path.insert(0, str(tree))
from tests.test_fn_verify import dot_stuff
from tests.native_process import wait_for_announcement, stop_and_diagnostics
work.mkdir(parents=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
def fn(*args):
    r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=tree, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=1800)
    if r.returncode: raise SystemExit("{} -> {} {}".format(args[:2], r.returncode, r.stderr.decode()[-1500:]))
    return r.stdout.decode()
with socket.socket() as probe:
    probe.bind(("127.0.0.1", 0)); port = probe.getsockname()[1]
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                  % (store, port, control), encoding="ascii")
flags = ["--max-article-octets", "220000", "--max-groups-per-article", "1",
         "--max-group-name-octets", "64", "--max-record-octets", "240000"]
fn("operator", config, "init", *flags, "fn.test")
print("PROFILE", " ".join(w for w in fn("operator", config, "status").split() if w.startswith("max-")), flush=True)
owner = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], cwd=tree, env=env,
                         stdout=subprocess.PIPE, stderr=open(work / "owner.stderr", "wb"))
def cmd(f, line):
    f.write(line + b"\r\n"); return f.readline().decode().strip()
try:
    wait_for_announcement(owner, b"LISTENING ")
    fn("hybrid-enroll", control, "1", keys / "principal.bin", keys / "ed-public.bin", keys / "ml-public.pem")
    for c in carried:
        octets = c.read_bytes()
        s = socket.create_connection(("127.0.0.1", port), timeout=1800); f = s.makefile("rwb", buffering=0)
        f.readline(); assert cmd(f, b"POST").startswith("340")
        t0 = time.perf_counter(); f.write(dot_stuff(octets) + b".\r\n"); reply = f.readline().decode().strip()
        print("POST {} octets={} wall={:.2f}s reply={}".format(c.name, len(octets), time.perf_counter() - t0, reply), flush=True)
        print("DATE after:", cmd(f, b"DATE"), flush=True); s.close()
    print("owner alive:", owner.poll() is None)
finally:
    print(stop_and_diagnostics(owner, timeout=120)[-300:])
