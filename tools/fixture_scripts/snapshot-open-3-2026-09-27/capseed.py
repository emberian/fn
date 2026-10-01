#!/usr/bin/env python3
"""Set a seed store's configured capacity: capseed.py IMAGE STORE UNITS.

The synthesized fixtures (tools/fixtures.py syn100k-2k, syn1m-2k;
tools/synth_log_store.py) renumber a POSTed seed's articles to N records; a
2 KiB article is charged 2 units, so the seed's configuration must hold
2 N units.  This starts the seed's owner once on loopback (a config file
beside the store), sends `operator CONFIG capacity UNITS`, and stops it: the
configuration record lands at the txid after the seed's history, which the
renumbered history ties (configuration first, as the replay orders a tie).
Exit 0 when the operator accepted the capacity, else 1."""
import os, socket, subprocess, sys, time
from pathlib import Path

image, store, units = sys.argv[1], Path(sys.argv[2]), sys.argv[3]
work = store.parent / (store.name + ".capseed")
work.mkdir(exist_ok=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
env.pop("ACL2_SYSTEM_BOOKS", None)
s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
cfg = work / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
               '[control]\npath = "%s"\n' % (store, port, work / "control.sock"))
p = subprocess.Popen([image, "--fn", "operator", str(cfg), "run"], env=env,
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
line = b""
while b"LISTENING" not in line:
    line = p.stdout.readline()
    if not line:
        print("capseed: the owner exited before LISTENING"); sys.exit(1)
r = subprocess.run([image, "--fn", "operator", str(cfg), "capacity", units], env=env,
                   capture_output=True, text=True)
print("capseed: capacity %s exit %d: %s %s" % (units, r.returncode, r.stdout.strip()[-300:],
                                               r.stderr.strip()[-300:]))
time.sleep(1)
p.terminate(); p.wait(timeout=120)
sys.exit(0 if r.returncode == 0 and "ACCEPTED" in (r.stdout + r.stderr) else 1)
