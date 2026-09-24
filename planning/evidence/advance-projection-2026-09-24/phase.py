import os, subprocess, sys, time, socket
from pathlib import Path
sys.path.insert(0, sys.argv.pop(1))
import msgid_measure as m
image = Path(sys.argv[1]).resolve(); work = Path(sys.argv[2]); work.mkdir(parents=True)
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
port = m.free_port()
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
subprocess.run([str(image), "--fn", "store", str(store), "init", "fn.test"], env=env, check=True, stdout=subprocess.PIPE)
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=open(work / "err", "wb"))
try:
    m.wait_for_announcement(proc, b"LISTENING ")
    c = m.Conn(port)
    rows = []
    for i in range(24):
        t0 = time.perf_counter(); r = c.line("POST"); t1 = time.perf_counter()
        c.stream.write(m.article(i) + b".\r\n"); r2 = c.readline(); t2 = time.perf_counter()
        rows.append(((t1 - t0) * 1000, (t2 - t1) * 1000))
        # also a raw recv-level look at 240 arrival: none
    c.close()
    for a, b in rows[-8:]: print("POST->340 %.2f ms  body->240 %.2f ms" % (a, b))
finally:
    proc.terminate(); proc.wait(timeout=60)
