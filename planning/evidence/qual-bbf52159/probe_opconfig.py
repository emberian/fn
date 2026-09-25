"""qual-bbf52159: operator-config on the production image (show, mission, SIGHUP log reopen).
Only the PIDs started here are signalled."""
import os, signal, socket, subprocess, time
I = "/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host"
D = "/tank/fn/scratch/qual-bbf52159/probe-opconfig"
subprocess.run(["rm", "-rf", D]); os.makedirs(D)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
def port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0)); return s.getsockname()[1]
def run(name, *argv, stdin=None):
    r = subprocess.run([I, "--fn", *argv], env=env, capture_output=True, input=stdin, timeout=300)
    print("STEP %s rc=%d" % (name, r.returncode))
    for l in (r.stdout + r.stderr).decode("utf-8", "replace").splitlines()[:30]:
        print("  | " + l[:220])
    return r
cfg = D + "/fn.toml"; p = port()
open(cfg, "w").write('[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/control.sock"\n[log]\npath = "%s/fn.log"\n[alerts]\n' % (D, p, D, D))
run("init", "operator", cfg, "init", "fn.test")
run("show (whole file)", "operator", cfg, "show")
run("show listener port", "operator", cfg, "show", "listener", "port")
mcfg = D + "/relay/fn.toml"; os.makedirs(D + "/relay")
run("mission relay --port", "operator", mcfg, "mission", "relay", "--port", str(port()))
run("mission relay again (existing file, expected refusal)", "operator", mcfg, "mission", "relay")
r = subprocess.run(["cat", mcfg], capture_output=True); print("  mission fn.toml:\n" + r.stdout.decode())
run("init under the mission", "operator", mcfg, "init", "fn.test")
run("init under the mission with a profile flag (expected refusal)", "operator", mcfg, "init", "fn.test", "--profile", "scale")
run("status under the mission", "operator", mcfg, "status")
o = subprocess.Popen([I, "--fn", "operator", cfg, "run"], env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
while True:
    l = o.stdout.readline()
    if not l or l.startswith(b"LISTENING"): break
print("owner pid", o.pid, l)
os.rename(D + "/fn.log", D + "/fn.log.1")
o.send_signal(signal.SIGHUP); time.sleep(2)
with socket.create_connection(("127.0.0.1", p), 30) as c:
    c.makefile("rb").readline()
time.sleep(1)
o.send_signal(signal.SIGHUP); time.sleep(2)
print("fn.log exists after SIGHUP:", os.path.exists(D + "/fn.log"))
for f in ("fn.log.1", "fn.log"):
    if os.path.exists(D + "/" + f):
        print("== " + f); print(open(D + "/" + f).read()[-800:])
o.send_signal(signal.SIGTERM); o.wait(60); print("owner exit", o.returncode)
