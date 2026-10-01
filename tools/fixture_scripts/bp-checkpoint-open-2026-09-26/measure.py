"""bp-checkpoint-open: the three opens of SCN-077's first half on the
registered fixture (1,311 held rows): dispatch before the rotation, the
rotation, dispatch after it (the reopen from the kind-19 checkpoint).
Usage: measure.py LABEL TREE IMAGE"""
import os, sys, time, subprocess, shutil
label, tree, image = sys.argv[1:4]
FIX = "/tank/fn/scratch/fixtures/bp-checkpoint-open-1311"
W = f"/tank/fn/scratch/bp-checkpoint-open/run-{label}"
shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
subprocess.run(["tar", "-C", W, "-xf", f"{FIX}/pre-rotation.tar"], check=True)
t = f"{W}/t"
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"
env.pop("ACL2_SYSTEM_BOOKS", None); env.pop("FN_HOST", None)
env["FN_BP_TEST_PROFILE"] = "999999"
disp = ["bp-node", "dispatch", f"{t}/fnbs", f"{t}/store", f"{t}/fnrj", f"{t}/fnwf",
        "dtn://receiver/", "dtn://sender/", "dtn://receiver/", "native-policy",
        "dtn://receiver/", "127.0.0.1", 9, 1, 3600000, 2, 32, 1048576, 1000, 0]
out = open(f"{W}/table.txt", "wb")
for name, args in [("dispatch-before-rotation", disp),
                   ("rotation", ["bp-node", "checkpoint", f"{t}/fnbs", "dtn://receiver/"]),
                   ("dispatch-after-rotation", disp)]:
    s = time.monotonic()
    p = subprocess.run([image, "--fn", *map(str, args)], cwd=tree, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=7200)
    w = time.monotonic() - s
    out.write(f"== {name} rc={p.returncode} wall={w:.1f}s\n".encode())
    out.write(b"\n".join(l for l in p.stdout.splitlines()
                         if l.startswith(b"BP profile") or l.startswith(b"BP FNBS")
                         or b"retired" in l) + b"\n")
    out.write(p.stderr[-2000:] + b"\n"); out.flush()
    print(f"MEASURE {label} {name} rc={p.returncode} wall={w:.1f}s", flush=True)
print("MEASURE-DONE", flush=True)
