#!/usr/bin/env python3
"""Live heap by object type (reservation-after-flip scratch).
usage: slope.py TREE IMAGE WORK --posts N --octets L [--groups K] [--flags ...]
init a store with FLAGS (default the small preset), GC+ROOM at: empty, after N POSTs, after reopen."""
import argparse, json, os, re, subprocess, sys, time, shutil
from pathlib import Path
ap = argparse.ArgumentParser()
ap.add_argument("tree"); ap.add_argument("image"); ap.add_argument("work")
ap.add_argument("--posts", type=int, default=1000); ap.add_argument("--octets", type=int, default=2048)
ap.add_argument("--groups", type=int, default=1); ap.add_argument("--subject", type=int, default=0); ap.add_argument("--heap", type=int, default=2048)
# 16 MiB of history (was 8 MiB): the 1,000 x 8,000 row's bodies alone are
# 8,000,000 octets, and under format 10 the store refused POST 998 as full
# (batch AZ, 2026-09-28); all three rows share the profile.
ap.add_argument("--flags", default="--profile development --max-transactions 16384 --max-history-octets 16777216 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128")
a = ap.parse_args()
sys.path.insert(0, a.tree + "/tools"); sys.path.insert(0, a.tree)
import rep_measure as r, msgid_measure as m
work = Path(a.work); shutil.rmtree(work, ignore_errors=True); work.mkdir(parents=True)
heapd = work / "heap"; heapd.mkdir()
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
env["FN_HEAP_DIR"] = str(heapd); env["FN_PROF_LOAD"] = str(Path(__file__).resolve().parent / "hook.lisp")
env["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % a.heap
groups = ["fn.test"] + ["fn.g%d" % i for i in range(1, a.groups)]
port = m.free_port(); config = work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"))
res = subprocess.run([a.image, "--fn", "operator", str(config), "init"] + a.flags.split() + ["fn.letters"] + groups, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out = {"init_rc": res.returncode, "init_out": res.stdout.decode(errors="replace")[-400:], "posts": a.posts, "octets": a.octets, "groups": a.groups}
fig = subprocess.run([a.image, "--fn", "heap", "--", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out["figure"] = fig.stdout.decode(errors="replace").strip()[-300:]
def snap(tag):
    (heapd / "go").write_text(tag)
    t = time.time()
    while not (heapd / ("done-" + tag)).exists():
        if time.time() - t > 120: return {"error": "timeout"}
        time.sleep(0.05)
    return (heapd / ("heap-" + tag + ".txt")).read_text()
if a.groups > 1:
    ng = ",".join(groups)
    orig = r.article
    def art(i, octets, _o=orig):
        return _o(i, octets).replace(b"Newsgroups: fn.test", b"Newsgroups: " + ng.encode(), 1)
    r.article = art
if a.subject:
    orig2 = r.article
    def art2(i, octets, _o=orig2):
        return _o(i, octets).replace(b"Subject: rep %d" % i, b"Subject: rep %d" % i + b"\r\n ssssssssss ssssssssss ssssssssss ssssssssss ssssssssss ssssssssss sssssssss" * (a.subject // 75), 1)
    r.article = art2
out["subject"] = a.subject
proc, secs, err = r.start_owner(Path(a.image), config, env, work / "owner.stderr", timeout=600)
try:
    time.sleep(1); out["empty"] = snap("gc-empty")
    c = m.Conn(port); t0 = time.time()
    for i in range(a.posts): r.post(c, i, a.octets)
    out["post_s"] = round(time.time() - t0, 2); c.close()
    out["posted"] = snap("gc-posted")
    if os.environ.get("RAF_STR"): out["strings"] = snap("str-posted")
finally:
    r.stop_owner(proc, err)
st = subprocess.run([a.image, "--fn", "operator", str(config), "status"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out["status"] = st.stdout.decode(errors="replace")[-1500:]
proc, secs, err = r.start_owner(Path(a.image), config, env, work / "owner.stderr", timeout=600)
try:
    out["reopen_s"] = round(secs, 3); time.sleep(1); out["reopen"] = snap("gc-reopen")
finally:
    r.stop_owner(proc, err)
out["stderr_tail"] = (work / "owner.stderr").read_text(errors="replace")[-800:]
print(json.dumps(out, indent=1))
