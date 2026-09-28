#!/usr/bin/env python3
"""Reopen of a fixture store with and without the state checkpoint (lane checkpoint-arena-2).
usage: reopen_ckpt.py TREE IMAGE FIXTURE WORK JSON MODE
MODE full: the fixture's copy with any state checkpoint moved aside (full replay).
MODE ckpt: the copy checkpointed first by the developer verb `store ROOT checkpoint`
(timed), then opened (open=checkpoint:S).
MODE asis (fundamentals-scoreboard): the copy opened with the fixture's own checkpoint in place.
MODE reckpt (fundamentals-scoreboard): the fixture's checkpoint kept, the verb run over it (so
the checkpoint the owner opens is this image's), then opened.  The registered fixtures are
compacted (early log segments dropped), so full/ckpt refuse them: checkpoint-damaged.  Either way `operator run` with the heap hook:
seconds to LISTENING, VmRSS/VmHWM, the live heap after a full collection, the open line."""
import json, os, shutil, subprocess, sys, time
from pathlib import Path
tree, image, fixture, work, out_path, mode = sys.argv[1:7]
sys.path.insert(0, tree + "/tools"); sys.path.insert(0, tree)
import rep_measure as r
import msgid_measure as m
work = Path(work); work.mkdir(parents=True, exist_ok=False)
shutil.copytree(Path(fixture) / "store", work / "store", symlinks=True)
lock = work / "store" / "writer.lock"
if not lock.exists():
    # the t40k-2k-cp5 fixture's store has none (its loader's): the init's empty file
    lock.touch(mode=0o600)
cp = work / "store" / "store-checkpoint.fnsc"
if cp.exists() and mode in ("full", "ckpt"):
    cp.rename(work / "old-store-checkpoint.fnsc")
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
heap_dir = work / "heap"; heap_dir.mkdir(); env["FN_HEAP_DIR"] = str(heap_dir)
env["FN_PROF_LOAD"] = os.environ.get("FS_HEAP_HOOK", str(Path(__file__).resolve().parent / "heap.lisp"))
res = {"mode": mode, "image": image, "core_sha256": m.digest(image + ".core"), "fixture": fixture}
reb = subprocess.run([image, "--fn", "store", str(work / "store"), "rebind-filesystem"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
sec = subprocess.run([image, "--fn", "store", str(work / "store"), "node-secret", "create"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
res["rebind_rc"] = reb.returncode; res["node_secret_rc"] = sec.returncode
if mode in ("ckpt", "reckpt"):
    env2 = dict(env); env2.pop("FN_PROF_LOAD", None)
    t0 = time.perf_counter()
    ck = subprocess.run(["/usr/bin/time", "-v", image, "--fn", "store", str(work / "store"), "checkpoint"],
                        env=env2, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    res["checkpoint_seconds"] = time.perf_counter() - t0
    res["checkpoint_rc"] = ck.returncode
    res["checkpoint_out"] = ck.stdout.decode("ascii", "replace")[-600:]
    err = ck.stderr.decode("ascii", "replace")
    res["checkpoint_err_tail"] = err[-300:]
    for line in err.splitlines():
        if "Maximum resident set size" in line:
            res["checkpoint_maxrss_kib"] = int(line.split(":")[-1])
    res["checkpoint_octets"] = cp.stat().st_size if cp.exists() else None
port = m.free_port()
config = work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                  % (work / "store", port, work / "control.sock"), encoding="ascii")
proc, res["open_seconds"], stderr = r.start_owner(Path(image), config, env, work / "owner.stderr")
heap = r.Heap(str(heap_dir), proc)
res["residency_open"] = r.residency(proc, heap, "open")
r.stop_owner(proc, stderr)
tail = (work / "owner.stderr").read_text(errors="replace")
res["open_line"] = [l for l in tail.splitlines() if "OWNER-OPEN" in l]
res["stderr_tail"] = tail[-1200:]
Path(out_path).write_text(json.dumps(res, indent=1))
print(json.dumps({k: res.get(k) for k in ("mode", "open_seconds", "open_line", "checkpoint_seconds", "checkpoint_octets", "residency_open")}))
