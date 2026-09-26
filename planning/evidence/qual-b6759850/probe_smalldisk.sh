#!/bin/sh
# qual-b6759850: which files a refused (temporary-space) reclaim changes on the tight store.
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
R=$S/s15/smalldisk; rm -rf $R; mkdir -p $R
cd $S/tree
DEV=$I/fn-host-developer
# the tight store, built and compacted exactly as reclaim_lifecycle_native.py --headroom-only does, stopped before its reclaim
python3 - $DEV $R <<'PY'
import sys, os, shutil, subprocess
sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2], "0", "1024", "300000", "--headroom-only"]
sys.path.insert(0, "tests")
import importlib.util
spec = importlib.util.spec_from_file_location("rl", "tests/reclaim_lifecycle_native.py")
rl = importlib.util.module_from_spec(spec); spec.loader.exec_module(rl)
from pathlib import Path
rl.work.mkdir(parents=True, exist_ok=True)
store, cfg, port = rl.build("tight", 400, 1024, 300000)
rl.native("operator", cfg, "retention", "set", "released-by-all-holders")
print("compact", rl.native("operator", cfg, "store", "compact")[:2])
copy = rl.work / "copy"; shutil.copytree(store, copy)
ccfg, _ = rl.config_for(copy, "copy")
def listing(root):
    import hashlib
    return {str(p.relative_to(root)): (p.stat().st_size, hashlib.sha256(p.read_bytes()).hexdigest()[:16]) for p in Path(root).rglob("*") if p.is_file()}
before = listing(copy)
small = dict(rl.ENV); small["FN_NATIVE_DISK_FREE"] = "1000"
print("reclaim small disk", rl.native("operator", ccfg, "store", "reclaim", env=small))
after = listing(copy)
for k in sorted(set(before) | set(after)):
    if before.get(k) != after.get(k):
        print("CHANGED", k, before.get(k), "->", after.get(k))
print("files before", len(before), "after", len(after))
PY
