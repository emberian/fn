#!/bin/sh
set -u
S=/tank/fn/scratch/test-latency; T=$S/tree
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
cd $T
cat > $S/boot.py <<'PY'
import sys, time
sys.path.insert(0, ".")
from tools import run_bp_ingress, run_store
for label in ("store", "bp-ingress"):
    cls = run_store.Acl2Store if label == "store" else run_bp_ingress.Acl2BpIngress
    t = time.time(); b = cls(); print(label, "boot", round(time.time() - t, 2), "preloaded", b.preloaded, flush=True); b.close()
PY
echo "source boots (FN_BRIDGE_IMAGE=0):"; FN_BRIDGE_IMAGE=0 python3 $S/boot.py 2>&1 | grep boot
echo "image build:"; python3 tools/bridge_image.py ensure --kind store 2>&1 | tail -1; python3 tools/bridge_image.py ensure --kind bp-ingress 2>&1 | tail -1
echo "image boots:"; python3 $S/boot.py 2>&1 | grep boot
