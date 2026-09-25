#!/bin/sh
set -u
S=/tank/fn/scratch/test-latency; T=$S/tree; L=$S/logs; mkdir -p $L $S/site $S/diag
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
B=$T/build
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer FN_NATIVE_READER_HOST=$B/fn-host-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
cat > $S/site/sitecustomize.py <<PY
import subprocess, os, time
_orig = subprocess.Popen.__init__
def _init(self, args, *a, **k):
    t = time.time()
    try:
        first = args[0] if isinstance(args, (list, tuple)) else args
        with open("$L/popen.log", "a") as f:
            f.write("%s %s\n" % (t, os.path.basename(str(first))))
    except Exception:
        pass
    _orig(self, args, *a, **k)
subprocess.Popen.__init__ = _init
PY
rm -f $L/popen.log
cd $T
s=$(date +%s)
PYTHONPATH=$S/site systemd-run --user --scope -q -p MemoryMax=24G timeout 3600 python3 tools/test_budget.py --one tests.test_bp_node_native > $L/after.log 2>&1 < /dev/null
echo "after rc=$? wall=$(( $(date +%s)-s ))s"
sha256sum $L/after.log
awk '{print $2}' $L/popen.log | sort | uniq -c | sort -rn | head
echo ALLDONE
