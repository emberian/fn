#!/bin/sh
# marker-required: the commit path with the marker on ZFS (/tank), profiled.
# `store ROOT probe N` commits N maximum payloads in one process (the m5 probe);
# strace -c attributes the wall to syscall classes, and a second run with
# strace -T gives the per-call latency of each fsync by target.
set -u
S=/tank/fn/scratch/marker-required
IMG=$S/src/build/fn-host-developer
W=$S/probe; rm -rf $W; mkdir -p $W
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
N=${N:-120}
echo "## image"; sha256sum $IMG.core
for run in 1 2 3; do
  "$IMG" --fn store $W/plain-$run probe $N > $W/plain-$run.json 2>&1; echo "plain run $run: $(cat $W/plain-$run.json | tr -d '\n' | cut -c1-300)"
done
echo "## strace -c (syscall summary, one run)"
strace -f -c -e trace=fsync,fdatasync,rename,renameat,renameat2,link,linkat,unlink,unlinkat,openat,write,pwrite64 -o $W/strace-c.txt "$IMG" --fn store $W/sc probe $N > $W/sc.json 2>&1
cat $W/strace-c.txt
echo "## strace -T fsync latency by target (one run)"
strace -f -T -y -e trace=fsync,fdatasync -o $W/strace-t.txt "$IMG" --fn store $W/st probe $N > $W/st.json 2>&1
python3 - "$W/strace-t.txt" <<'PY'
import re, sys, collections
t = collections.defaultdict(list)
for line in open(sys.argv[1]):
    m = re.search(r'f(?:data)?sync\(\d+<([^>]*)>\)\s*=\s*0\s*<([\d.]+)>', line)
    if not m: continue
    path = m.group(1)
    if "/.stage-marker" in path or path.endswith("committed-history.json"): k = "marker stage file"
    elif "/.stage-" in path and "frontier" in path: k = "frontier stage file"
    elif "/staging/.stage" in path: k = "record stage file"
    elif path.endswith("/transactions"): k = "transactions dir"
    elif path.endswith("/staging"): k = "staging dir"
    elif re.search(r'/(st|sc|plain-\d)$', path): k = "store root dir"
    else: k = path.rsplit("/", 1)[-1][:40]
    t[k].append(float(m.group(2)) * 1000)
for k, v in sorted(t.items(), key=lambda kv: -sum(kv[1])):
    v.sort()
    print("%-22s n=%4d total=%8.1f ms mean=%6.2f p50=%6.2f p90=%6.2f" % (k, len(v), sum(v), sum(v)/len(v), v[len(v)//2], v[int(len(v)*0.9)]))
PY
echo PROBE-DONE
