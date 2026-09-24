#!/bin/sh
# m4-app-receipt runner: one module (or test id) at a time, each to its own log.
# Images are this lane's unfrozen DTN pair built from the tree below.
set -u
S=/tank/fn/scratch/m4-app-receipt
T=$S/tree
B=$T/build
L=$S/logs
cd "$T"
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_DTN_HOST=$B/fn-host-dtn
export FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_CONTACT_SENDER=$B/fn-host-dtn
export FN_NATIVE_CONTACT_RECEIVER=$B/fn-host-dtn
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR" "$L"
for m in "$@"; do
  log=$L/$m${NS_TAG:+.$NS_TAG}.log
  {
    echo "# target tests.$m  start $(date -u +%FT%TZ)  cwd $T"
    echo "# cmd: timeout 3600 python3 -m unittest -v tests.$m"
    env | grep -E '^(FN_|LD_LIBRARY_PATH|SBCL_HOME)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s.%N)
  timeout 3600 python3 -m unittest -v "tests.$m" >> "$log" 2>&1 < /dev/null
  rc=$?
  e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f end %s\n' "$rc" "$(echo "$e - $s" | bc)" "$(date -u +%FT%TZ)" >> "$log"
  echo "$m${NS_TAG:+.$NS_TAG} rc=$rc $(tail -n 4 "$log" | grep -E '^(OK|FAILED)' )"
done
