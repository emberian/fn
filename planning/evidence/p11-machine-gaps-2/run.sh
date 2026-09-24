#!/bin/sh
set -u
S=/tank/fn/scratch/p11-gaps-2
T=$S/tree
B=$T/build
L=$S/logs
cd "$T"
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_DTN_DEVELOPER_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_BP_NODE_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$B/fn-host-dtn-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR" "$L"
tag=$1; shift
log=$L/$tag.log
{ echo "# targets $*  start $(date -u +%FT%TZ)  cwd $T"; env | grep -E "^(FN_|LD_LIBRARY_PATH)" | sort | sed "s/^/# env /"; } > "$log"
timeout 3600 python3 -m unittest -v "$@" >> "$log" 2>&1 < /dev/null
echo "# rc=$? end $(date -u +%FT%TZ)" >> "$log"
tail -n 5 "$log"
