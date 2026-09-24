#!/bin/sh
# m4-dtn-n08 runner: one module (or test id) at a time, each to its own log.
# Usage: sh run.sh target [target...]
# NS_TAG=x adds .x to the log name.  NS_DEV_IMAGE (default fn-host-developer)
# is FN_NATIVE_DEVELOPER_HOST, the image test_bp_node_native drives;
# NS_BP_IMAGE (default fn-host-dtn-developer) is FN_NATIVE_BP_HOST;
# NS_CONTACT_IMAGE (default fn-host-dtn) is the contact sender and receiver.
set -u
S=/tank/fn/scratch/m4-dtn-n08
T=$S/tree
REV=1b73486898d9b49fc1907690a406a7a422dabcc4
I=$T/build/images/$REV
L=$S/logs
mkdir -p "$L" "$S/bin"
ln -sf "$I/runtime/sbcl" "$S/bin/sbcl"
cd "$T"
h() { awk -v f="$1" '$2==f {print $1}' "$I/image.sha256"; }
export PATH=$S/bin:$PATH
export SBCL_HOME=$I/runtime/sbcl-home/
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$I/fn-host
export FN_NATIVE_DEVELOPER_HOST=$I/${NS_DEV_IMAGE:-fn-host-developer}
export FN_NATIVE_CRASH_HOST=$I/fn-host-developer
export FN_NATIVE_DTN_HOST=$I/fn-host-dtn
export FN_NATIVE_DTN_DEVELOPER_HOST=$I/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$I/${NS_BP_IMAGE:-fn-host-dtn-developer}
export FN_NATIVE_CONTACT_SENDER=$I/${NS_CONTACT_IMAGE:-fn-host-dtn}
export FN_NATIVE_CONTACT_RECEIVER=$I/${NS_CONTACT_IMAGE:-fn-host-dtn}
export FN_NATIVE_IMAGE_SOURCE_SHA=$REV
export FN_NATIVE_LAUNCHER_SHA256=$(h fn-host)
export FN_NATIVE_CORE_SHA256=$(h fn-host.core)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$(h fn-host-developer)
export FN_NATIVE_DEVELOPER_CORE_SHA256=$(h fn-host-developer.core)
export FN_NATIVE_RUNTIME_SHA256=$(h runtime/sbcl)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR"
for m in "$@"; do
  log=$L/$m${NS_TAG:+.$NS_TAG}.log
  {
    echo "# target tests.$m  start $(date -u +%FT%TZ)  cwd $T"
    echo "# cmd: python3 -m unittest -v tests.$m"
    echo "# sbcl on PATH: $(command -v sbcl) ($(sbcl --version))"
    env | grep -E '^(FN_|LD_LIBRARY_PATH|SBCL_HOME)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s.%N)
  timeout 3600 python3 -m unittest -v "tests.$m" >> "$log" 2>&1 < /dev/null
  rc=$?
  e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f end %s\n' "$rc" "$(echo "$e - $s" | bc)" "$(date -u +%FT%TZ)" >> "$log"
  echo "$m${NS_TAG:+.$NS_TAG} rc=$rc $(tail -n 4 "$log" | grep -E '^(OK|FAILED)' )"
done
