#!/bin/sh
# qual-dtn-c3420013 native runner (qual-c3420013 run.sh, scratch path changed; NS_DEV_IMAGE overrides FN_NATIVE_DEVELOPER_HOST): one module (or test id) at a time, each to its own log.
# Usage: sh run.sh target [target...]
# NS_TAG=x adds .x to the log name. NS_BP_IMAGE=fn-host-dtn-developer for the
# selector cases. NS_BP_NODE_IMAGE picks the bp-node image (default the DTN
# developer image). The image's SBCL is first on PATH and every opt-in flag is set.
set -u
G=/tank/fn/gates/qual-c3420013-20260925
I=$G/build/images/c3420013
S=/tank/fn/scratch/qual-dtn-c3420013
T=$S/tree
L=$S/logs
mkdir -p "$L"
cd "$T"
h() { awk -v f="$1" '$2==f {print $1}' "$I/image.sha256"; }
export PATH=$S/bin:$PATH
export SBCL_HOME=$I/runtime/sbcl-home/
export PYTHONDONTWRITEBYTECODE=1
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
export FN_NATIVE_BP_HOST=$I/${NS_BP_IMAGE:-fn-host-dtn}
export FN_NATIVE_BP_NODE_HOST=$I/${NS_BP_NODE_IMAGE:-fn-host-dtn-developer}
export FN_NATIVE_CONTACT_SENDER=$I/fn-host-dtn
export FN_NATIVE_CONTACT_RECEIVER=$I/fn-host-dtn
export FN_NATIVE_IMAGE_SOURCE_SHA=c3420013
export FN_NATIVE_LAUNCHER_SHA256=$(h fn-host)
export FN_NATIVE_CORE_SHA256=$(h fn-host.core)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$(h fn-host-developer)
export FN_NATIVE_DEVELOPER_CORE_SHA256=$(h fn-host-developer.core)
export FN_NATIVE_RUNTIME_SHA256=$(h runtime/sbcl)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
export FN_D23_VERIFY=1
export FN_TEST_OPENSSL=$S/bin/test-openssl
for f in TOPIC_LOCAL_E2E TOPIC_METADATA_E2E HYBRID_E2E NATIVE_READER_INDEX \
         CONSUMER_INSPECT CONSUMER_PROJECT_BOUNDS NATIVE_CLONE CONSUMER_E2E \
         CONSUMER_POLL_E2E VERIFY_E2E; do export FN_RUN_$f=1; done
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
