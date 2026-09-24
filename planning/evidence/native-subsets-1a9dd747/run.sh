#!/bin/sh
# native-subsets-1a9dd747 runner: one module at a time, each to its own log.
# Usage: sh run.sh module [module...]   (runs in the scratch copy of the gate)
set -u
G=/tank/fn/gates/qual-1a9dd747-20260924
S=/tank/fn/scratch/native-subsets-1a9dd747
T=$S/tree
L=$S/logs
mkdir -p "$L"
cd "$T"
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$G/build/fn-host
export FN_NATIVE_DEVELOPER_HOST=$G/build/fn-host-developer
export FN_NATIVE_CRASH_HOST=$G/build/fn-host-developer
export FN_NATIVE_IMAGE_SOURCE_SHA=1a9dd747855c2e23ddfd4d8357270ef8f75cebb8
export FN_NATIVE_LAUNCHER_SHA256=60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9
export FN_NATIVE_CORE_SHA256=12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=5d42db2d8929ba256677ecb3bdfe957edc54176e0f5a1492b24376aa21ae1d9d
export FN_NATIVE_DEVELOPER_CORE_SHA256=9b38ba45ed4ce31ca1997e3e4165873203e09d8e41fa176eb3fedbfee95741d0
export FN_NATIVE_RUNTIME_SHA256=$(sha256sum /tank/fn/sbcl/bin/sbcl | cut -d' ' -f1)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR"
for m in "$@"; do
  log=$L/$m${NS_TAG:+.$NS_TAG}.log
  {
    echo "# module tests.$m  start $(date -u +%FT%TZ)  cwd $T"
    echo "# cmd: python3 -m unittest -v tests.$m"
    env | grep -E '^(FN_|LD_LIBRARY_PATH)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s.%N)
  timeout 3600 python3 -m unittest -v "tests.$m" >> "$log" 2>&1
  rc=$?
  e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f end %s\n' "$rc" "$(echo "$e - $s" | bc)" "$(date -u +%FT%TZ)" >> "$log"
  echo "$m rc=$rc $(tail -n 4 "$log" | grep -E '^(OK|FAILED)' )"
done
