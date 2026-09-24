#!/bin/sh
# bp-app-txid runner: runs named unittest ids against an image.
# Usage: sh runcase.sh <tree> <image-dir> <src-sha> <tag> <test-id> [...]
set -u
T=$1; B=$2; SRC=$3; TAG=$4; shift 4
S=/tank/fn/scratch/bp-app-txid
L=$S/logs/$TAG
mkdir -p "$L"
cd "$T"
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$B/fn-host
export FN_NATIVE_DEVELOPER_HOST=$B/fn-host-developer
export FN_NATIVE_CRASH_HOST=$B/fn-host-developer
export FN_NATIVE_IMAGE_SOURCE_SHA=$SRC
[ -e "$B/fn-host" ] && export FN_NATIVE_LAUNCHER_SHA256=$(sha256sum -L "$B/fn-host" 2>/dev/null | cut -d' ' -f1 || sha256sum "$B/fn-host" | cut -d' ' -f1)
[ -e "$B/fn-host.core" ] && export FN_NATIVE_CORE_SHA256=$(sha256sum "$B/fn-host.core" | cut -d' ' -f1)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$(sha256sum "$B/fn-host-developer" | cut -d' ' -f1)
export FN_NATIVE_DEVELOPER_CORE_SHA256=$(sha256sum "$B/fn-host-developer.core" | cut -d' ' -f1)
export FN_NATIVE_RUNTIME_SHA256=$(sha256sum /tank/fn/sbcl/bin/sbcl | cut -d' ' -f1)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag/$TAG
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR"
for m in "$@"; do
  log=$L/$m.log
  {
    echo "# test $m  start $(date -u +%FT%TZ)  cwd $T"
    echo "# cmd: python3 -m unittest -v $m"
    env | grep -E '^(FN_|LD_LIBRARY_PATH)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s)
  timeout 3600 python3 -m unittest -v "$m" >> "$log" 2>&1
  rc=$?
  e=$(date +%s)
  echo "# rc=$rc wall=$((e - s))s end $(date -u +%FT%TZ)" >> "$log"
  echo "$m rc=$rc $(grep -E '^(OK|FAILED)' "$log" | tail -1)"
done
