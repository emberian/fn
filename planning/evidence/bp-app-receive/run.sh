#!/bin/sh
# bp-app-receive runner.  Usage: IMG=after|before sh run.sh target...
# after:  the developer image built from lane commit in tree/build.
# before: the 47bdb9a4 qualification developer image (read only).
# Tests and the Python/ACL2 bridge always come from tree/ (the lane commit).
set -u
S=/tank/fn/scratch/bp-app-receive
T=$S/tree
L=$S/logs
case "${IMG:-after}" in
  after) I=$T/build ;;
  before) I=/tank/fn/gates/qual-47bdb9a4-20260924/build/images/47bdb9a4 ;;
esac
mkdir -p "$L" "$S/diag"
cd "$T"
export PATH=/tank/fn/scratch/native-subsets-47bdb9a4/bin:$PATH
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_DEVELOPER_HOST=$I/fn-host-developer
export FN_NATIVE_BP_HOST=$I/fn-host-dtn-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
for m in "$@"; do
  log=$L/$m.${IMG:-after}.log
  {
    echo "# target tests.$m  image ${IMG:-after} $I  start $(date -u +%FT%TZ)  cwd $T"
    echo "# cmd: python3 -m unittest -v tests.$m"
    echo "# image core sha256: $(sha256sum $I/fn-host-developer.core | cut -c1-64)"
    env | grep -E '^(FN_|LD_LIBRARY_PATH)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s)
  timeout 3600 python3 -m unittest -v "tests.$m" >> "$log" 2>&1
  rc=$?
  printf '# rc=%s wall=%ss end %s\n' "$rc" "$(( $(date +%s) - s ))" "$(date -u +%FT%TZ)" >> "$log"
  echo "$m.${IMG:-after} rc=$rc $(tail -n 4 "$log" | grep -E '^(OK|FAILED)')"
done
