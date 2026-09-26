#!/bin/sh
# consumer-e2 native runner (from qual-bbf52159/run.sh): one target per log.
# Usage: I=<image dir> T=<tree> NS_TAG=x sh run.sh target [target...]
set -u
S=/tank/fn/scratch/consumer-e2
I=${I:?image dir}
T=${T:-$S/tree}
L=$S/logs
mkdir -p "$L" "$S/bin" "$S/diag"
ln -sf "$I/runtime/sbcl" "$S/bin/sbcl"
printf '#!/bin/sh\nLD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib exec /tank/fn/toolchains/openssl-3.5.8/bin/openssl "$@"\n' > "$S/bin/test-openssl"
chmod +x "$S/bin/test-openssl"
cd "$T"
export PATH=$S/bin:$PATH
export SBCL_HOME=$I/runtime/sbcl-home/
export PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$I/fn-host
export FN_NATIVE_DEVELOPER_HOST=$I/fn-host-developer
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
export FN_TEST_OPENSSL=$S/bin/test-openssl
export FN_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl
for f in CONSUMER_E2E CONSUMER_POLL_E2E CONSUMER_EXCHANGE; do export FN_RUN_$f=1; done
for m in "$@"; do
  log=$L/$m${NS_TAG:+.$NS_TAG}.log
  export FN_CONSUMER_EXCHANGE_EVIDENCE=$L/$m${NS_TAG:+.$NS_TAG}.evidence.json
  {
    echo "# target tests.$m  start $(date -u +%FT%TZ)  cwd $T image $I"
    echo "# cmd: python3 -m unittest -v tests.$m"
    env | grep -E '^(FN_|LD_LIBRARY_PATH|SBCL_HOME)' | sort | sed 's/^/# env /'
  } > "$log"
  s=$(date +%s.%N)
  timeout 3600 python3 -m unittest -v "tests.$m" >> "$log" 2>&1
  rc=$?
  e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f end %s\n' "$rc" "$(echo "$e - $s" | bc)" "$(date -u +%FT%TZ)" >> "$log"
  echo "$m${NS_TAG:+.$NS_TAG} rc=$rc $(tail -n 4 "$log" | grep -E '^(OK|FAILED)' )"
done
