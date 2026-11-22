#!/bin/sh
# Run only after current books/node-profile and books/native-b3-evidence
# are record-qualified/installed, within the owner's named capped scope.
# Pass the full SHA from the completed qualification; never infer it from HEAD.
# Modes are sequential: host, fnct, durable-retry, nntp, large, cursor, fanout, membership. Each requires its own bounded scope.
set -eu
candidate=${1:?usage: native-current-gate.sh CANDIDATE QUALIFIED_FULL_SHA host-or-fnct-or-durable-retry-or-nntp-or-large-or-cursor-or-fanout-or-membership}
expected=${2:?missing explicitly qualified full source SHA}
mode=${3:?missing mode}
[ "${#expected}" -eq 40 ] || { echo 'expected full 40-character SHA' >&2; exit 2; }
case "$expected" in *[!0123456789abcdef]*) echo 'invalid source SHA' >&2; exit 2 ;; esac
case "$mode" in host|fnct|durable-retry|nntp|large|cursor|fanout|membership) ;; *) echo 'invalid mode' >&2; exit 2 ;; esac
[ "$(git -C "$candidate" rev-parse HEAD)" = "$expected" ] || {
  echo 'candidate changed: reconcile current qualified source before execution' >&2; exit 2;
}
git -C "$candidate" diff --quiet
git -C "$candidate" diff --cached --quiet
exec env -i HOME="$HOME" USER="${USER:-fn}" PATH="$PATH" LANG=C \
 FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k \
 FN_SBCL=/tank/fn/sbcl/bin/sbcl SBCL=/tank/fn/sbcl/bin/sbcl \
 FN_CERT_CACHE=/home/fn/.cache/fn-certs FN_ACL2_DYNAMIC_SPACE_MB=4096 FN_ACL2_SLOT_WAIT=30 \
 FN2_ORIGIN_LINEAGE=811 FN2_ORIGIN_DOMAIN=812 FN2_ORIGIN_INCARNATION=1 \
 FN2_HISTORY_ID=813 FN2_HISTORY_INCARNATION=1 FN2_STORAGE_FAULT_MODEL=crash-only \
 sh -eu -c '
 cd "$1"
 # Refuse missing/current-key-incompatible artifacts; never certify here.
 python3 tools/certs.py install-set books/node-profile books/native-b3-evidence \
   --root "$PWD" --cache "$FN_CERT_CACHE" --acl2 "$FN_ACL2" \
   --toolchain-identity 8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c
 if [ "$2" != host ]; then
   mkdir -p build
   attempt=$(mktemp -d "build/native-$3-$2.XXXXXXXX")
   run_directory="$attempt/run"
   echo "Native $2 run artifacts in $PWD/$run_directory" >&2
 fi
 case "$2" in
 host)
   sh host/build-blake3.sh build/lib
   python3 tools/host_check.py --load
   python3 tools/interface_emit.py --check
   ;;
 fnct)
   python3 tests/native-append-fetch-restart.py --directory "$run_directory"
   ;;
 durable-retry)
   python3 tests/native-append-fetch-restart.py --directory "$run_directory" --durable-retry
   ;;
 membership)
   python3 tests/native-consumer-membership.py --directory "$run_directory"
   ;;
 fanout)
   python3 tests/native-crosspost-fanout.py --directory "$run_directory"
   ;;
 cursor)
   python3 tests/native-consumer-cursor-restart.py --directory "$run_directory"
   ;;
 nntp)
   python3 tests/native-image-restart.py --directory "$run_directory"
   ;;
 large)
   python3 tests/native-large-article-restart.py --directory "$run_directory"
   ;;
 *) echo "unknown mode: $2" >&2; exit 2 ;;
 esac
 ' sh "$candidate" "$mode" "$expected"
