#!/bin/sh
# Certify fn2 books on dregg-forge (docs/boxes.md). Run it ON the box, from any fn2 tree:
#
#   swarm-build sh fn2/tools/forge-certify.sh [-j N] [book.lisp ...]
#
# No books named: the whole closure (every certifiable book under books/ sim/ tests/;
# the LD-only drivers and raw-Lisp files are excluded, see EXCLUDED below).
# Books named: those books and whatever they depend on (cert.pl rebuilds only what is stale).
# -j defaults to 8. Log in the tree: build/certify-closure.log (whole closure) or build/certify-named.log (named books);
# per-book times: python3 fn2/tools/certify-times.py [TREE [LOG]].
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
: "${FN_ACL2:=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}"
: "${ACL2_SYSTEM_BOOKS:=/tank/fn/acl2-8.7/books}"
export FN_ACL2 ACL2_SYSTEM_BOOKS
TIME_CERT=1; export TIME_CERT
jobs=8
log=certify-named.log
if [ "${1:-}" = -j ]; then jobs=$2; shift 2; fi
EXCLUDED="sim/abi-evidence sim/echo-evidence sim/echo-scenario tests/format-check tests/alloc-random tests/blake3-native tests/blake3-vectors tests/check-history-unit tests/core-allocation tests/crash-model-differential tests/merkle-random tests/scribe-scenario tests/sim-allocation tests/sim-device-broad tests/sim-fault-controls tests/sim-layer-a tests/sim-replay-controls"
if [ "$#" -eq 0 ]; then
  log=certify-closure.log
  cd "$root/fn2"
  for f in books/*.lisp sim/*.lisp tests/*.lisp; do
    case " $EXCLUDED " in *" ${f%.lisp} "*) continue ;; esac
    set -- "$@" "$f"
  done
fi
mkdir -p "$root/build"
date +%s > "$root/build/certify-start"
status=0
sh "$root/fn2/tools/certify.sh" -j "$jobs" -k "$@" > "$root/build/$log" 2>&1 || status=$?
date +%s > "$root/build/certify-end"
echo "exit $status" >> "$root/build/$log"
tail -3 "$root/build/$log"
exit "$status"
