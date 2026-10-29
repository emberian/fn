#!/bin/sh
# Run one fn2 acceptance driver (an LD .lsp) on dregg-forge, detached (docs/boxes.md). ON the box, from any fn2 tree
# whose books are certified (fn2/tools/forge-certify.sh):
#
#   sh fn2/tools/forge-driver.sh NAME            start it; prints the PID file and log
#   sh fn2/tools/forge-driver.sh                 list the names (SECS=N overrides the timeout; any tests/NAME.lsp works)
#
# Log build/NAME.log, PID file build/NAME.pid, in the tree. Stop one with the PID in its PID file, only that.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
case "${1:-}" in
  sim-layer-a-a4-driver)       secs=3600 ;;   # layer A's full fixed gate (A: R1 coverage, R3 differential, R5b controls)
  core-allocation-driver)      secs=900 ;;
  sim-allocation-driver)       secs=900 ;;
  executor-allocation-driver)  secs=1800 ;;
  sim-acquisition-driver)      secs=1800 ;;
  sim-layer-a-a4-smoke)        secs=1800 ;;
  crash-model-differential)    secs=1800 ;;   # layer B's concrete differential sweep (B1)
  sim-layer-b)                 secs=7200 ;;   # layer B's commit-machine concrete sweep (B3b-2 nightly row; FN2_B_PROFILE=tiny for the gate)
  blake3-vectors)              secs=7200 ;;
  "") echo "A: sim-layer-a-a4-driver core-allocation-driver sim-allocation-driver executor-allocation-driver sim-acquisition-driver sim-layer-a-a4-smoke" >&2
      echo "B: crash-model-differential blake3-vectors sim-layer-b (the 20,000-case concrete sweep; any tests/NAME.lsp runs the same way, SECS=N sets its timeout)" >&2; exit 2 ;;
  *) [ -f "$root/fn2/tests/$1.lsp" ] || { echo "no fn2/tests/$1.lsp" >&2; exit 2; }; secs=3600 ;;
esac
name=$1
secs=${SECS:-$secs}
: "${FN_ACL2:=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}"
export FN_ACL2
cd "$root"
mkdir -p build
# Fixed gates run with FN2_SWARM and FN2_SWARM_SEED unset.
unset FN2_SWARM FN2_SWARM_SEED || :
nohup swarm-build timeout -k 5 "$secs" tools/acl2 < "fn2/tests/$name.lsp" > "build/$name.log" 2>&1 &
echo $! > "build/$name.pid"
echo "started $name pid $(cat "build/$name.pid"): $root/build/$name.log"
