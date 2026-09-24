#!/bin/bash
# Opt-in, isolated pinned-ION ID observation test. Never touches the live fn node.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/env.sh"
run=${1:?usage: run_native_send_id.sh ABSOLUTE_RUN_DIR}
sender=${FN_LTP_SEND_BIN:-$ION_ROOT/install/bin/fn_ltp_send}
case "$run" in /*) ;; *) echo 'run directory must be absolute' >&2; exit 5;; esac
mkdir -p "$run/stage"
if [ -e "$run/observation" ]; then echo 'existing observation' >&2; exit 1; fi
cleanup() {
  bash "$here/stop_node.sh" "$ION_ROOT/cfg/node2" >/dev/null 2>&1 || true
  bash "$here/stop_node.sh" "$ION_ROOT/cfg/node1" >/dev/null 2>&1 || true
}
trap cleanup EXIT
bash "$here/start_node.sh" "$ION_ROOT/cfg/node1" > "$run/start-node1.log" 2>&1
bash "$here/start_node.sh" "$ION_ROOT/cfg/node2" > "$run/start-node2.log" 2>&1
printf 'fn-ltp-observed-bundle-id\n' > "$run/request.adu"
(
  cd "$ION_ROOT/cfg/node2"
  timeout 40s fn_ltp_stage ipn:2.1 "$run/stage" 30 1
) > "$run/stage.log" 2>&1 &
stage_pid=$!
(
  sleep 2
  cd "$ION_ROOT/cfg/node1"
  "$sender" ipn:1.1 ipn:2.1 \
    dtn://fn.lab/inbox "$run/request.adu" 60 "$run/observation"
) > "$run/send-stdout.log" 2> "$run/send-stderr.log"
wait "$stage_pid"
observed=$(cat "$run/observation")
staged=$(sed -n 's/^staged \([^ ]*\) .*/\1/p' "$run/stage.log")
case "$observed" in
  "observed-v1|dtn://fn.lab/inbox|ipn:2.1|$staged") ;;
  *) echo 'sender and receiver bundle IDs differ' >&2; exit 1;;
esac
cmp "$run/request.adu" "$run/stage/$staged"
printf 'native ION ID and ADU matched: %s\n' "$staged"
