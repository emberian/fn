#!/bin/zsh
# Reproducible, loopback-only BPv7 laboratory check for dtn7-rs.
# It is an adapter evaluation, not an fn acceptance/receipt implementation.
set -euo pipefail
export NO_PROXY='*'
export no_proxy='*'

SCRIPT=${0:A}
ROOT=${SCRIPT:h}
REPO=${DTN7_REPO:-"$ROOT/dtn7-rs"}
BIN="$REPO/target/release"
RUN_BASE=${BP_RUN_BASE:-"$ROOT/runs"}
mkdir -p "$RUN_BASE"
RUN=$(mktemp -d "$RUN_BASE/bpv7.XXXXXX")
ART="$RUN/artifacts"
mkdir -p "$RUN/a" "$RUN/b" "$ART" "$RUN/inbox"
PA=32101
PB=32102
CA=32111
CB=32112
A_PID=""
B_PID=""
A_STARTS=0
B_STARTS=0

cleanup() {
  for pid in "$A_PID" "$B_PID"; do
    if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      wait "$pid" 2>/dev/null || true
    fi
  done
}
trap cleanup EXIT INT TERM

cat > "$RUN/a.toml" <<EOF_A
nodeid = "bp-a"
ipv4 = false
ipv6 = true
webport = $PA
workdir = "$RUN/a"
db = "sled"
[routing]
strategy = "epidemic"
[core]
janitor = "1s"
[convergencylayers]
cla.0.id = "tcp"
cla.0.port = "$CA"
cla.0.bind = "::1"
[statics]
peers = ["tcp://[::1]:$CB/bp-b"]
[endpoints]
local.0 = "incoming"
EOF_A

cat > "$RUN/b.toml" <<EOF_B
nodeid = "bp-b"
ipv4 = false
ipv6 = true
webport = $PB
workdir = "$RUN/b"
db = "sled"
[routing]
strategy = "epidemic"
[core]
janitor = "1s"
[convergencylayers]
cla.0.id = "tcp"
cla.0.port = "$CB"
cla.0.bind = "::1"
[statics]
peers = ["tcp://[::1]:$CA/bp-a"]
[endpoints]
local.0 = "incoming"
EOF_B

wait_http() {
  local port=$1 out=$2
  for _ in {1..100}; do
    if curl --noproxy '*' -g -6 --fail --silent --show-error --max-time 1 \
        "http://[::1]:$port/status/nodeid" > "$out" 2>/dev/null; then
      return 0
    fi
    sleep 0.1
  done
  return 1
}

inventory() {
  local port=$1 out=$2
  "$BIN/dtnquery" -6 -p "$port" bundles > "$out"
}

wait_for_id() {
  local port=$1 bid=$2 out=$3
  for _ in {1..100}; do
    inventory "$port" "$out"
    if rg -Fq "$bid" "$out"; then
      return 0
    fi
    sleep 0.1
  done
  return 1
}

assert_absent() {
  local port=$1 bid=$2 out=$3
  inventory "$port" "$out"
  if rg -Fq "$bid" "$out"; then
    print -u2 "unexpected retained BPA bundle: $bid"
    return 1
  fi
}

assert_stays_absent() {
  local port=$1 bid=$2 out=$3
  for _ in {1..20}; do
    assert_absent "$port" "$bid" "$out"
    sleep 0.1
  done
}

assert_empty_endpoint() {
  local port=$1 out=$2 target=$3 rc
  set +e
  "$BIN/dtnrecv" -6 -v -p "$port" -e incoming -o "$target" > "$out" 2>&1
  rc=$?
  set -e
  if [[ "$rc" -ne 23 ]] || ! rg -Fxq "Nothing to fetch." "$out"; then
    print -u2 "expected empty endpoint (exit 23, Nothing to fetch.); got exit $rc"
    return 1
  fi
}

start_a() {
  A_STARTS=$((A_STARTS + 1))
  "$BIN/dtnd" -c "$RUN/a.toml" --disable_nd > "$ART/a-daemon-$A_STARTS.log" 2>&1 &
  A_PID=$!
  wait_http "$PA" "$ART/a-ready.txt"
}

start_b() {
  B_STARTS=$((B_STARTS + 1))
  "$BIN/dtnd" -c "$RUN/b.toml" --disable_nd > "$ART/b-daemon-$B_STARTS.log" 2>&1 &
  B_PID=$!
  wait_http "$PB" "$ART/b-ready.txt"
}

stop_a() {
  kill "$A_PID"
  wait "$A_PID" 2>/dev/null || true
  A_PID=""
}

stop_b() {
  kill "$B_PID"
  wait "$B_PID" 2>/dev/null || true
  B_PID=""
}

fsync_file() {
  python3 - "$1" <<'PY'
import os
import sys
with open(sys.argv[1], "rb") as f:
    os.fsync(f.fileno())
PY
}

fsync_dir() {
  python3 - "$1" <<'PY'
import os
import sys
fd = os.open(sys.argv[1], os.O_RDONLY)
try:
    os.fsync(fd)
finally:
    os.close(fd)
PY
}

start_a
lsof -nP -p "$A_PID" -a -iTCP -sTCP:LISTEN > "$ART/a-listeners.txt"
rg -Fq "[::1]:$PA" "$ART/a-listeners.txt"
rg -Fq "[::1]:$CA" "$ART/a-listeners.txt"
if rg -q "0\.0\.0\.0|\*:" "$ART/a-listeners.txt"; then
  print -u2 "non-loopback listener detected"
  exit 1
fi

python3 - "$ART/queued-adu.bin" "$ART/live-adu.bin" "$ART/expiry-adu.bin" <<'PY'
from pathlib import Path
import sys
Path(sys.argv[1]).write_bytes(b"fn-bpv7\x00queued\xffadu\n")
Path(sys.argv[2]).write_bytes(b"fn-bpv7\x00live\xffadu\n")
Path(sys.argv[3]).write_bytes(b"fn-bpv7-expiry\n")
PY
shasum -a 256 "$ART"/*-adu.bin > "$ART/payload-sha256.txt"

# Node B is absent: submission creates a BP bundle that must survive A restart.
"$BIN/dtnsend" -6 -p "$PA" -r dtn://bp-b/incoming -l 300 "$ART/queued-adu.bin" \
  | tee "$ART/queued-submit.txt"
QUEUED_BID=$(awk '/^Bundle-Id:/ {print $2}' "$ART/queued-submit.txt")
[[ -n "$QUEUED_BID" ]]
wait_for_id "$PA" "$QUEUED_BID" "$ART/a-queued-before-restart.txt"
"$BIN/dtnquery" -6 -p "$PA" store > "$ART/a-queued-store-before-restart.txt"
stop_a
start_a
wait_for_id "$PA" "$QUEUED_BID" "$ART/a-queued-after-restart.txt"
"$BIN/dtnquery" -6 -p "$PA" store > "$ART/a-queued-store-after-restart.txt"

# Restoring B's configured static contact forwards the queued binary ADU.
start_b
lsof -nP -p "$B_PID" -a -iTCP -sTCP:LISTEN > "$ART/b-listeners.txt"
rg -Fq "[::1]:$PB" "$ART/b-listeners.txt"
rg -Fq "[::1]:$CB" "$ART/b-listeners.txt"
if rg -q "0\.0\.0\.0|\*:" "$ART/b-listeners.txt"; then
  print -u2 "non-loopback listener detected"
  exit 1
fi
wait_for_id "$PB" "$QUEUED_BID" "$ART/b-queued-after-contact.txt"

# The inbound application-agent queue is memory-only. Restart B before pop,
# then rediscover the retained bundle by inventory and retrieve it by BID.
stop_b
start_b
wait_for_id "$PB" "$QUEUED_BID" "$ART/b-queued-after-restart.txt"
assert_empty_endpoint "$PB" "$ART/endpoint-after-restart.txt" "$ART/unexpected-endpoint.adu"
# Safe prototype ingress: the BPA download is non-destructive.  It is copied
# to a temporary name, fsynced, atomically named into the inbox, and the inbox
# directory is fsynced before its explicit BPA delete.  This is a filesystem
# staging boundary only; it does not invoke fn validation or acceptance.
QUEUED_TMP="$RUN/inbox/.queued.adu.stage"
QUEUED_FINAL="$RUN/inbox/queued.adu"
"$BIN/dtnrecv" -6 -p "$PB" -b "$QUEUED_BID" -o "$QUEUED_TMP"
fsync_file "$QUEUED_TMP"
mv "$QUEUED_TMP" "$QUEUED_FINAL"
fsync_dir "$RUN/inbox"
cmp "$ART/queued-adu.bin" "$QUEUED_FINAL"
wait_for_id "$PB" "$QUEUED_BID" "$ART/b-queued-after-nondestructive-download.txt"
"$BIN/dtnrecv" -6 -p "$PB" -d "$QUEUED_BID" > "$ART/queued-explicit-delete.txt"
assert_absent "$PB" "$QUEUED_BID" "$ART/b-queued-after-explicit-delete.txt"

# A live contact forwards a second binary ADU. Re-inserting its exact BP
# bundle tests BPA duplicate suppression; endpoint pop demonstrates the
# destructive receive API that fn must not use before inbox staging.
"$BIN/dtnsend" -6 -p "$PA" -r dtn://bp-b/incoming -l 300 "$ART/live-adu.bin" \
  | tee "$ART/live-submit.txt"
LIVE_BID=$(awk '/^Bundle-Id:/ {print $2}' "$ART/live-submit.txt")
[[ -n "$LIVE_BID" ]]
wait_for_id "$PB" "$LIVE_BID" "$ART/b-live-before-delivery.txt"
"$BIN/dtnrecv" -6 -p "$PB" -b "$LIVE_BID" --raw -o "$ART/live.bundle"
curl --noproxy '*' -g -6 --fail --silent --show-error --data-binary "@$ART/live.bundle" \
  "http://[::1]:$PB/insert" > "$ART/live-duplicate-insert.txt"
"$BIN/dtnrecv" -6 -p "$PB" -e incoming -o "$ART/live-endpoint.adu"
cmp "$ART/live-adu.bin" "$ART/live-endpoint.adu"
assert_empty_endpoint "$PB" "$ART/duplicate-endpoint.txt" "$ART/unexpected-duplicate.adu"
assert_absent "$PB" "$LIVE_BID" "$ART/b-live-after-endpoint-pop.txt"

# BP lifetime is independent of fn retention. A short-lived disconnected
# attempt is removed from A before contact restoration, so no BPA event here
# can release or complete an fn work item.
stop_b
"$BIN/dtnsend" -6 -p "$PA" -r dtn://bp-b/incoming -l 1 "$ART/expiry-adu.bin" \
  | tee "$ART/expiry-submit.txt"
EXPIRY_BID=$(awk '/^Bundle-Id:/ {print $2}' "$ART/expiry-submit.txt")
[[ -n "$EXPIRY_BID" ]]
wait_for_id "$PA" "$EXPIRY_BID" "$ART/a-expiry-before-wait.txt"
sleep 3
assert_absent "$PA" "$EXPIRY_BID" "$ART/a-expiry-after-wait.txt"
start_b
assert_stays_absent "$PB" "$EXPIRY_BID" "$ART/b-expiry-after-contact.txt"

git -C "$REPO" rev-parse HEAD > "$ART/dtn7-rs-revision.txt"
"$BIN/dtnd" --version > "$ART/dtnd-version.txt"
"$BIN/dtnsend" --version > "$ART/dtnsend-version.txt"
shasum -a 256 "$SCRIPT" "$REPO/Cargo.lock" \
  "$REPO/core/dtn7/src/core/store/sled.rs" \
  "$REPO/core/dtn7/src/core/application_agent.rs" \
  "$REPO/core/dtn7/src/dtnd/httpd.rs" > "$ART/input-sha256.txt"
cat > "$ART/manifest.txt" <<EOF_MANIFEST
invocation=./run_two_node.sh
transport=tcp convergence layer over IPv6 loopback only
control=[::1]:$PA,[::1]:$PB
cla=[::1]:$CA,[::1]:$CB
db=sled
source_revision=$(cat "$ART/dtn7-rs-revision.txt")
queued_bid=$QUEUED_BID
live_bid=$LIVE_BID
expiry_bid=$EXPIRY_BID
EOF_MANIFEST
cat > "$ART/results.json" <<EOF_RESULTS
{
  "schema": 1,
  "loopback_only": true,
  "outbound_queue_disconnected": true,
  "outbound_clean_restart": true,
  "restored_contact": true,
  "inbound_inventory_after_restart": true,
  "endpoint_empty_after_restart": {"exit": 23, "text": "Nothing to fetch."},
  "non_destructive_download": true,
  "inbox_file_fsync": true,
  "inbox_directory_fsync_after_rename": true,
  "explicit_delete_after_stage": true,
  "live_binary_delivery": true,
  "duplicate_suppressed": true,
  "endpoint_pop_destructive": true,
  "expiry_absent_after_contact": {"samples": 20, "interval_ms": 100}
}
EOF_RESULTS
print "PASS artifact_dir=$ART queued_bid=$QUEUED_BID live_bid=$LIVE_BID expiry_bid=$EXPIRY_BID"
