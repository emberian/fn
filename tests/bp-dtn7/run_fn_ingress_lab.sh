#!/bin/zsh
# Loopback-only BPv7 transport to the actual isolated fn BP ingress host.
# This is a lab profile, not a receipt, deployment, or BPA qualification.
set -euo pipefail
export NO_PROXY='*'
export no_proxy='*'

SCRIPT=${0:A}
ROOT=${SCRIPT:h}
REPO=${DTN7_REPO:-"$ROOT/../../build/bp-dtn7/dtn7-rs"}
BIN="$REPO/target/release"
INGRESS_ROOT=${BP_INGRESS_ROOT:-"$ROOT/../.."}
WORKFLOW_JOURNAL=${BP_WORKFLOW_JOURNAL:-"$INGRESS_ROOT/tools/workflow_journal.py"}
RUN_BASE=${BP_FN_INGRESS_RUN_BASE:-"$INGRESS_ROOT/build/bp-dtn7-fn-ingress"}
[[ -x "$BIN/dtnd" && -f "$INGRESS_ROOT/tools/run_bp_ingress.py" && -f "$WORKFLOW_JOURNAL" ]]
mkdir -p "$RUN_BASE"
RUN=$(mktemp -d "$RUN_BASE/fn-bp-ingress.XXXXXX")
ART="$RUN/artifacts"
mkdir -p "$RUN/a" "$RUN/b" "$ART"
PA=32301
PB=32302
CA=32311
CB=32312
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
peers = ["tcp://[::1]:$CB/fn.lab"]
[endpoints]
local.0 = "outbox"
EOF_A
cat > "$RUN/b.toml" <<EOF_B
nodeid = "fn.lab"
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
local.0 = "inbox"
EOF_B

wait_http() {
  local port=$1 out=$2
  for _ in {1..100}; do
    if curl --noproxy '*' -g -6 --fail --silent --show-error --max-time 1 \
      "http://[::1]:$port/status/nodeid" > "$out" 2>/dev/null; then return 0; fi
    sleep 0.1
  done
  return 1
}
inventory() { "$BIN/dtnquery" -6 -p "$1" bundles > "$2"; }
wait_for_id() {
  local port=$1 bid=$2 out=$3
  for _ in {1..100}; do
    inventory "$port" "$out"
    if rg -Fq "$bid" "$out"; then return 0; fi
    sleep 0.1
  done
  return 1
}
assert_loopback_listeners() {
  local pid=$1 control=$2 cla=$3 out=$4
  lsof -nP -p "$pid" -a -iTCP -sTCP:LISTEN > "$out"
  rg -Fq "[::1]:$control" "$out"
  rg -Fq "[::1]:$cla" "$out"
  if rg -q "0\\.0\\.0\\.0|\\*:" "$out"; then print -u2 "non-loopback listener"; return 1; fi
}
start_a() {
  A_STARTS=$((A_STARTS + 1)); "$BIN/dtnd" -c "$RUN/a.toml" --disable_nd > "$ART/a-$A_STARTS.log" 2>&1 &
  A_PID=$!; wait_http "$PA" "$ART/a-ready.txt"
}
start_b() {
  B_STARTS=$((B_STARTS + 1)); "$BIN/dtnd" -c "$RUN/b.toml" --disable_nd > "$ART/b-$B_STARTS.log" 2>&1 &
  B_PID=$!; wait_http "$PB" "$ART/b-ready.txt"
}
stop_b() { kill "$B_PID"; wait "$B_PID" 2>/dev/null || true; B_PID=""; }

start_a
assert_loopback_listeners "$A_PID" "$PA" "$CA" "$ART/a-listeners.txt"
cat > "$ART/legacy-article.adu" <<'EOF_ADU'
Message-ID: <bp-loopback@fn.example>
Newsgroups: fn.letters
Subject: BP loopback ingress lab
From: bp sender <sender@bp.example>
Date: Thu, 01 Jan 2026 00:00:00 +0000

Exact legacy article ADU over BPv7.
EOF_ADU
# zsh heredoc uses literal CRLF only through this conversion; the original ADU
# is retained byte-for-byte and checked by the real Store lookup.
python3 - "$ART/legacy-article.adu" <<'PY'
from pathlib import Path
p = Path(__import__('sys').argv[1])
p.write_bytes(p.read_bytes().replace(b'\\r\\n', b'\r\n'))
PY
shasum -a 256 "$ART/legacy-article.adu" > "$ART/legacy-article.sha256"
"$BIN/dtnsend" -6 -p "$PA" -r dtn://fn.lab/inbox -l 300 "$ART/legacy-article.adu" | tee "$ART/submit.txt"
BID=$(awk '/^Bundle-Id:/ {print $2}' "$ART/submit.txt")
[[ -n "$BID" ]]
wait_for_id "$PA" "$BID" "$ART/a-queued.txt"

start_b
assert_loopback_listeners "$B_PID" "$PB" "$CB" "$ART/b-listeners-first.txt"
wait_for_id "$PB" "$BID" "$ART/b-before-restart.txt"
# Receiver restart happens before ingress.  Inventory discovery, not endpoint
# pop, proves that the BPA bundle remains obtainable after that restart.
stop_b
start_b
assert_loopback_listeners "$B_PID" "$PB" "$CB" "$ART/b-listeners-restart.txt"
wait_for_id "$PB" "$BID" "$ART/b-after-restart.txt"
SOURCE_EID=${BID%/*}
python3 "$ROOT/bp_fn_ingress_driver.py" \
  --ingress-root "$INGRESS_ROOT" --workflow-journal "$WORKFLOW_JOURNAL" \
  --store "$RUN/store" --journal "$RUN/workflow" --bpa-bin "$BIN" --bpa-port "$PB" \
  --bid "$BID" --expected-adu "$ART/legacy-article.adu" \
  --expected-msgid '<bp-loopback@fn.example>' --destination dtn://fn.lab/inbox \
  --source-eid "$SOURCE_EID" --lifetime 300 --artifact-dir "$ART" --phase accept \
  | tee "$ART/fn-ingress-accept.txt"
# Retry transports the byte-identical ADU in a distinct real BPA bundle.  This
# is the relevant fn duplicate boundary: BPA BIDs are provenance, while ACL2
# recognizes the recovered exact article identity and must not allocate again.
"$BIN/dtnsend" -6 -p "$PA" -r dtn://fn.lab/inbox -l 300 "$ART/legacy-article.adu" \
  | tee "$ART/duplicate-submit.txt"
DUPLICATE_BID=$(awk '/^Bundle-Id:/ {print $2}' "$ART/duplicate-submit.txt")
[[ -n "$DUPLICATE_BID" && "$DUPLICATE_BID" != "$BID" ]]
wait_for_id "$PB" "$DUPLICATE_BID" "$ART/b-before-duplicate.txt"
python3 "$ROOT/bp_fn_ingress_driver.py" \
  --ingress-root "$INGRESS_ROOT" --workflow-journal "$WORKFLOW_JOURNAL" \
  --store "$RUN/store" --journal "$RUN/workflow" --bpa-bin "$BIN" --bpa-port "$PB" \
  --bid "$DUPLICATE_BID" --expected-adu "$ART/legacy-article.adu" \
  --expected-msgid '<bp-loopback@fn.example>' --destination dtn://fn.lab/inbox \
  --source-eid "$SOURCE_EID" --lifetime 300 --artifact-dir "$ART" --phase duplicate \
  --baseline "$ART/fn-ingress-accept.json" | tee "$ART/fn-ingress-duplicate.txt"
git -C "$REPO" rev-parse HEAD > "$ART/dtn7-rs-revision.txt"
"$BIN/dtnd" --version > "$ART/dtnd-version.txt"
"$BIN/dtnsend" --version > "$ART/dtnsend-version.txt"
"$BIN/dtnrecv" --version > "$ART/dtnrecv-version.txt"
"$BIN/dtnquery" --version > "$ART/dtnquery-version.txt"
cargo --version > "$ART/cargo-version.txt"
python3 --version > "$ART/python-version.txt"
shasum -a 256 "$SCRIPT" "$ROOT/bp_fn_ingress_driver.py" \
  "$INGRESS_ROOT/tools/run_bp_ingress.py" "$INGRESS_ROOT/host/bp-ingress-host.lisp" \
  "$WORKFLOW_JOURNAL" > "$ART/input-sha256.txt"
cat > "$ART/manifest.txt" <<EOF_MANIFEST
invocation=./run_fn_ingress_lab.sh
transport=tcp convergence layer over IPv6 loopback only
control=[::1]:$PA,[::1]:$PB
cla=[::1]:$CA,[::1]:$CB
source_revision=$(cat "$ART/dtn7-rs-revision.txt")
bid=$BID
duplicate_bid=$DUPLICATE_BID
source_eid=$SOURCE_EID
destination=dtn://fn.lab/inbox
lifetime=300
receiver_restart_before_ingress=true
duplicate_transport_bid_distinct=true
endpoint_pop_used=false
receipt_emitted=false
EOF_MANIFEST
python3 - "$ART" "$BID" "$DUPLICATE_BID" <<'PY'
import json
import sys
from pathlib import Path

art = Path(sys.argv[1])
accepted = json.loads((art / "fn-ingress-accept.json").read_text())
duplicate = json.loads((art / "fn-ingress-duplicate.json").read_text())
first, second = accepted["state"], duplicate["state"]
checks = {
    "receiver_restart_before_first_ingress": True,
    "distinct_real_transport_bids": sys.argv[2] != sys.argv[3],
    "first_acl2_outcome_accepted": accepted["outcome"] == "accepted",
    "second_acl2_outcome_duplicate": duplicate["outcome"] == "duplicate",
    "same_article_record_count": first["records"] == second["records"] == 1,
    "same_article_count": first["articles"] == second["articles"] == 1,
    "same_retention_pin_count": first["pins"] == second["pins"] == 1,
    "same_exact_adu_digest": first["payload_sha256"] == second["payload_sha256"],
    "endpoint_pop_used": False,
    "receipt_emitted": False,
}
assert all(v for k, v in checks.items() if k not in ("endpoint_pop_used", "receipt_emitted")), checks
assert not checks["endpoint_pop_used"] and not checks["receipt_emitted"]
versions = {name: (art / name).read_text().strip() for name in (
    "dtnd-version.txt", "dtnsend-version.txt", "dtnrecv-version.txt",
    "dtnquery-version.txt", "cargo-version.txt", "python-version.txt")}
sources = {}
for row in (art / "input-sha256.txt").read_text().splitlines():
    digest, path = row.split(maxsplit=1)
    sources[path] = digest
summary = {
    "schema": 1,
    "status": "passed",
    "commands": ["./run_fn_ingress_lab.sh", "cargo build --release --locked"],
    "dtn7_revision": (art / "dtn7-rs-revision.txt").read_text().strip(),
    "bids": {"accepted": sys.argv[2], "duplicate_transport": sys.argv[3]},
    "accepted": accepted,
    "duplicate": duplicate,
    "assertions": checks,
    "versions": versions,
    "sources_sha256": sources,
    "limitations": [
        "The second operation is a new BP bundle containing byte-identical legacy article bytes; BPA BID is transport provenance, not article identity.",
        "The exposed dtn7-rs /insert endpoint is an outbound send API, not an inbound raw-bundle injection interface.",
        "The BPA endpoint dequeue/pop API was not used; no application receipt is created or implied.",
        "This is a loopback lab profile and does not establish power-loss durability, authenticated transport, or receipt semantics.",
    ],
}
(art / "fn-ingress-evidence.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
PY
print "PASS artifact_dir=$ART bid=$BID"
