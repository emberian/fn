#!/bin/sh
# Build the exact pinned upstream revision in a fresh supplied directory, then
# run the loopback-only harness. No source, listeners, or logs are installed.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
WORK=${1:?usage: bootstrap.sh EMPTY_WORK_DIRECTORY}
PIN=4daf02d7ea927e9293753b2a5c4497457f6e5a40
REMOTE=https://github.com/dtn7/dtn7-rs
if [ -e "$WORK" ] && [ "$(find "$WORK" -mindepth 1 -maxdepth 1 -print -quit)" ]; then
  echo "work directory must be absent or empty: $WORK" >&2
  exit 2
fi
mkdir -p "$WORK"
git clone "$REMOTE" "$WORK/dtn7-rs"
git -C "$WORK/dtn7-rs" checkout --detach "$PIN"
[ "$(git -C "$WORK/dtn7-rs" rev-parse HEAD)" = "$PIN" ]
(
  cd "$WORK/dtn7-rs"
  cargo build --release --locked
)
DTN7_REPO="$WORK/dtn7-rs" BP_RUN_BASE="$WORK/runs" "$HERE/run_two_node.sh"
LATEST=$(ls -dt "$WORK"/runs/bpv7.* | head -n 1)
python3 "$HERE/record_evidence.py" \
  --repo "$WORK/dtn7-rs" --artifact "$LATEST/artifacts" \
  --harness "$HERE/run_two_node.sh" --output "$WORK/evidence.json"
printf '%s\n' "PASS evidence=$WORK/evidence.json"
