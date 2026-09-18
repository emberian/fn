#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=${DTN7_REPO:?set DTN7_REPO to the pinned dtn7-rs checkout}
PIN=4daf02d7ea927e9293753b2a5c4497457f6e5a40
[ "$(git -C "$REPO" rev-parse HEAD)" = "$PIN" ]
cp "$HERE/../../tools/bpa_payload_extract.rs" "$REPO/core/dtn7/src/bin/fn_bpa_payload_extract.rs"
(
  cd "$REPO"
  cargo build --release --locked -p dtn7 --bin fn_bpa_payload_extract
)
printf '%s\n' "$REPO/target/release/fn_bpa_payload_extract"
