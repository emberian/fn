#!/bin/sh
# Run one tests/fuzz_nntp.py campaign on hbox against images tools/hbox_native.sh built.
#
#   tools/fuzz_nntp_hbox.sh TREE CAMPAIGN [fuzz_nntp.py options...]
#
# TREE is the hbox_native scratch directory (e.g.
# /tank/fn/scratch/fuzz-nntp/native-fz1): its tree/build/fn-host-developer
# and tree/build/fn-host are the images.  This copies tests/fuzz_nntp.py
# from this worktree into TREE/tree/tests/, runs the campaign there under
# `systemd-run --user --scope -p MemoryMax=16G` (the owner and every model
# process inside the one cgroup; SWARM_MEM_MAX-style override: FUZZ_MEM),
# bounded by `timeout` at the campaign's --seconds plus 20 minutes, writing
# its log and findings to TREE/fuzz/CAMPAIGN-<UTC>/, and copies that
# directory back to build/fuzz-nntp/ here.  It starts and stops only the
# processes of its own scope; it never touches /tank/fn/node.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
HOST=${FN_HBOX:-hbox}
MEM=${FUZZ_MEM:-16G}
[ $# -ge 2 ] || { sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2; }
TREE=$1; CAMPAIGN=$2; shift 2
SECONDS_ARG=600
prev=
for word in "$@"; do
    [ "$prev" = "--seconds" ] && SECONDS_ARG=${word%.*}
    prev=$word
done
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
OUT=$TREE/fuzz/$CAMPAIGN-$STAMP
scp -q "$HERE/tests/fuzz_nntp.py" "$HOST:$TREE/tree/tests/fuzz_nntp.py"
QUOTED=
for word in "$@"; do QUOTED="$QUOTED '$word'"; done
ssh "$HOST" "S=$(dirname $TREE)/s$(date +%s); mkdir -p '$OUT' \$S && cd '$TREE/tree' && \
  FN_NATIVE_DEVELOPER_HOST='$TREE/tree/build/fn-host-developer' FN_NATIVE_HOST='$TREE/tree/build/fn-host' \
  timeout $((SECONDS_ARG + 1200)) systemd-run --user --scope --quiet -p MemoryMax=$MEM -p MemorySwapMax=0 \
  nice -n 10 python3 tests/fuzz_nntp.py $CAMPAIGN --out '$OUT' --scratch \$S $QUOTED \
  > '$OUT/campaign.log' 2>&1; echo \$? > '$OUT/exit'; rm -rf \$S" || true
mkdir -p "$HERE/build/fuzz-nntp"
rsync -a "$HOST:$OUT" "$HERE/build/fuzz-nntp/"
echo "== $CAMPAIGN exit $(cat "$HERE/build/fuzz-nntp/$(basename "$OUT")/exit") -> build/fuzz-nntp/$(basename "$OUT")"
tail -n 25 "$HERE/build/fuzz-nntp/$(basename "$OUT")/campaign.log"
