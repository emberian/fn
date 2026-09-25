#!/bin/sh
# spike-storage: functional test of release/reclaim/chain on a small store.  usage: test-small.sh SRC-WORK TAG
set -u
S=/tank/fn/scratch/spike-storage; I=$S/tree/build/fn-host-developer
. /tank/fn/scratch/bounds-p3/env.sh; export ACL2_CUSTOMIZATION=NONE PYTHONPATH=$S/tree/tools
W=/dev/shm/spike-storage-$2; rm -rf $W; cp -a $1 $W
port=$(python3 -c "import sys; sys.path.insert(0,'$S/tree/tools'); import msgid_measure as m; print(m.free_port())")
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' $W/store $port $W/control.sock > $W/fn.toml
st() { echo "== $*"; $I --fn spike-store $W/store "$@" 2>&1 | tail -4; echo "rc=$?"; }
op() { echo "== operator $*"; $I --fn operator $W/fn.toml "$@" 2>&1 | grep -E "^open=|^transactions|^checkpoint|error|refus" ; }
st history-digest
st release --oldest 100
st reclaim --verify --dry-run
st reclaim --verify
st history-digest
op status
python3 $S/d25.py $S/tree $I $W 5
st compact-chain --link-events 64
st history-digest
op status
op store checkpoint
op status
st release --oldest 50
st reclaim --verify
st history-digest
op status
python3 $S/d25.py $S/tree $I $W 120
du -sk $W/store $W/store/*
echo "== phase 2: reclaim through the chain with a checkpoint"
st release --oldest 60
st reclaim --verify
st history-digest
op status
python3 $S/d25.py $S/tree $I $W 150
echo "== phase 3: process-death cuts (exit 137 at the named point), then reopen and resume"
for cut in link-staged link-linked chain-selection-staged chain-selection-replaced chain-selected chain-reclaim-unlink; do
  W2=/dev/shm/spike-storage-$2-cut; rm -rf $W2; cp -a $1 $W2
  FN_SPIKE_CUT=$cut $I --fn spike-store $W2/store compact-chain --link-events 64 >/dev/null 2>&1; echo "cut=$cut rc=$?"
  $I --fn spike-store $W2/store history-digest 2>&1 | cut -c1-150
  $I --fn spike-store $W2/store compact-chain --link-events 64 2>&1 | cut -c1-100
  $I --fn spike-store $W2/store chain-retire 2>&1 | cut -c1-100
  $I --fn spike-store $W2/store history-digest 2>&1 | cut -c1-150
done
for cut in reclaim-record-staged reclaim-record-replaced reclaim-history-done; do
  W2=/dev/shm/spike-storage-$2-cut; rm -rf $W2; cp -a $1 $W2
  $I --fn spike-store $W2/store release --oldest 20 >/dev/null 2>&1
  FN_SPIKE_CUT=$cut $I --fn spike-store $W2/store reclaim >/dev/null 2>&1; echo "cut=$cut rc=$?"
  $I --fn spike-store $W2/store history-digest 2>&1 | cut -c1-150
  $I --fn spike-store $W2/store reclaim --verify 2>&1 | grep -E "verify|done|nothing" | cut -c1-200
  $I --fn spike-store $W2/store history-digest 2>&1 | cut -c1-150
done
