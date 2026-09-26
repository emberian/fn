#!/bin/sh
# qual-b6759850 fact 1a: a checkpoint at the scale profile's largest admitted
# article times K/2, published and reopened; then the live store copy's own checkpoint.
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
C=$S/ckpt; mkdir -p $C
cd $S/tree
IMG=$I/fn-host
python3 $S/probe_maxart.py $IMG $C/maxart > $C/maxart.log 2>&1; echo "rc=$?" >> $C/maxart.log
A=$(sed -n 's/^LARGEST-ADMITTED \([0-9]*\) .*/\1/p' $C/maxart.log)
echo "largest admitted $A" > $C/summary.txt
# K/2 for the scale profile: read max-open-suffix from its status
K=$(grep -o 'max-open-suffix=[0-9]*' $C/maxart.log | head -1 | cut -d= -f2)
N=$(( K / 2 ))
echo "K=$K N=$N A=$A" >> $C/summary.txt
/usr/bin/time -v python3 tools/rep_measure.py --image $IMG --work $C/n$N --articles $N --octets $A --profile scale --samples 32 --readers 3 --json $C/n$N.json > $C/rep.log 2>&1; echo "rc=$?" >> $C/rep.log
CF=$C/n$N/fn.toml
ls -la $C/n$N/store/ > $C/store-ls.txt 2>&1
$IMG --fn operator $CF status > $C/status-after.txt 2>&1; echo "rc=$?" >> $C/status-after.txt
# the same store once more: stop-free offline status twice (open from the checkpoint), then an owner open with timing
s=$(date +%s.%N); $IMG --fn operator $CF status > $C/status-again.txt 2>&1; echo "rc=$? wall=$(echo "$(date +%s.%N) - $s" | bc)" >> $C/status-again.txt
sha256sum $C/n$N/store/store-checkpoint.fnsc > $C/checkpoint.sha256 2>&1
# the live store copy's own profile: store checkpoint and reopen
rm -rf $C/live; mkdir -p $C/live; cp -a /tank/fn/node/store $C/live/store; rm -f $C/live/store/control.sock
P=$(python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1])')
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' $C/live/store $P $C/live/control.sock > $C/live/fn.toml
{ $IMG --fn operator $C/live/fn.toml status; echo "status rc=$?"
  $IMG --fn operator $C/live/fn.toml store checkpoint; echo "checkpoint rc=$?"
  $IMG --fn operator $C/live/fn.toml status; echo "status-after rc=$?"
  ls -la $C/live/store; } > $C/live.log 2>&1
python3 - $IMG $C/live/fn.toml >> $C/live.log 2>&1 <<'PY2'
import os, sys, time
sys.path.insert(0, "/tank/fn/scratch/qual-b6759850/tree/tools"); sys.path.insert(0, "/tank/fn/scratch/qual-b6759850/tree")
import rep_measure as rm
from pathlib import Path
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
p, secs, err = rm.start_owner(sys.argv[1], Path(sys.argv[2]), env, Path(sys.argv[2]).parent / "owner.stderr")
print("owner reopen of the live copy from its checkpoint: LISTENING after %.2f s" % secs)
rm.stop_owner(p, err)
print("owner exit", p.returncode)
PY2
$IMG --fn operator $C/live/fn.toml status >> $C/live.log 2>&1; echo "status-after-owner rc=$?" >> $C/live.log
echo CKPT-DONE
