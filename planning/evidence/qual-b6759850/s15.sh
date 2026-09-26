#!/bin/sh
# qual-b6759850 section 15 native rows not covered by a test module:
# the N=300 reclaim lifecycle with every cut, and the tight store (budget exhaustion and recovery).
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
R=$S/s15; mkdir -p $R
cd $S/tree
DEV=$I/fn-host-developer
rm -rf $R/n300; /usr/bin/time -v python3 tests/reclaim_lifecycle_native.py $DEV $R/n300 300 512 67108864 --cuts > $R/n300.jsonl 2> $R/n300.err; echo "n300 rc=$?" >> $R/rcs
rm -rf $R/tight; /usr/bin/time -v python3 tests/reclaim_lifecycle_native.py $DEV $R/tight 0 1024 300000 --headroom-only > $R/tight.jsonl 2> $R/tight.err; echo "tight rc=$?" >> $R/rcs
python3 $S/probe_budget.py > $R/probe-budget.log 2>&1; echo "probe-budget rc=$?" >> $R/rcs
echo S15-DONE
