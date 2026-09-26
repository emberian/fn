#!/bin/sh
# qual-69046a76 section 15 native rows not covered by a module: the N=300 reclaim lifecycle
# with every cut, the tight store, the admission count, the count exhaustion, the small disk;
# then the kept 20,000-record chain fixture's served-identical test (never rebuilt).
set -u
. /tank/fn/scratch/qual-69046a76/env.sh
R=$S/s15; mkdir -p $R
cd $S/tree
DEV=$I/fn-host-developer
rm -rf $R/n300; /usr/bin/time -v python3 tests/reclaim_lifecycle_native.py $DEV $R/n300 300 512 67108864 --cuts > $R/n300.jsonl 2> $R/n300.err; echo "n300 rc=$?" >> $R/rcs
rm -rf $R/tight; /usr/bin/time -v python3 tests/reclaim_lifecycle_native.py $DEV $R/tight 0 1024 300000 --headroom-only > $R/tight.jsonl 2> $R/tight.err; echo "tight rc=$?" >> $R/rcs
python3 $S/probe_budget.py > $R/probe-budget.log 2>&1; echo "probe-budget rc=$?" >> $R/rcs
python3 $S/probe_count.py > $R/probe-count.log 2>&1; echo "probe-count rc=$?" >> $R/rcs
sh $S/probe_smalldisk.sh > $R/smalldisk.log 2>&1; echo "smalldisk rc=$?" >> $R/rcs
touch $S/done.s15a
FX=/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c
if [ -d $FX ]; then
  { echo "# chain-20000 fixture $FX start $(date -u +%FT%TZ)"; s=$(date +%s)
    FN_P5_FIXTURE=$FX FN_NATIVE_HOST=$DEV timeout 5400 python3 -m unittest -v tests.test_native_pack_chain.NativePackChainTests.test_scale_store_compacts_into_a_chain 2>&1
    echo "# rc=$? wall=$(( $(date +%s) - s ))"; } > $R/chain20000.log 2>&1
fi
echo S15-DONE; touch $S/done.s15
