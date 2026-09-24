#!/bin/sh
set -u
S=/tank/fn/scratch/campaign-production-kill
G=/tank/fn/gates/qual-1a9dd747-20260924/build
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd $S/tree
date -u +%FT%TZ > $S/run.start
sha256sum $G/fn-host $G/fn-host.core > $S/image.sha256
sha256sum tests/campaign/native_production_kill.py tests/campaign/native_operator_campaign.py > $S/driver.sha256
for n in 1 2; do
  /usr/bin/time -v python3 -m tests.campaign.native_production_kill run --image $G/fn-host --work $S/work$n --out $S/run$n.json --seed $n --kills 80 --concurrent 12 > $S/run$n.log 2>&1; echo "rc=$?" >> $S/run$n.log
  python3 -m tests.campaign.native_production_kill judge $S/run$n.json > $S/judged$n.md 2>&1; echo "judge rc=$?" >> $S/judged$n.md
done
date -u +%FT%TZ > $S/run.end
