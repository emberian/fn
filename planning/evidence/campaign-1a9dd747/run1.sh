#!/bin/sh
set -u
S=/tank/fn/scratch/campaign-1a9dd747
G=/tank/fn/gates/qual-1a9dd747-20260924/build
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd $S/tree
date -u +%FT%TZ > $S/run1.start
( sha256sum $G/fn-host $G/fn-host.core $G/fn-host-developer $G/fn-host-developer.core ) > $S/image.sha256
FN_NATIVE_IMAGES=$G python3 -m unittest -v tests.campaign.test_native_operator_campaign > $S/image-gated-test.log 2>&1; echo "rc=$?" >> $S/image-gated-test.log
/usr/bin/time -v python3 -m tests.campaign.native_operator_campaign --images $G --work $S/work --out $S/campaign.json > $S/campaign.log 2>&1; echo "rc=$?" >> $S/campaign.log
/usr/bin/time -v python3 -m tests.campaign.native_operator_campaign --images $G --work $S/work2 --out $S/campaign-repeat.json > $S/campaign-repeat.log 2>&1; echo "rc=$?" >> $S/campaign-repeat.log
date -u +%FT%TZ > $S/run1.end
