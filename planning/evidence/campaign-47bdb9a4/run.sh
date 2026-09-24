#!/bin/sh
set -u
S=/tank/fn/scratch/campaign-47bdb9a4
GT=/tank/fn/gates/qual-47bdb9a4-20260924
G=$GT/build/images/47bdb9a4
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$GT
export PYTHONDONTWRITEBYTECODE=1
cd $S/tree
date -u +%FT%TZ > $S/run.start
ss -ltn > $S/ss-before.txt
( cd $G && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
( cd $G && sha256sum fn-host fn-host.core fn-host-developer fn-host-developer.core ) > $S/image.sha256
sha256sum tests/campaign/native_operator_campaign.py tests/campaign/native_nntp_post_probe.py tests/campaign/native_production_kill.py tests/campaign/native_cuts.py tests/campaign/test_native_operator_campaign.py tests/test_native_crash_model.py > $S/driver.sha256
echo "image-gated $(date -u +%T)"
FN_NATIVE_IMAGES=$G python3 -m unittest -v tests.campaign.test_native_operator_campaign > $S/image-gated-test.log 2>&1; echo "rc=$?" >> $S/image-gated-test.log
echo "campaign1 $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_operator_campaign --images $G --work $S/work --out $S/campaign.json > $S/campaign.log 2>&1; echo "rc=$?" >> $S/campaign.log
echo "campaign2 $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_operator_campaign --images $G --work $S/work2 --out $S/campaign-repeat.json > $S/campaign-repeat.log 2>&1; echo "rc=$?" >> $S/campaign-repeat.log
echo "probe1 $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work --out $S/nntp-probe.json > $S/nntp-probe.log 2>&1; echo "rc=$?" >> $S/nntp-probe.log
echo "probe2 $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work2 --out $S/nntp-probe-repeat.json > $S/nntp-probe-repeat.log 2>&1; echo "rc=$?" >> $S/nntp-probe-repeat.log
echo "crash-model $(date -u +%T)"
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_CRASH_HOST=$G/fn-host-developer /usr/bin/time -v python3 -m unittest -v tests.test_native_crash_model > $S/crash-model.log 2>&1; echo "rc=$?" >> $S/crash-model.log
echo "prodkill $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_production_kill run --image $G/fn-host --work $S/pk-work --out $S/pk-run.json --seed 3 --kills 80 --concurrent 10 > $S/pk-run.log 2>&1; echo "rc=$?" >> $S/pk-run.log
python3 -m tests.campaign.native_production_kill judge $S/pk-run.json > $S/pk-judged.md 2>&1; echo "judge rc=$?" >> $S/pk-judged.md
ss -ltn > $S/ss-after.txt
date -u +%FT%TZ > $S/run.end
echo "done $(date -u +%T)"
