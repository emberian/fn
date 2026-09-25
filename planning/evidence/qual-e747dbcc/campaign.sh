#!/bin/sh
# qual-e747dbcc campaign: the 10 compaction cuts and 25 cuts (one run), the
# marker cuts through both entries, the ACL2 differential, the NNTP probe, the
# production external-kill run with one seed, the D25 review matrix.
set -u
S=/tank/fn/scratch/qual-e747dbcc/campaign
GT=/tank/fn/gates/qual-e747dbcc-20260925
G=$GT/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$GT
export PYTHONDONTWRITEBYTECODE=1
mkdir -p $S
cd /tank/fn/scratch/qual-e747dbcc/ctree
date -u +%FT%TZ > $S/run.start
ss -ltn > $S/ss-before.txt
( cd $G && sha256sum fn-host fn-host.core fn-host-developer fn-host-developer.core ) > $S/image.sha256
sha256sum tests/campaign/native_operator_campaign.py tests/campaign/native_nntp_post_probe.py tests/campaign/native_production_kill.py tests/campaign/native_cuts.py tests/campaign/test_native_operator_campaign.py tests/test_native_crash_model.py tests/test_native_history_marker.py ../marker_cuts.py ../d25b_matrix.py > $S/driver.sha256
echo "image-gated $(date -u +%T)"
FN_NATIVE_IMAGES=$G python3 -m unittest -v tests.campaign.test_native_operator_campaign > $S/image-gated-test.log 2>&1; echo "rc=$?" >> $S/image-gated-test.log
echo "campaign $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_operator_campaign --images $G --work $S/work --out $S/campaign.json > $S/campaign.log 2>&1; echo "rc=$?" >> $S/campaign.log
echo "marker-cuts $(date -u +%T)"
PYTHONPATH=. /usr/bin/time -v python3 ../marker_cuts.py $G/fn-host-developer $S/marker-work $S/marker-cuts.json > $S/marker-cuts.log 2>&1; echo "rc=$?" >> $S/marker-cuts.log
echo "probe $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work --out $S/nntp-probe.json > $S/nntp-probe.log 2>&1; echo "rc=$?" >> $S/nntp-probe.log
echo "crash-model $(date -u +%T)"
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_CRASH_HOST=$G/fn-host-developer /usr/bin/time -v python3 -m unittest -v tests.test_native_crash_model > $S/crash-model.log 2>&1; echo "rc=$?" >> $S/crash-model.log
echo "d25-matrix $(date -u +%T)"
if ss -ltn | grep -q ':11396 '; then echo "port 11396 busy" > $S/d25-matrix.log; else
/usr/bin/time -v python3 ../d25b_matrix.py $G/fn-host-developer /tank/fn/scratch/d25-dup/img/build/fn-host-developer $S/d25-work 11396 /tank/fn/scratch/qual-e747dbcc/bin/test-openssl > $S/d25-matrix.log 2>&1; echo "rc=$?" >> $S/d25-matrix.log; fi
echo "prodkill $(date -u +%T)"
/usr/bin/time -v python3 -m tests.campaign.native_production_kill run --image $G/fn-host --work $S/pk-work --out $S/pk-run.json --seed 3 --kills 80 --concurrent 10 > $S/pk-run.log 2>&1; echo "rc=$?" >> $S/pk-run.log
python3 -m tests.campaign.native_production_kill judge $S/pk-run.json > $S/pk-judged.md 2>&1; echo "judge rc=$?" >> $S/pk-judged.md
ss -ltn > $S/ss-after.txt
date -u +%FT%TZ > $S/run.end
echo "done $(date -u +%T)"
