#!/bin/sh
set -u
. /tank/fn/scratch/probe-tables/env.sh
date -u +%FT%TZ > $S/run.start
( cd $G && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
python3 -m unittest -v tests.test_native_nntp_post_probe > $S/probe-unit.log 2>&1; echo "rc=$?" >> $S/probe-unit.log
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work --out $S/nntp-probe.json > $S/nntp-probe.log 2>&1; echo "rc=$?" >> $S/nntp-probe.log
FN_NATIVE_CRASH_HOST=$G/fn-host-developer /usr/bin/time -v python3 -m unittest -v tests.test_native_crash_model > $S/crash-model.log 2>&1; echo "rc=$?" >> $S/crash-model.log
date -u +%FT%TZ > $S/run.end
( cd $S/tree && sha256sum tests/campaign/native_nntp_post_probe.py tests/campaign/native_cuts.py tests/test_native_crash_model.py tests/test_native_nntp_post_probe.py host/native/io.lisp ) > $S/tree.sha256
tar czf $S/owner-logs.tgz -C $S probe-work --wildcards '*/owner-*.err' 2>/dev/null
gzip -kf $S/nntp-probe.json
cd $S && sha256sum run.sh image-check.log probe-unit.log nntp-probe.log nntp-probe.json nntp-probe.json.gz crash-model.log owner-logs.tgz tree.sha256 > $S/SHA256SUMS
echo done
