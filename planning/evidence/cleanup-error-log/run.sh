#!/bin/sh
set -u
S=/tank/fn/scratch/cleanup-error-log
G=$S/images/03bdd1054fa6dfc4d57fe162e3a07fc5c9a405e0
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$S/tree
export PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
cd $S/tree
date -u +%FT%TZ > $S/run.start
( cd $G && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
python3 -m unittest -v tests.test_native_nntp_post_probe > $S/probe-unit.log 2>&1; echo "rc=$?" >> $S/probe-unit.log
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G --work $S/probe-work --out $S/nntp-probe.json > $S/nntp-probe.log 2>&1; echo "rc=$?" >> $S/nntp-probe.log
date -u +%FT%TZ > $S/run.end
tar czf $S/owner-logs.tgz -C $S probe-work --wildcards '*/owner-*.err' 2>/dev/null
gzip -kf $S/nntp-probe.json
cd $S && sha256sum run.sh build.sh image-check.log probe-unit.log nntp-probe.log nntp-probe.json nntp-probe.json.gz owner-logs.tgz > $S/SHA256SUMS
echo done
