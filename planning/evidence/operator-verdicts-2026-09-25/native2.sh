#!/bin/sh
# operator-verdicts native runs on the images built from d265fddd.
T=/tank/fn/scratch/operator-verdicts/tree2; L=/tank/fn/scratch/operator-verdicts/logs2
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_SOURCE_ROOT=$T PYTHONDONTWRITEBYTECODE=1
date -u +start=%FT%TZ
echo == all operator-verdict cases, format-7 start from c3420013
FN_OLD_NATIVE_HOST=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host FN_NATIVE_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_operator_verdicts > $L/native-operator-verdicts-2.log 2>&1; echo rc=$?
echo == PKT-103 oversize and transit 437 on this image
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_owner.NativeOwnerTests.test_article_over_the_body_limit_is_refused_and_the_owner_survives > $L/native-owner-oversize-2.log 2>&1; echo rc=$?
FN_NATIVE_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_control_filing > $L/native-control-filing-2.log 2>&1; echo rc=$?
date -u +end=%FT%TZ
cd $L && sha256sum native-*.log image.sha256
