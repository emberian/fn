#!/bin/sh
# operator-verdicts native runs on the images built from the lane commit.
T=/tank/fn/scratch/operator-verdicts/tree; L=/tank/fn/scratch/operator-verdicts/logs
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_SOURCE_ROOT=$T PYTHONDONTWRITEBYTECODE=1
date -u +start=%FT%TZ
echo == PKT-103 native owner oversize
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_owner.NativeOwnerTests.test_article_over_the_body_limit_is_refused_and_the_owner_survives > $L/native-owner-oversize.log 2>&1; echo rc=$?
echo == PKT-104 transit 437
FN_NATIVE_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_control_filing.NativeControlFilingTests.test_transit_ihave tests.test_native_control_filing.NativeControlFilingTests.test_served_post > $L/native-transit-437.log 2>&1; echo rc=$?
echo == PKT-095 PKT-102 PKT-103-init
FN_NATIVE_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_operator_verdicts > $L/native-operator-verdicts.log 2>&1; echo rc=$?
echo == native owner module
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest tests.test_native_owner > $L/native-owner-all.log 2>&1; echo rc=$?
date -u +end=%FT%TZ
cd $L && sha256sum *.log
