#!/bin/sh
S=/tank/fn/scratch/signed-path; T=$S/after-tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib PYTHONDONTWRITEBYTECODE=1
date -u +start=%FT%TZ
echo == prof after; sh $S/run-prof.sh after $T $T/build/fn-host-developer-prof --sign-prof-seconds 5 > $S/prof-after.log 2>&1; echo rc=$?
echo == refusal; rm -rf $S/work-refusal; systemd-run --user --scope -q -p MemoryMax=24G python3 $S/refusal_check.py $T $T/build/fn-host-developer $S/work-refusal $S/work-after $S/work-after/carried-204800.eml $S/work-after/carried-65536.eml > $S/refusal.log 2>&1; echo rc=$?
cd $T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$T/build/fn-host-developer FN_RUN_VERIFY_E2E=1 FN_TEST_OPENSSL=/tank/fn/scratch/qual-4eca4148/bin/test-openssl PATH=/tank/fn/scratch/qual-4eca4148/bin:$PATH
echo == verify large 4 MiB; FN_VERIFY_LARGE=1 FN_VERIFY_INIT_FLAGS="--max-article-octets 4194304" systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-large.log 2>&1; echo rc=$?
echo == verify default; systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-default.log 2>&1; echo rc=$?
date -u +end=%FT%TZ
