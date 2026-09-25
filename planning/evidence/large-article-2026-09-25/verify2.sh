#!/bin/sh
T=/tank/fn/scratch/large-article/tree; S=/tank/fn/scratch/large-article
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g PYTHONDONTWRITEBYTECODE=1
export FN_NATIVE_HOST=$T/build/fn-host-developer FN_RUN_VERIFY_E2E=1 FN_TEST_OPENSSL=/tank/fn/scratch/qual-4eca4148/bin/test-openssl PATH=/tank/fn/scratch/qual-4eca4148/bin:$PATH
exit_unused=0; echo == verify bound 65536
FN_VERIFY_INIT_FLAGS='--max-article-octets 65536' systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-64k.log 2>&1; echo rc=$?
echo == verify large 4 MiB
FN_VERIFY_LARGE=1 FN_VERIFY_INIT_FLAGS='--max-article-octets 4194304' systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-large-3.log 2>&1; echo rc=$?
