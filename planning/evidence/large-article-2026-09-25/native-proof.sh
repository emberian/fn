#!/bin/sh
# large-article native proof on the fixed images (tree = lane source at 4d75b021 + nothing else).
T=/tank/fn/scratch/large-article/tree; S=/tank/fn/scratch/large-article
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_SOURCE_ROOT=$T PYTHONDONTWRITEBYTECODE=1
date -u +start=%FT%TZ
echo == probe 3 MiB cuts
systemd-run --user --scope -q -p MemoryMax=24G python3 -m tests.campaign.native_nntp_post_probe --images $T/build --work $S/probe-work --out $S/probe.json --init-flags '--max-article-octets 4194304' --body-octets 3145728 --size-controls 2097152,3145728,4193280,4194305 --profile-bound 4194304 > $S/probe.log 2>&1; echo probe-rc=$?
date -u +probe-end=%FT%TZ
echo == verify default bound
FN_NATIVE_HOST=$T/build/fn-host-developer FN_RUN_VERIFY_E2E=1 FN_TEST_OPENSSL=/tank/fn/scratch/qual-4eca4148/bin/test-openssl PATH=/tank/fn/scratch/qual-4eca4148/bin:$PATH systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-default.log 2>&1; echo verify-default-rc=$?
echo == verify large
FN_NATIVE_HOST=$T/build/fn-host-developer FN_RUN_VERIFY_E2E=1 FN_VERIFY_LARGE=1 FN_VERIFY_INIT_FLAGS='--max-article-octets 4194304' FN_TEST_OPENSSL=/tank/fn/scratch/qual-4eca4148/bin/test-openssl PATH=/tank/fn/scratch/qual-4eca4148/bin:$PATH systemd-run --user --scope -q -p MemoryMax=24G /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/verify-large.log 2>&1; echo verify-large-rc=$?
echo == native owner oversize plaintext
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_owner.NativeOwnerTests.test_article_over_the_body_limit_is_refused_and_the_owner_survives > $S/native-owner.log 2>&1; echo native-owner-rc=$?
date -u +end=%FT%TZ
