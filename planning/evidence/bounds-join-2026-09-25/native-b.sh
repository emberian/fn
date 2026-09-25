#!/bin/sh
T=/tank/fn/scratch/bounds-join/tree; S=/tank/fn/scratch/bounds-join
cd $T
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_NATIVE_SOURCE_ROOT=$T PYTHONDONTWRITEBYTECODE=1
export FN_FORMAT7_IMAGE=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host
date -u +start=%FT%TZ
echo == profile-upgrade
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer python3 -m unittest tests.test_native_profile_upgrade > $S/native-b-upgrade.log 2>&1; echo rc=$?
echo == verifier
PATH=/tank/fn/scratch/qual-4eca4148/bin:$PATH FN_NATIVE_HOST=$T/build/fn-host-developer FN_RUN_VERIFY_E2E=1 FN_VERIFY_LARGE=1 FN_TEST_OPENSSL=/tank/fn/scratch/qual-4eca4148/bin/test-openssl FN_VERIFY_INIT_FLAGS='--max-article-octets 4194304' /tank/fn/scratch/p8-verifier/venv/bin/python -m unittest -v tests.test_fn_verify > $S/native-b-verify.log 2>&1; echo rc=$?
echo == python store
python3 -m unittest tests.test_store tests.test_store_config tests.test_store_lifecycle tests.test_acl2_bridge tests.test_checkpoint tests.test_store_node_host > $S/native-b-pystore.log 2>&1; echo rc=$?
echo == native checkpoint
FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-developer python3 -m unittest tests.test_native_checkpoint > $S/native-b-checkpoint.log 2>&1; echo rc=$?
echo == probe
python3 -m tests.campaign.native_nntp_post_probe --images $T/build --work $S/probe-work --out $S/probe.json --init-flags '--max-article-octets 4194304' --body-octets 204800 --size-controls 33792,204800,1048576,2097152,3145728,4194305 --profile-bound 4194304 > $S/probe.log 2>&1; echo probe-rc=$?
date -u +end=%FT%TZ
