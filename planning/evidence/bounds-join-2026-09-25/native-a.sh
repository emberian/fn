#!/bin/sh
cd /tank/fn/scratch/bounds-join/tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export FN_NATIVE_HOST=$PWD/build/fn-host FN_NATIVE_DEVELOPER_HOST=$PWD/build/fn-host-developer
export FN_FORMAT7_IMAGE=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host
export PYTHONDONTWRITEBYTECODE=1
date -u +start=%FT%TZ
python3 -m unittest -v tests.test_native_bounds_join tests.test_native_profile_upgrade tests.test_native_owner.NativeOwnerTests.test_article_over_the_body_limit_is_refused_and_the_owner_survives 2>&1
echo rc=$?
date -u +end=%FT%TZ
