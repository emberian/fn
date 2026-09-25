#!/bin/sh
# bp-resume-verbs lane: native modules on the DTN developer image of img-tree.
set -u
S=/tank/fn/scratch/bp-resume
T=$S/img-tree
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_NATIVE_SOURCE_ROOT=$T FN_NATIVE_DEVELOPER_HOST=$T/build/fn-host-dtn-developer
export FN_NATIVE_BP_NODE_HOST=$T/build/fn-host-dtn-developer FN_NATIVE_DTN_DEVELOPER_HOST=$T/build/fn-host-dtn-developer
cd "$T"
L=$S/tests; mkdir -p $L
for m in "$@"; do
  s=$(date +%s)
  timeout 3600 python3 -m unittest -v tests.$m > $L/$m.log 2>&1; rc=$?
  echo "$m rc=$rc $(( $(date +%s) - s ))s $(tail -1 $L/$m.log) $(sha256sum $L/$m.log | cut -c1-16)"
done
echo TESTS-DONE
