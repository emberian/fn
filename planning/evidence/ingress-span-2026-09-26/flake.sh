#!/bin/sh
# usage: flake.sh -- the two-client uncertainty test 15 times on each image
T=/tank/fn/scratch/ingress-span-2/native-after/tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib64:/tank/fn/toolchains/openssl-3.5.8/lib
cd $T
for side in before after; do
  if [ $side = after ]; then I=$T/build/fn-host-developer; else I=/tank/fn/scratch/throughput-gate/native-img-f314a5a3/tree/build/fn-host-developer; fi
  ok=0; bad=0
  for i in $(seq 1 40); do
    if FN_NATIVE_DEVELOPER_HOST=$I timeout 120 python3 -m unittest tests.test_native_owner.NativeOwnerTests.test_two_client_uncertainty_fences_before_later_mutation > /tank/fn/scratch/ingress-span-2/meas/flake2-$side-$i.log 2>&1; then ok=$((ok+1)); else bad=$((bad+1)); fi
  done
  echo "$side ok=$ok failed=$bad"
done
