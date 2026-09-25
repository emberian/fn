#!/bin/sh
# P2 native: the POST probe's cuts on a large article and the size controls.
set -u
T=/tank/fn/scratch/bounds-p2/gate-b25de18b
S=/tank/fn/scratch/bounds-p2
G=$T/build
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export PYTHONDONTWRITEBYTECODE=1
cd $T
date -u +start=%FT%TZ
/usr/bin/time -v python3 -m tests.campaign.native_nntp_post_probe --images $G \
  --work $S/probe-large-work --out $S/probe-large.json --body-octets 31000 \
  --size-controls 32000,33792,204800,3145728 --profile-bound 32768 \
  > $S/probe-large.log 2>&1
echo probe-rc=$?
date -u +end=%FT%TZ
