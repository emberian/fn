#!/bin/sh
# qual-dfa810fc item 2: the release tarball from the gate's frozen production image
# (the qualified bytes), the friend's install exactly as tests/friends_tarball.sh does
# after its freeze step, then the friend modules and friends_signed.py on the tarball's node.
set -u
. /tank/fn/scratch/qual-dfa810fc/env.sh
F=$S/friends; rm -rf $F; mkdir -p $F
cd $S/ctree
short=$(printf '%s' "$REV" | cut -c1-12)
sh packaging/release-tarball.sh $I $REV $F/release > $F/release.log 2>&1; echo "release rc=$?" >> $F/release.log
mkdir -p $F/friend
cp $F/release/fn-$short-linux-x86_64.tar.gz $F/release/fn-$short-linux-x86_64.tar.gz.sha256 $F/friend/
( cd $F/friend && sha256sum -c fn-$short-linux-x86_64.tar.gz.sha256 && tar xzf fn-$short-linux-x86_64.tar.gz && cd fn-$short && sha256sum -c --quiet SHA256SUMS && echo SUMS-OK ) > $F/install.log 2>&1
FFN=$F/friend/fn-$short/bin/fn
{ echo "tarball sha256 $(sha256sum $F/release/fn-$short-linux-x86_64.tar.gz)";
  echo "tarball core vs gate core:"; sha256sum $F/friend/fn-$short/libexec/fn/fn-host.core $I/fn-host.core $F/friend/fn-$short/libexec/fn/fn-host $I/fn-host;
  echo "fn --version: $(env -u LD_LIBRARY_PATH $FFN --version 2>&1)"; echo "bare fn: $(env -u LD_LIBRARY_PATH $FFN 2>&1 | head -3)"; } >> $F/install.log 2>&1
m() { tag=$1; shift; log=$F/$tag.log; { echo "# $tag start $(date -u +%FT%TZ)"; s=$(date +%s); env "$@" 2>&1; echo "# rc=$? wall=$(( $(date +%s) - s ))"; } > $log 2>&1; echo "$tag: $(grep -E '^(OK|FAILED)' $log | tail -1) $(tail -1 $log)" >> $F/summary.txt; }
m friends_feed FN_NATIVE_HOST=$I/fn-host-developer FN_FRIEND_FN=$FFN timeout 1800 python3 -m unittest -v tests.test_native_friends_feed
m friends_accounts FN_NATIVE_HOST=$I/fn-host-developer FN_FRIEND_FN=$FFN FN_OLD_IMAGE=$OLDI/fn-host timeout 1800 python3 -m unittest -v tests.test_native_friends_accounts
m friends_signed timeout 1200 python3 $S/friends_signed.py $FFN $F/signed $I/fn-host-developer $FN_TEST_OPENSSL
m auth_on_tarball FN_NATIVE_HOST=$F/friend/fn-$short/libexec/fn/fn-host timeout 1800 python3 -m unittest -v tests.test_native_auth
m pull_unavailable_on_tarball FN_NATIVE_HOST=$F/friend/fn-$short/libexec/fn/fn-host timeout 1800 python3 -m unittest -v tests.test_native_peer_pull.NativePeerPullTests.test_unavailable_id_is_dropped_at_the_bound tests.test_native_peer_pull.NativePeerPullTests.test_unavailable_count_survives_a_cut
touch $S/done.friends
