#!/bin/sh
# qual-69046a76 sequence A (one at a time): facts 1b/1c + rollback consequences, friends (item 2),
# fact 1a (checkpoint at A x K/2), section-15 rows (n300, tight, probes, the 20,000 fixture),
# the pack-chain-link and chain publication cuts, bigreply on the 20,000 fixture copy.
set -u
S=/tank/fn/scratch/qual-69046a76
cd $S
echo "upgrade $(date -u +%FT%TZ)"; sh $S/upgrade.sh
echo "friends $(date -u +%FT%TZ)"; sh $S/friends.sh
echo "ckpt $(date -u +%FT%TZ)"; sh $S/ckpt.sh > $S/logs/ckpt.out 2>&1
echo "s15 $(date -u +%FT%TZ)"; sh $S/s15.sh > $S/logs/s15.out 2>&1
echo "chaincuts $(date -u +%FT%TZ)"
. $S/env.sh
( cd $S/tree && export FN_NATIVE_HOST=$I/fn-host-developer && timeout 5400 python3 -m unittest -v tests.test_native_pack_chain.NativePackChainTests.test_pack_chain_link_cut_leaves_exactly_the_selected_links tests.test_native_pack_chain.NativePackChainTests.test_every_chain_publication_cut_from_both_entries > $S/logs/chaincuts.log 2>&1; echo "rc=$?" >> $S/logs/chaincuts.log )
echo "bigreply $(date -u +%FT%TZ)"
rm -rf $S/bigreply; ( cd $S/tree && timeout 3600 python3 $S/bigreply.py $I/fn-host $S/bigreply > $S/logs/bigreply.log 2>&1; echo "rc=$?" >> $S/logs/bigreply.log ); rm -rf $S/bigreply/store
touch $S/done.A; echo "A-DONE $(date -u +%FT%TZ)"
