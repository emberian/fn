#!/bin/sh
# qual-69046a76 sequence B (after seqA): the 4,500-record chain EIO campaign; the campaign
# (cuts, marker cuts, probe, crash model, D25 matrix, production kill); the relocated image;
# outcome_algebra against the b6759850 image as the old one.
set -u
S=/tank/fn/scratch/qual-69046a76
while systemctl --user is-active -q qual-69046a76-seqA; do sleep 60; done
. $S/env.sh
echo "eio $(date -u +%FT%TZ)"
( cd $S/tree && export FN_NATIVE_HOST=$I/fn-host-developer && timeout 5400 python3 -m unittest -v tests.test_native_pack_chain.NativePackChainTests.test_eio_at_each_link_publication_cut_from_both_entries > $S/logs/chain-eio.log 2>&1; echo "rc=$?" >> $S/logs/chain-eio.log )
echo "campaign $(date -u +%FT%TZ)"; sh $S/campaign.sh > $S/logs/campaign.out 2>&1
echo "reloc $(date -u +%FT%TZ)"; sh $S/reloc.sh
echo "outcome-b67 $(date -u +%FT%TZ)"
( cd $S/tree && FN_OLD_NATIVE_HOST=$B67I/fn-host timeout 3600 python3 -m unittest -v tests.test_native_outcome_algebra > $S/logs/outcome-algebra-old-b6759850.log 2>&1; echo "rc=$?" >> $S/logs/outcome-algebra-old-b6759850.log )
touch $S/done.B2; echo "B-DONE $(date -u +%FT%TZ)"
