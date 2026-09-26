#!/bin/sh
# qual-b6759850 reruns: the four runs earlyoom terminated at 05:34:44-45Z (box memory
# pressure from other lanes plus the 1a checkpoint reopen), each once more, whole;
# fragment_node without the 10 MiB SCN-077 test (PKT-294: ~43 h projected); relocation.
set -u
S=/tank/fn/scratch/qual-b6759850
cd $S
L=$S/logs/rerun; mkdir -p $L
one() { tag=$1; shift; log=$L/$tag.log
  ( . $S/env.sh; cd $S/tree; echo "# $tag start $(date -u +%FT%TZ) FN_NATIVE_HOST=$FN_NATIVE_HOST"; s=$(date +%s)
    timeout 3600 python3 -m unittest -v "$@" 2>&1; echo "# rc=$? wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)" ) > $log 2>&1
  echo "$tag $(grep -E '^(OK|FAILED)' $log | tail -1) $(tail -1 $log)"; }
F=tests.test_bp_fragment_node_native.NativeBpFragmentNodeTests
FR="$F.test_adu_past_the_profile_is_refused_before_custody $F.test_journal_past_its_profile_is_refused_at_open $F.test_nonzero_fragment_then_restart_offset_zero_dispatches_once $F.test_rotation_with_a_family_in_flight_loses_no_fragment $F.test_seventy_fragments_across_a_kill_reassemble_once $F.test_sixty_four_fragments_across_a_kill_reassemble_once"
NS_TAG=dev NS_HOST=fn-host-developer one checkpoint.dev tests.test_checkpoint
NS_TAG=prod one served_crash_model.prod tests.test_native_served_crash_model
NS_TAG=dtn NS_BP_IMAGE=fn-host-dtn NS_BP_NODE_IMAGE=fn-host-dtn one fragment.dtn $FR
sh $S/reloc.sh; echo "reloc $(grep -E '^(OK|FAILED)' $S/logs/test_native_frozen_relocation.log)"
touch $S/done.rerun
