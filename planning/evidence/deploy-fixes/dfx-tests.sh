#!/bin/sh
cd /tank/fn/scratch/deploy-fixes/tree
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
L=/tank/fn/scratch/deploy-fixes/logs; mkdir -p $L
run() { n=$1; shift; timeout 3600 python3 -m unittest -v "$@" > $L/$n.log 2>&1; echo "$n rc=$?"; tail -3 $L/$n.log; }
run control_authority tests.test_native_control_authority
run control_a4 tests.test_native_control.NativeControlTests.test_two_clients_sigterm_cleanup_and_restart tests.test_native_control.NativeControlTests.test_lost_reply_after_submission_is_uncertain_and_recovers
run history_migrate tests.test_native_history_required.MigrationTests.test_migrate_then_absence_and_loss_are_damage
grep -il "invariant-risk" $L/*.log || echo "no invariant-risk in any log"
