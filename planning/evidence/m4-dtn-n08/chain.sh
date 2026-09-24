#!/bin/sh
cd /tank/fn/scratch/m4-dtn-n08
NS_DEV_IMAGE=fn-host-dtn-developer NS_TAG=dtn-developer sh run.sh test_bp_node_native.NativeBpNodeTests.test_death_after_kind_eight_retries_once_and_peer_holds_one_copy
for m in test_bp_service_native test_bp_contact_native test_bp_contact_relay_native test_bp_receive_integrity_native test_native_app_journal; do sh run.sh $m; done
NS_TAG=default-developer sh run.sh test_bp_node_native
