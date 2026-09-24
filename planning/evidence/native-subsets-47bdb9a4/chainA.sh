#!/bin/sh
cd /tank/fn/scratch/native-subsets-47bdb9a4
sh run.sh test_bp_service_native test_bp_contact_native test_bp_contact_relay_native test_bp_receive_integrity_native
NS_BP_IMAGE=fn-host-dtn-developer NS_TAG=dtn-developer sh run.sh test_bp_service_native test_bp_receive_integrity_native
sh run.sh test_native_app_journal test_native_image_profiles test_bp_obligation_native test_bp_node_native test_bp_app_native test_bp_fragment_node_native
NS_TREE=tree-dev NS_TAG=devtests sh run.sh test_bp_node_native test_bp_app_native
touch /tank/fn/scratch/native-subsets-47bdb9a4/done.A
