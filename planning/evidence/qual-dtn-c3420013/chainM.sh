#!/bin/sh
# qual-dtn-c3420013 module chain: every DTN module on the frozen DTN images.
S=/tank/fn/scratch/qual-dtn-c3420013
cd $S; echo "chainM pid $$ start $(date -u +%FT%TZ)"
# developer DTN image
NS_BP_IMAGE=fn-host-dtn-developer NS_TAG=dtn-developer sh run.sh test_bp_service_native test_bp_receive_integrity_native test_bp_contact_native
NS_DEV_IMAGE=fn-host-dtn-developer NS_TAG=dtn-developer sh run.sh test_bp_obligation_native test_bp_app_native test_native_app_journal
NS_TAG=dtn-developer sh run.sh test_bp_node_native
# production DTN image (module defaults: FN_NATIVE_BP_HOST and contact sender/receiver = fn-host-dtn)
NS_TAG=dtn sh run.sh test_bp_service_native test_bp_receive_integrity_native test_bp_contact_native test_bp_contact_relay_native
NS_DEV_IMAGE=fn-host-dtn NS_TAG=dtn sh run.sh test_bp_obligation_native test_bp_app_native
# all four images
NS_TAG=four sh run.sh test_native_image_profiles
echo "chainM end $(date -u +%FT%TZ)"; touch $S/done.M
