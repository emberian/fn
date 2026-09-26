#!/bin/sh
# qual-harness-c18: C15, C16, C17 and W1 on the frozen b6759850 images, after C18.
R=/tank/fn/scratch/qual-harness-c18
while [ ! -e $R/done.c18 ]; do sleep 20; done
I=/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80
DEVF=/tank/fn/scratch/throughput-gate/native-img-f370581bf9f3/tree/build/fn-host-developer
V=tests.test_native_operator_verbs.NativeOperatorInitTests.test_help_names_init
sh $R/run.sh c15-help-init.prod $V
NS_HOST=fn-host-developer sh $R/run.sh c15-help-init.dev $V
FN_NATIVE_HOST=$DEVF sh -c ". $R/env.sh; export FN_NATIVE_HOST=$DEVF; cd \$T; s=\$(date +%s); { echo '# c15 on dev f370581b image $DEVF'; sha256sum $DEVF; timeout 600 python3 -m unittest -v $V 2>&1; echo \"# rc=\$? wall=\$(( \$(date +%s) - s ))\"; } > $R/logs/c15-help-init.dev-f370581b.log 2>&1"
echo "c15-help-init.dev-f370581b: $(grep -E '^(OK|FAILED)' $R/logs/c15-help-init.dev-f370581b.log | tail -1)" >> $R/logs/summary.log
NS_BP_IMAGE=fn-host-dtn sh $R/run.sh c16-bp-raw.dtn tests.test_native_bp_channel_admission tests.test_native_bp_node_admission_lock
NS_BP_IMAGE=fn-host-dtn-developer sh $R/run.sh c16-bp-raw.dtndev tests.test_native_bp_channel_admission tests.test_native_bp_node_admission_lock
O=tests.test_native_owner.NativeOwnerHandlerStructureTests.test_developer_selectors_gate_arm_the_owner_and_stop_synchronously
sh $R/run.sh c16-owner-raw.prod $O
NS_HOST=fn-host-developer sh $R/run.sh c16-owner-raw.dev $O
FN_NATIVE_IMAGES=$I sh $R/run.sh c17-campaign.images tests.campaign.test_native_operator_campaign
W=tests.test_fn_web_native
sh $R/run.sh w1-web.prod $W
NS_HOST=fn-host-developer sh $R/run.sh w1-web.dev $W
touch $R/done.rest
