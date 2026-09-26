R=/tank/fn/scratch/qual-harness-c18
C=tests.test_native_control.NativeControlTests.test_operator_post_is_injected_and_refuses_what_post_refuses
sh $R/run.sh w1-web.prod.r2 tests.test_fn_web_native
NS_HOST=fn-host-developer sh $R/run.sh w1-web.dev.r2 tests.test_fn_web_native
sh $R/run.sh c15-help-init.prod.r2 tests.test_native_operator_verbs.NativeOperatorInitTests.test_help_names_init tests.test_native_operator_verbs.NativeOperatorReservedGroupSourceTests
NS_HOST=fn-host-developer sh $R/run.sh c15-help-init.dev.r2 tests.test_native_operator_verbs.NativeOperatorInitTests.test_help_names_init tests.test_native_operator_verbs.NativeOperatorReservedGroupSourceTests
sh $R/run.sh c4-control-path.prod $C
NS_HOST=fn-host-developer sh $R/run.sh c4-control-path.dev $C
touch $R/done.rest2
