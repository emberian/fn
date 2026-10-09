# The per-command heap decision every launcher of a saved fn core carries
# (the image's, tools/build_native_host.sh; fn-core's, tools/extract/
# core_launcher.py), after packaging/fn's fn_decide_heap: a start whose
# caller names no heap runs the core's own `heap -- ARGV' probe and starts at
# the heap and control stack ACL2 decides.  A caller's SBCL_USER_ARGS that
# names a heap (--dynamic-space-size) is its own figure and wins; one that
# names only other runtime options (a test's control stack) composes with the
# decision: the decided heap and stack first, the caller's options after, and
# SBCL takes the last of each, so the caller's stack runs on the decided heap
# (LAUNCHER-STACK-ARGS-REPLACE-DECIDED-HEAP: since train 63 a stack-only
# caller lost the decision and cold-started at the launcher's small-preset
# heap).  FN_TEST_HEAP_MB is the tests' named override of the decided heap.
fn_decide_command_heap() {
    shift
    fn_decide_heap "$0" "$@"
}
case " ${SBCL_USER_ARGS:-} " in
    *" --dynamic-space-size "*) fn_caller_heap=1 ;;
    *) fn_caller_heap= ;;
esac
if [ -z "$fn_caller_heap" ] && [ "${1:-}" = --fn ] && [ "${2:-}" != heap ]; then
    fn_caller_args=${SBCL_USER_ARGS:-}
    if [ -n "${FN_TEST_HEAP_MB:-}" ]; then
        SBCL_USER_ARGS="--dynamic-space-size $FN_TEST_HEAP_MB"
    else
        fn_decide_command_heap "$@"
    fi
    SBCL_USER_ARGS="$SBCL_USER_ARGS${fn_caller_args:+ $fn_caller_args}"
    export SBCL_USER_ARGS
fi
