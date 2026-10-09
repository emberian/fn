# The per-command heap decision every launcher of a saved fn core carries
# (the image's, tools/build_native_host.sh; fn-core's, tools/extract/
# core_launcher.py), after packaging/fn's fn_decide_heap: a start with no
# caller figure runs the core's own `heap -- ARGV' probe and starts at the
# heap and control stack ACL2 decides.  A caller's SBCL_USER_ARGS is its own
# figure and wins; FN_TEST_HEAP_MB is the tests' named override.
fn_decide_command_heap() {
    shift
    fn_decide_heap "$0" "$@"
}
if [ -z "${SBCL_USER_ARGS:-}" ] && [ "${1:-}" = --fn ] && [ "${2:-}" != heap ]; then
    if [ -n "${FN_TEST_HEAP_MB:-}" ]; then
        SBCL_USER_ARGS="--dynamic-space-size $FN_TEST_HEAP_MB"
        export SBCL_USER_ARGS
    else
        fn_decide_command_heap "$@"
    fi
fi
