#!/bin/sh
# `make extract-check': the extraction differential (tools/extract/check.sh)
# on hbox.  On hbox inside a built tree (build/fn-host-developer present) it
# runs there; elsewhere it ships REV (default `.', this tree) with
# tools/hbox_native.sh, which certifies what the cache lacks and builds the
# developer image (running the served differential module on the way), then
# runs check.sh in that scratch tree over ssh.  Exit 0 only on PASS.
set -u
REV=${1:-.}
LABEL=${EXTRACT_LABEL:-extract-check}
if [ -x build/fn-host-developer ] && [ -d /tank/fn/toolchains ]; then
    exec sh tools/extract/check.sh . build/fn-host-developer
fi
NAME=$(basename "$(pwd)")
# hbox_native.sh detaches by default and returns once the box run has
# started; check.sh needs the built image, so wait for the run's status
# (attach), which also leaves the run alive if this side dies.  --box hbox:
# the check below runs in hbox's scratch path.
tools/hbox_native.sh --box hbox --label "$LABEL" "$REV" tests.test_native_served_differential || {
    echo "extract-check: FAIL at image: tools/hbox_native.sh could not start"; exit 1; }
tools/hbox_native.sh attach "$LABEL" || {
    echo "extract-check: FAIL at image: tools/hbox_native.sh run $LABEL (status: tools/hbox_native.sh status $LABEL)"; exit 1; }
# The source the image was built from, for the gate's extraction manifest
# (as hbox_native.sh names it: HEAD, +dirty for uncommitted edits, or REV).
if [ "$REV" = . ]; then
    SOURCE=$(git rev-parse HEAD)$(git diff --quiet HEAD -- 2>/dev/null || echo '+dirty')
else
    SOURCE=$(git rev-parse --verify "$REV^{commit}")
fi
ssh hbox "cd /tank/fn/scratch/$NAME/native-$LABEL/tree && FN_EXTRACT_SOURCE=$SOURCE swarm-build sh tools/extract/check.sh . build/fn-host-developer"
st=$?
[ $st = 0 ] || echo "extract-check: FAIL (remote status $st; /tank/fn/scratch/$NAME/native-$LABEL/tree/build/extract/check/status.json)"
exit $st
