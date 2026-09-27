#!/bin/sh
# Build a PROFILING developer image (tools/profile/native-profile-entry.lisp):
# host/native/build.lisp with the profiler's entry loaded before its save-exec.
# Run from the tree root, under swarm-build on hbox:
#   swarm-build sh tools/profile/build_native_profile.sh build/fn-host-prof
# Never a release artifact: the entry starts sb-sprof when FN_PROF_OUT is set.
set -eu
OUT=${1:-build/fn-host-prof}
mkdir -p build
SCRIPT=build/native-profile-build.lisp
awk '/^\(save-exec / { print "(load \"tools/profile/native-profile-entry.lisp\")" } { print }' \
    host/native/build.lisp > "$SCRIPT"
grep -q 'native-profile-entry' "$SCRIPT" || { echo "no save-exec line in build.lisp" >&2; exit 2; }
FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD="$SCRIPT" \
  FN_NATIVE_IMAGE="$OUT" FN_NATIVE_LOG="$OUT.log" sh tools/build_native_host.sh
