#!/bin/sh
# Build a PROFILING developer image (tools/profile/native-profile-entry.lisp):
# host/native/build.lisp with the profiler's entry loaded before its save-exec.
# Run from the tree root, under swarm-build on hbox:
#   swarm-build sh tools/profile/build_native_profile.sh build/fn-host-prof
# Never a release artifact: the entry starts sb-sprof when FN_PROF_OUT is set.
set -eu
OUT=${1:-build/fn-host-prof}
# The image's launcher must run at --tls-limit 65536 (batch AV: "Thread local
# storage exhausted" at 16384); on hbox that is the w28 tls64k launcher,
# as tools/hbox_native.sh uses (the certify step's FN_ACL2, the plain w28
# launcher, is replaced by it here).  Any other explicit FN_ACL2 wins.
TLS64K=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k
if [ -x "$TLS64K" ] && { [ -z "${FN_ACL2:-}" ] || [ "$FN_ACL2" = /tank/fn/toolchains/w28/acl2-literal-4g ]; }; then
  FN_ACL2=$TLS64K; export FN_ACL2
fi
mkdir -p build
SCRIPT=build/native-profile-build.lisp
awk '/^\(save-exec / { print "(load \"tools/profile/native-profile-entry.lisp\")" } { print }' \
    host/native/build.lisp > "$SCRIPT"
grep -q 'native-profile-entry' "$SCRIPT" || { echo "no save-exec line in build.lisp" >&2; exit 2; }
FN_NATIVE_PROFILE=developer FN_NATIVE_WORLD=full FN_NATIVE_BUILD="$SCRIPT" \
  FN_NATIVE_IMAGE="$OUT" FN_NATIVE_LOG="$OUT.log" sh tools/build_native_host.sh
