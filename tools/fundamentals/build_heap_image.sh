#!/bin/sh
# build_heap_image.sh TREE: TREE/build/fn-host-developer-heap, the developer
# image of TREE with heap-entry.lisp loaded just before build.lisp's
# save-exec (the fundamentals scoreboard's recipe, 2026-09-27).  Run on hbox
# in a tree whose certificates are installed (tools/hbox_native.sh's tree).
set -eu
T=$1; H=$(cd "$(dirname "$0")" && pwd); cd "$T"; mkdir -p build/freeze
awk -v f="$H/heap-entry.lisp" '/^\(save-exec / { print "(load \"" f "\")" } { print }' host/native/build.lisp > build/heap-build.lisp
grep -q heap-entry build/heap-build.lisp || { echo "build_heap_image: the hook was not spliced (no save-exec line)"; exit 1; }
FN_ACL2=${FN_IMAGE_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k} FN_NATIVE_PROFILE=developer \
  FN_NATIVE_WORLD=full FN_NATIVE_BUILD=build/heap-build.lisp FN_NATIVE_IMAGE=build/fn-host-developer-heap \
  FN_NATIVE_LOG=build/freeze/native-build-heap.log swarm-build sh tools/build_native_host.sh
echo BUILD-OK
