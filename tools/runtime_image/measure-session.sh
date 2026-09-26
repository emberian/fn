#!/bin/sh
# tools/runtime_image/measure-session.sh ACL2 BUILD LABEL OUT
# Run BUILD (an image build script such as host/native/build.lisp) through
# ACL2 up to its `:q', then, instead of save-exec, measure the world and the
# host's executable closure (world-measure.lisp, closure.lisp).  Run from a
# certified tree's root; nothing is saved.  LABEL names the lines; OUT is the
# log.  The roots file is every symbol-like token of host/native/*.lisp.
set -eu
ACL2=$1 BUILD=$2 LABEL=$3 OUT=$4
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
cat host/native/*.lisp | tr -c 'A-Za-z0-9*+!<>=/?%&$_.-' '\n' | grep -E '^[A-Za-z]' | sort -u > "$dir/roots.txt"
sed -n '1,/^:q$/p' "$BUILD" > "$dir/session.lisp"
cat >> "$dir/session.lisp" <<LISP
(in-package "ACL2")
(load "tools/runtime_image/world-measure.lisp")
(load "tools/runtime_image/closure.lisp")
(ri-world-report "$LABEL")
(ri-closure-report "$dir/roots.txt")
(ri-strip-report "$LABEL-execution-props" *ri-execution-props*)
(ri-strip-report "$LABEL-no-world" nil)
(format t "~&RI-DONE~%")
(sb-ext:exit :code 0 :abort t)
LISP
FN_NATIVE_PROFILE=${FN_NATIVE_PROFILE:-production} FN_NATIVE_IMAGE="$dir/unused" \
  ACL2_CUSTOMIZATION=NONE env -u ACL2_SYSTEM_BOOKS "$ACL2" < "$dir/session.lisp" > "$OUT" 2>&1
grep -q 'RI-DONE' "$OUT"
