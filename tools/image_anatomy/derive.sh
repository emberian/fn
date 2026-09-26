#!/bin/sh
# tools/image_anatomy/derive.sh BASE NEW FORMS...
# Make an experimental image NEW from the native image BASE (lane
# image-anatomy): start BASE's core without starting ACL2, evaluate each of
# FORMS in order (e.g. '(load "x.lisp")'), then save the core again with
# SBCL's own toplevel, exactly as ACL2's save-exec does, so NEW's script
# starts it with the same `--eval (acl2::sbcl-restart)' and arguments.  NEW
# is BASE's script with the core path replaced.  Never a release image.
set -eu
BASE=$1 NEW=$2; shift 2
line=$(grep '^exec ' "$BASE")
home=$(sed -n "s/^export SBCL_HOME='\(.*\)'/\1/p" "$BASE")
sbcl=$(echo "$line" | sed 's/^exec "\([^"]*\)".*/\1/')
core=$(echo "$line" | sed 's/.*--core "\([^"]*\)".*/\1/')
newcore=$(cd "$(dirname "$NEW")" && pwd)/$(basename "$NEW").core
set -- "$@" "(progn (sb-ext:gc :full t) (sb-ext:save-lisp-and-die \"$newcore\" :executable nil))"
args=""
for f in "$@"; do args="$args --eval '$f'"; done
eval SBCL_HOME="$home" "$sbcl" --tls-limit 16384 --dynamic-space-size 8000MB --control-stack-size 64 \
  --disable-ldb --core "$core" --noinform --end-runtime-options --no-userinit \
  --disable-debugger $args
sed "s|--core \"[^\"]*\"|--core \"$newcore\"|" "$BASE" > "$NEW"
chmod +x "$NEW"
ls -la "$newcore"
