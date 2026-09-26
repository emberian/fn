#!/bin/sh
# tools/image_anatomy/guard.sh IMAGE: run guard-probe.lisp in IMAGE's core.
set -u
IMAGE=$1
here=$(cd "$(dirname "$0")" && pwd)
line=$(grep '^exec ' "$IMAGE")
home=$(sed -n "s/^export SBCL_HOME='\(.*\)'/\1/p" "$IMAGE")
sbcl=$(echo "$line" | sed 's/^exec "\([^"]*\)".*/\1/')
core=$(echo "$line" | sed 's/.*--core "\([^"]*\)".*/\1/')
SBCL_HOME=$home timeout 120 "$sbcl" --tls-limit 16384 --dynamic-space-size 1024MB --control-stack-size 64 \
  --disable-ldb --core "$core" --noinform --end-runtime-options --no-userinit \
  --eval "(load \"$here/guard-probe.lisp\")" --eval '(acl2::sbcl-restart)' --disable-debugger \
  < /dev/null 2>&1
echo "guard.sh exit $?"
