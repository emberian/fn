#!/bin/sh
# rf-start.sh IMAGE FILE: start IMAGE's core without ACL2's loop and load FILE.
IMAGE=$1; FILE=$2
line=$(grep '^exec ' "$IMAGE")
home=$(sed -n "s/^export SBCL_HOME='\(.*\)'/\1/p" "$IMAGE")
sbcl=$(echo "$line" | sed 's/^exec "\([^"]*\)".*/\1/')
core=$(echo "$line" | sed 's/.*--core "\([^"]*\)".*/\1/')
SBCL_HOME=$home exec "$sbcl" --tls-limit 65536 --dynamic-space-size 8000MB --control-stack-size 64 \
  --disable-ldb --core "$core" --noinform --end-runtime-options --no-userinit \
  --disable-debugger --eval "(load \"$FILE\")" --non-interactive
