#!/bin/sh
# tools/image_anatomy/anatomy.sh IMAGE OUT SNAPSHOT...
# Start IMAGE's core with tools/image_anatomy/ia-anatomy.lisp in place of
# (acl2::sbcl-restart): ACL2 never starts, nothing is saved.  Every object of
# the core is given an owner and joined with the residency SNAPSHOTs
# (ia_node.py).  OUT is the log (IA- lines).  Run under a memory limit.
set -eu
IMAGE=$1 OUT=$2; shift 2
here=$(cd "$(dirname "$0")" && pwd)
snaps=""
for s in "$@"; do snaps="$snaps \"$s\""; done
line=$(grep '^exec ' "$IMAGE")
home=$(sed -n "s/^export SBCL_HOME='\(.*\)'/\1/p" "$IMAGE")
sbcl=$(echo "$line" | sed 's/^exec "\([^"]*\)".*/\1/')
core=$(echo "$line" | sed 's/.*--core "\([^"]*\)".*/\1/')
SBCL_HOME=$home "$sbcl" --tls-limit 16384 --dynamic-space-size 6000MB --control-stack-size 64 \
  --disable-ldb --core "$core" --noinform --end-runtime-options --no-userinit \
  --eval "(load \"$here/ia-anatomy.lisp\")" \
  --eval "(acl2::ia-main (list $snaps))" --non-interactive > "$OUT" 2>&1
grep -q IA-DONE "$OUT"
