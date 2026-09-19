#!/bin/bash
# Start one ION node (ionadmin, ltpadmin with ltpclock/ltpcli/ltpclo, bpadmin).
# Never use ION's bundled `killm`: it pattern-kills every ION process on the
# host, which is unsafe on a shared build machine.
set -eu
. "$(dirname "$0")/env.sh"
cd "$1"
ionadmin node.ionrc
sleep 1
ionadmin global.ionrc
sleep 1
ionsecadmin node.ionsecrc
sleep 1
ltpadmin node.ltprc
sleep 1
bpadmin node.bprc
sleep 2
bpadmin <<'BPQ'
l induct
l outduct
BPQ
