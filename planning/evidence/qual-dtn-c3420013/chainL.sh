#!/bin/sh
# qual-dtn-c3420013 lab chain: the BP labs on the frozen DTN images, from a copy of the gate.
set -u
S=/tank/fn/scratch/qual-dtn-c3420013
I=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013
T=$S/tree
R=$S/labs
D=/tank/fn/dtn7/repo
export PATH=$S/bin:$PATH SBCL_HOME=$I/runtime/sbcl-home/ PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
cd $T; echo "chainL pid $$ start $(date -u +%FT%TZ)"
run() { n=$1; shift; s=$(date +%s); { echo "# $n start $(date -u +%FT%TZ) cwd $T"; echo "# cmd: $*"; } > $R/$n.out
  "$@" >> $R/$n.out 2>&1 < /dev/null; rc=$?; echo "# rc=$rc wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)" >> $R/$n.out; echo "$n rc=$rc"; }
A=tests/bp-dtn7/run_fn_dtn7_app_receipt.py
DEV=$I/fn-host-dtn-developer
run control      python3 $A --image $DEV --relays 0 --work $R/control
run relay1-listed python3 $A --image $DEV --relays 1 --a-releases listed --dtn7-repo $D --work $R/relay1-listed
run relay1-none  python3 $A --image $DEV --relays 1 --a-releases none --dtn7-repo $D --work $R/relay1-none
run relay2-listed python3 $A --image $DEV --relays 2 --a-releases listed --dtn7-repo $D --work $R/relay2-listed
run four-dtn7    python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-dtn7 --revision c3420013 --dtn7-repo $D --image $DEV
run ic-dtn       python3 tests/bp-dtn7/run_fn_dtn7_interrupted_contact.py --image $I/fn-host-dtn --dtn7-repo $D --work $R/ic-dtn
run ic-dtn-developer python3 tests/bp-dtn7/run_fn_dtn7_interrupted_contact.py --image $DEV --dtn7-repo $D --work $R/ic-dtn-developer
echo "chainL end $(date -u +%FT%TZ)"; touch $S/done.L
