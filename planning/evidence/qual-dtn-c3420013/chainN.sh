#!/bin/sh
# qual-dtn-c3420013 native-authoring lab chain: the same app-receipt labs with
# `--native' (A authors the request with `bp-obligation request'), plus the
# unauthorized-carrier control (B enrols only the neighbour). Runs after chainX.
set -u
S=/tank/fn/scratch/qual-dtn-c3420013
I=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013
while [ ! -e $S/done.X ]; do sleep 20; done
T=$S/tree; R=$S/labs-native; D=/tank/fn/dtn7/repo; mkdir -p $R
export PATH=$S/bin:$PATH SBCL_HOME=$I/runtime/sbcl-home/ PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
cd $T; echo "chainN pid $$ start $(date -u +%FT%TZ)"
run() { n=$1; shift; s=$(date +%s); { echo "# $n start $(date -u +%FT%TZ) cwd $T"; echo "# cmd: $*"; } > $R/$n.out
  "$@" >> $R/$n.out 2>&1 < /dev/null; rc=$?; echo "# rc=$rc wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)" >> $R/$n.out; echo "$n rc=$rc"; }
A=tests/bp-dtn7/run_fn_dtn7_app_receipt.py
DEV=$I/fn-host-dtn-developer
run n-control       python3 $A --image $DEV --relays 0 --native --work $R/n-control
run n-relay1-listed python3 $A --image $DEV --relays 1 --native --a-releases listed --dtn7-repo $D --work $R/n-relay1-listed
run n-relay1-none   python3 $A --image $DEV --relays 1 --native --a-releases none --dtn7-repo $D --work $R/n-relay1-none
run n-relay2-listed python3 $A --image $DEV --relays 2 --native --a-releases listed --dtn7-repo $D --work $R/n-relay2-listed
run n-unauthorized  python3 $A --image $DEV --relays 1 --native --b-trusts neighbour --dtn7-repo $D --work $R/n-unauthorized
echo "chainN end $(date -u +%FT%TZ)"; touch $S/done.N
