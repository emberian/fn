#!/bin/sh
# qual-dtn-c3420013 supplementary chain: dev's post-cut DTN tests and lab
# (signed receipts, BP resume, busy delivery, BP-R17 recover) against the
# FROZEN c3420013 images, to show where the post-cut cases fail. tree-dev is
# the gate copy with only dev's four changed files overlaid.
set -u
S=/tank/fn/scratch/qual-dtn-c3420013
I=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013
while [ ! -e $S/done.M ] || [ ! -e $S/done.L ]; do sleep 20; done
echo "chainX pid $$ start $(date -u +%FT%TZ)"
rsync -a $S/tree/ $S/tree-dev/ && cp -r $S/devtests/tests/. $S/tree-dev/tests/
sed -e "s#^T=\$S/tree#T=\$S/tree-dev#" -e "s#^L=\$S/logs#L=\$S/logs-dev#" $S/run.sh > $S/run-dev.sh
NS_TAG=dev-tests sh $S/run-dev.sh \
  test_bp_node_native.NativeBpNodeTests.test_busy_application_defers_and_redelivers_after_backoff \
  test_bp_node_native.NativeBpNodeTests.test_permanently_busy_application_strands_row_until_recovery \
  test_bp_node_native.NativeBpNodeTests.test_uncertain_transfer_is_connection_local_and_resume_rearms
NS_DEV_IMAGE=fn-host-dtn-developer NS_TAG=dev-tests sh $S/run-dev.sh \
  test_bp_obligation_native.NativeBpObligationTests.test_kill_between_attempt_and_outcome_then_recover_committed
NS_TAG=dev-tests sh $S/run-dev.sh test_bp_contact_relay_native
export PATH=$S/bin:$PATH SBCL_HOME=$I/runtime/sbcl-home/ PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
export FN_TEST_OPENSSL=$S/bin/test-openssl
R=$S/labs-dev; mkdir -p $R; cd $S/tree-dev
run() { n=$1; shift; s=$(date +%s); { echo "# $n start $(date -u +%FT%TZ) cwd $S/tree-dev"; echo "# cmd: $*"; } > $R/$n.out
  "$@" >> $R/$n.out 2>&1 < /dev/null; rc=$?; echo "# rc=$rc wall=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)" >> $R/$n.out; echo "$n rc=$rc"; }
A=tests/bp-dtn7/run_fn_dtn7_app_receipt.py
run relay1-signed python3 $A --image $I/fn-host-dtn-developer --relays 1 --signed-receipts $I/fn-host --dtn7-repo /tank/fn/dtn7/repo --work $R/relay1-signed
echo "chainX end $(date -u +%FT%TZ)"; touch $S/done.X
