#!/bin/sh
# qual-dfa810fc harvest: logs, judged tables, scripts; no store copies, no keys, no credentials, no codes.
set -u
S=/tank/fn/scratch/qual-dfa810fc
H=$S/harvest; rm -rf $H; mkdir -p $H
cd $S
cp env.sh setup.sh brun.sh chainM.sh chainB.sh labs.sh campaign.sh ckpt.sh probe_maxart.py upgrade.sh upgrade_live.py upgrade_followup.py upgrade_followup2.py rollback3.py friends.sh friends_signed.py oldclient.py bigart.py bigreply.py s15.sh mixed.py probe_budget.py probe_count.py probe_smalldisk.sh webnode.py opwalk.sh reloc.sh tin_walk.py table.py judge.py checkpoint_judge.py marker_cuts.py d25b_matrix.py harvest.sh $H/ 2>/dev/null
cp image-check.log image-full.sha256 build-log-scan.txt pylib.txt module-table.md $H/
mkdir -p $H/logs; cp logs/*.log $H/logs/ 2>/dev/null
mkdir -p $H/run1-contaminated; cp run1-contaminated/*.log $H/run1-contaminated/
mkdir -p $H/ckpt; cp ckpt/maxart.log ckpt/rep.log ckpt/n2048.json ckpt/status-after.txt ckpt/status-again.txt ckpt/checkpoint.sha256 ckpt/live.log ckpt/summary.txt $H/ckpt/ 2>/dev/null
mkdir -p $H/friends; cp friends/*.log friends/summary.txt $H/friends/; sha256sum friends/release/*.tar.gz > $H/friends/tarball.sha256
mkdir -p $H/s15; cp s15/rcs s15/n300.jsonl s15/tight.jsonl s15/probe-budget.log s15/probe-count.log s15/smalldisk.log s15/chain20000.log $H/s15/ 2>/dev/null
mkdir -p $H/campaign; for f in campaign.log judged.md checkpoint-judged.md marker-cuts.log nntp-probe.log crash-model.log d25-matrix.log pk-run.log pk-judged.md image-gated-test.log driver.sha256 image.sha256 run.start ss-before.txt; do [ -e campaign/$f ] && cp campaign/$f $H/campaign/; done
for j in campaign nntp-probe pk-run marker-cuts; do [ -e campaign/$j.json ] && gzip -9 -c campaign/$j.json > $H/campaign/$j.json.gz; done
mkdir -p $H/tin-walk; cp tin-walk/readback.txt tin-walk/owner.log tin-walk/walk.log $H/tin-walk/ 2>/dev/null; ( cd tin-walk && tar -czf $H/tin-walk/screens.tgz screens )
[ -e mixed/mixed.json ] && gzip -9 -c mixed/mixed.json > $H/mixed.json.gz
cp mixed/service.log $H/mixed-service.log 2>/dev/null; cp mixed/owner.stderr $H/mixed-owner.stderr 2>/dev/null
cp operator-walk/run/out/summary.txt $H/opwalk-summary.txt 2>/dev/null
( cd operator-walk/run && tar -czf $H/opwalk-out.tgz out ) 2>/dev/null
( tar -czf $H/native-logs.tgz blogs breport-*.json killed-*.txt logs/budget-*.log ) 2>/dev/null
( tar -czf $H/request-labs.tgz request-labs/rcs request-labs/*.out request-labs/image.sha256 missions/rcs missions/*.out $(ls missions/*/report.json 2>/dev/null) ) 2>/dev/null
sed -i -E "s/XREDEEM [0-9a-f]{32}/XREDEEM <code>/g" $H/logs/rollback3.log $H/run1-contaminated/rollback3.log
( cd $H && sha256sum $(find . -type f ! -name SHA256SUMS | sort) > SHA256SUMS )
echo HARVEST-DONE $(find $H -type f | wc -l)
