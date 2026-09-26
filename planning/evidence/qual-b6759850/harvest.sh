#!/bin/sh
# qual-b6759850 harvest: logs, judged tables, scripts; no store copies, no keys, no credentials.
set -u
S=/tank/fn/scratch/qual-b6759850
H=$S/harvest; rm -rf $H; mkdir -p $H
cd $S
cp env.sh setup.sh brun.sh chainM.sh chainB.sh labs.sh campaign.sh ckpt.sh probe_maxart.py upgrade_live.py upgrade_followup.py upgrade_followup2.py s15.sh mixed.py probe_budget.py probe_count.py probe_smalldisk.sh webnode.py protected.py rerun.sh reloc.sh scm.sh opwalk.sh matched.sh post.py table.py judge.py checkpoint_judge.py marker_cuts.py d25b_matrix.py harvest.sh $H/ 2>/dev/null
cp upgrade-live.log upgrade-followup.log upgrade-followup2.log protected.log webnode.log probe-count.log smalldisk.log mixed.log image-check.log image-full.sha256 build-log-scan.txt pylib.txt module-table.md served-crash-model-harness.diff campaign.out chainM.out chainB.out rerun.out ckpt.out s15.out $H/ 2>/dev/null
cp upgrade-live/pristine-store.sha256 $H/ 2>/dev/null
mkdir -p $H/ckpt; cp ckpt/maxart.log ckpt/rep.log ckpt/n2048.json ckpt/status-after.txt ckpt/status-again.txt ckpt/checkpoint.sha256 ckpt/live.log ckpt/summary.txt ckpt/store-ls.txt $H/ckpt/ 2>/dev/null
mkdir -p $H/s15; cp s15/rcs s15/n300.jsonl s15/tight.jsonl s15/probe-budget.log s15/n300.err s15/tight.err $H/s15/ 2>/dev/null
mkdir -p $H/campaign; for f in campaign.log judged.md checkpoint-judged.md marker-cuts.log nntp-probe.log crash-model.log d25-matrix.log pk-run.log pk-judged.md image-gated-test.log driver.sha256 image.sha256 run.start run.end ss-before.txt ss-after.txt; do [ -e campaign/$f ] && cp campaign/$f $H/campaign/; done
for j in campaign nntp-probe pk-run marker-cuts; do [ -e campaign/$j.json ] && gzip -9 -c campaign/$j.json > $H/campaign/$j.json.gz; done
mkdir -p $H/matched; cp matched/probe.log matched/post.log matched/images.sha256 $H/matched/ 2>/dev/null
[ -e mixed/mixed.json ] && gzip -9 -c mixed/mixed.json > $H/mixed.json.gz
cp operator-walk/run/out/summary.txt $H/opwalk-summary.txt 2>/dev/null
( cd operator-walk/run && tar -czf $H/opwalk-out.tgz out ) 2>/dev/null
( tar -czf $H/native-logs.tgz blogs logs breport-*.json killed-*.txt ) 2>/dev/null
( tar -czf $H/request-labs.tgz --exclude="*.pem" --exclude="*.sec" --exclude="*secret*" request-labs/rcs request-labs/*.out request-labs/image.sha256 missions/rcs missions/*.out $(ls missions/*/report.json 2>/dev/null) ) 2>/dev/null
( cd $H && sha256sum $(find . -type f ! -name SHA256SUMS | sort) > SHA256SUMS )
ss -ltn > $H/ss-final.txt
ps -eo pid,cmd | grep -F "$S" | grep -v grep > $H/ps-final.txt || true
echo HARVEST-DONE $(find $H -type f | wc -l)
