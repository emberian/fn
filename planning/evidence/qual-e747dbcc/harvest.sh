#!/bin/sh
# qual-e747dbcc harvest: logs, judged tables, scripts; no store copies of the live node, no keys.
set -u
S=/tank/fn/scratch/qual-e747dbcc
H=$S/harvest; rm -rf $H; mkdir -p $H
C=$S/campaign
cd $S
cp campaign.sh chainA.sh chainB.sh chainC.sh run.sh setup.sh reloc.sh labs.sh marker_cuts.py d25b_matrix.py judge.py faults.py checkpoint_judge.py web-manual.py upgrade_live.py probe_budget.py probe_cost.py probe_cleanup_prod.py harvest.sh $H/ 2>/dev/null
cp campaign.out chainA.out chainB.out chainC.out image-check.log image-full.sha256 pylib.txt web-manual.log ss-before.txt $H/ 2>/dev/null
cp upgrade-live.log upgrade-live-run1.log upgrade-live-run2.log upgrade-live-run3.log upgrade-live/pristine-store.sha256 probe-budget.log $H/ 2>/dev/null
for f in campaign.log judged.md checkpoint-judged.md faults.txt marker-cuts.log nntp-probe.log crash-model.log d25-matrix.log pk-run.log pk-judged.md image-gated-test.log driver.sha256 image.sha256 run.start run.end ss-after.txt; do [ -e $C/$f ] && cp $C/$f $H/; done
for j in campaign nntp-probe pk-run marker-cuts; do [ -e $C/$j.json ] && gzip -9 -c $C/$j.json > $H/$j.json.gz; done
[ -e $C/d25-work/rows.json ] && gzip -9 -c $C/d25-work/rows.json > $H/d25-rows.json.gz
( cd $C && find work probe-work pk-work marker-work d25-work -name "*.err" 2>/dev/null | tar -czf $H/owner-logs.tgz -T - )
( cd $S/logs && tar -czf $H/native-logs.tgz *.log )
[ -d $S/request-labs ] && ( cd $S && tar -czf $H/request-labs.tgz --exclude="*.pem" --exclude="*.sec" request-labs )
( cd $S && tar -czf $H/web-manual.tgz --exclude=key.pem --exclude=credentials.toml --exclude=cred --exclude=store web )
( cd ~/fn-deploy/native-e747dbcc-d78ee77 && tar -czf $H/matrix-node-logs.tgz $(ls -d a/*.log a/fn.toml b/*.log b/fn.toml gate-run/*.log 2>/dev/null) 2>/dev/null )
( cd $H && for z in *.json.gz; do printf "%s  %s\n" "$(gunzip -c $z | sha256sum | cut -d" " -f1)" "${z%.gz}"; done > raw.sha256 )
( cd $H && sha256sum $(ls | grep -v SHA256SUMS) > SHA256SUMS )
ss -ltn > $H/ss-final.txt
ps -eo pid,cmd | grep -F "$S" | grep -v grep > $H/ps-final.txt || true
echo HARVEST-DONE $(ls $H | wc -l)
