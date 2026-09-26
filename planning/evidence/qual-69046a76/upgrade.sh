#!/bin/sh
# qual-69046a76 facts 1b and 1c: the rehearsal, its two follow-ups, then the three new rollback consequences.
set -u
. /tank/fn/scratch/qual-69046a76/env.sh
unset LD_LIBRARY_PATH
cd $S
python3 upgrade_live.py > $S/logs/upgrade-live.log 2>&1; echo "rc=$?" >> $S/logs/upgrade-live.log
python3 upgrade_followup.py > $S/logs/upgrade-followup.log 2>&1; echo "rc=$?" >> $S/logs/upgrade-followup.log
python3 upgrade_followup2.py > $S/logs/upgrade-followup2.log 2>&1; echo "rc=$?" >> $S/logs/upgrade-followup2.log
python3 rollback3.py > $S/logs/rollback3.log 2>&1; echo "rc=$?" >> $S/logs/rollback3.log
touch $S/done.upgrade
