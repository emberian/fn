#!/bin/sh
set -u
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
S=/tank/fn/scratch/deploy-fixes; M=$S/migrated; L=$S/logs
T=$S/tree; IMG=$T/build/fn-host
rm -rf $M; cp -a /tank/fn/scratch/qual-e747dbcc/upgrade-live/w $M
sed -i "s#/tank/fn/scratch/qual-e747dbcc/upgrade-live/w#$M#g" $M/fn.toml
{
echo "# deploy-fixes U1 native case: production image $(sha256sum $IMG.core | cut -c1-16) on a cp -a of qual-e747dbcc's migrated copy of the live store (format 8, history-marker required, kept config.json.format-7)"
grep -n "path" $M/fn.toml
cd $T
echo "## status"; $IMG --fn operator $M/fn.toml status > $S/status.out 2>&1; echo "rc=$?"; grep -io "history-marker=[a-z0-9]*" $S/status.out
echo "## needs-upgrade"; $IMG --fn operator $M/fn.toml store needs-upgrade 2>&1; echo "rc=$?"
echo "## rollback-check config.json.format-7 (was: rollback sound on e747dbcc)"; $IMG --fn operator $M/fn.toml store rollback-check $M/store/config.json.format-7 2>&1; echo "rc=$?"
echo "## rollback-check of the store's own config.json (required over required)"; cp -p $M/store/config.json $S/config.json.required; $IMG --fn operator $M/fn.toml store rollback-check $S/config.json.required 2>&1; echo "rc=$?"
echo "## control list offline"; $IMG --fn operator $M/fn.toml control list 2>&1; echo "rc=$?"
} > $L/u1-migrated.log 2>&1
cat $L/u1-migrated.log
cd $L && sha256sum *.log
