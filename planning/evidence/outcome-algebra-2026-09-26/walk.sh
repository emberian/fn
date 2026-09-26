#!/bin/bash
# The operator walk (HST-008, SCN-076) on hbox scratch nodes, through the
# INSTALLED `fn` entry only (PREFIX/bin/fn from packaging/install-native.sh).
# Never /tank/fn/node.  usage: walk.sh IMAGE-DIR   (holds build/fn-host{,.core})
# Every step records its command, stdout, stderr and exit code under out/.
set -u
T=$1
B=/tank/fn/scratch/outcome-algebra/walk
W=$B/run
P=$B/prefix
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
for u in a b a2 copy nostream; do systemctl --user stop fn-oa-$u 2>/dev/null; systemctl --user reset-failed fn-oa-$u 2>/dev/null; done
rm -rf $W $P; mkdir -p $W/out $W/p
O=$W/out
N=0
say() { echo "$*" | tee -a $O/summary.txt; }
step() { # LABEL EXPECT CMD... : run one operator command, record it
  local label=$1 expect=$2; shift 2
  N=$((N + 1)); local f=$O/$(printf %02d $N)-$label
  echo "$*" > $f.cmd
  timeout 120 "$@" > $f.out 2> $f.err < /dev/null
  local rc=$?
  echo $rc > $f.rc
  say "$(printf %02d $N) $label exit=$rc expect=$expect $([ "$rc" = "$expect" ] && echo ok || echo DIFFERS) :: $(tail -1 $f.err | cut -c1-160)"
}
cert() { mkdir -p $1/tls; openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 \
  -subj "/CN=127.0.0.1" -addext "subjectAltName=IP:127.0.0.1" \
  -keyout $1/tls/key.pem -out $1/tls/cert.pem >/dev/null 2>&1; chmod 600 $1/tls/key.pem; }
art() { printf 'From: walk@example.invalid\r\nNewsgroups: local.test\r\nSubject: walk %s\r\nDate: Sat, 26 Sep 2026 02:00:00 +0000\r\nMessage-ID: <walk-%s@example.invalid>\r\n\r\nbody %s\r\n' "$1" "$1" "$1" > $W/p/$1; }
start() { # NAME : waits for the listener, not the socket file (a killed owner leaves a stale one)
  local port; port=$(awk -F= '/^port=/{print $2; exit}' $W/$1/fn.toml)
  systemd-run --user --unit fn-oa-$1 -p MemoryMax=24G --setenv FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX \
    --setenv LD_LIBRARY_PATH=$LD_LIBRARY_PATH $FN operator $W/$1/fn.toml run > /dev/null 2>&1
  for i in $(seq 600); do ss -ltnH "sport = :$port" | grep -q . && break; sleep 0.1; done
  say "   start $1: listening=$(ss -ltnH "sport = :$port" | grep -q . && echo yes || echo no) control-socket=$([ -S $W/$1/store/control.sock ] && echo yes || echo no)"
}
stop() { systemctl --user stop fn-oa-$1; say "   stop $1: $(systemctl --user is-active fn-oa-$1)"; }

# 0. Install: the packaging step an operator runs, into a scratch prefix.
( cd $T && FN_NATIVE_HOST=$T/build/fn-host FN_NATIVE_CORE=$T/build/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=$(cat $T/REVISION 2>/dev/null || echo lane) PREFIX=$P \
  sh packaging/install-native.sh ) > $O/00-install.out 2>&1
say "00 install exit=$? :: $(tail -1 $O/00-install.out)"
FN=$P/bin/fn
sha256sum $FN $P/libexec/fn/fn-host $P/libexec/fn/fn-host.core > $O/installed.sha256

A=$W/a/fn.toml; Bc=$W/b/fn.toml
mkdir -p $W/a $W/b
step help 0 $FN operator $A help
step status-no-config 5 $FN operator $A status
step mission-a 0 $FN operator $A mission small-community --port 31601
cert $W/a
# HST-009 (specs/host.md "CLI exit codes"): NO-STORE is the refused class, 1.
step status-never-initialized 1 $FN operator $A status
step health-never-initialized 1 $FN operator $A health
step run-never-initialized 1 $FN operator $A run --once
step init-profile-under-mission 5 $FN operator $A init --profile scale
step init-a 0 $FN operator $A init
step init-again 1 $FN operator $A init
step show-port 0 $FN operator $A show listener port
step path-identity-a 0 $FN operator $A policy set path-identity a.walk.invalid
step status-offline-a 0 $FN operator $A status
step health-offline-a 19 $FN operator $A health

# B, the second node, and enrolment of a login on A.
step mission-b 0 $FN operator $Bc mission small-community --port 31602
cert $W/b
step init-b 0 $FN operator $Bc init
step path-identity-b 0 $FN operator $Bc policy set path-identity b.walk.invalid
N=$((N + 1)); f=$O/$(printf %02d $N)-enrol-login
echo "$FN operator $A principal set-password walker --posting (password on the terminal)" > $f.cmd
printf 'walk-secret-1\nwalk-secret-1\n' | timeout 60 script -qec "$FN operator $A principal set-password walker --posting" /dev/null > $f.out 2> $f.err
echo $? > $f.rc; say "$(printf %02d $N) enrol-login exit=$(cat $f.rc) expect=0 :: $(tail -1 $f.out | tr -d '\r' | cut -c1-160)"
step principal-list 0 $FN operator $A principal list

# Peering: A feeds B local.*, B accepts from A; both stopped (offline records).
step peer-add-a-to-b 0 $FN operator $A peer add b b.walk.invalid 127.0.0.1 31602 - 'local.*' 127.0.0.1 true
step peer-add-b-from-a 0 $FN operator $Bc peer add a a.walk.invalid 127.0.0.1 31601 'local.*' - 127.0.0.1 true
step peer-list-a 0 $FN operator $A peer list
start a; start b
step status-live-a 0 $FN operator $A status
art 1; step post-a 0 $FN operator $A post --message-id '<walk-1@example.invalid>' --payload $W/p/1 --group local.test
sleep 8
step status-live-b 0 $FN operator $Bc status
step health-live-a 0 $FN operator $A health
# Budget refusal: an article over the mission's article bound (1 MiB).
head -c 1100000 /dev/zero | tr '\0' 'x' > $W/p/big.body
{ printf 'From: walk@example.invalid\r\nNewsgroups: local.test\r\nSubject: big\r\nMessage-ID: <walk-big@example.invalid>\r\n\r\n'; cat $W/p/big.body; printf '\r\n'; } > $W/p/big
step post-over-budget 1 $FN operator $A post --message-id '<walk-big@example.invalid>' --payload $W/p/big --group local.test
# Logs.
cp $W/a/log/fn.log $O/a-fn.log 2>/dev/null; cp $W/b/log/fn.log $O/b-fn.log 2>/dev/null
say "   logs: a $(wc -l < $O/a-fn.log 2>/dev/null) lines, b $(wc -l < $O/b-fn.log 2>/dev/null) lines; b accepted-peer=$(grep -c 'accepted peer' $O/b-fn.log 2>/dev/null) a feed-lines=$(grep -c ' feed ' $O/a-fn.log 2>/dev/null)"

# (c) A peer that answers 501 to MODE STREAM: A is given a streaming peer
# `nostream'; it must be stopped by name, not re-dialled.
stop a
step peer-add-nostream 0 $FN operator $A peer add nostream ns.walk.invalid 127.0.0.1 31603 - 'local.*' 127.0.0.9 true
systemd-run --user --unit fn-oa-nostream -p MemoryMax=1G python3 $T/planning/evidence/operator-walk-2026-09-26/nostream_peer.py 31603 > /dev/null 2>&1
sleep 1; start a
art 2; step post-a-2 0 $FN operator $A post --message-id '<walk-2@example.invalid>' --payload $W/p/2 --group local.test
sleep 40
journalctl --user -u fn-oa-nostream --no-pager -o cat > $O/nostream.log 2>&1
cp $W/a/log/fn.log $O/a-fn.log
say "   nostream: MODE STREAM received $(grep -c '^MODE STREAM' $O/nostream.log) times in 40 s; a log stop lines $(grep -c 'reason=mode-stream-refused' $O/a-fn.log)"
step health-live-a-nostream 26 $FN operator $A health
systemctl --user stop fn-oa-nostream

# Backup: stop, copy.  The snapshot for the rollback rehearsal.
stop a
cp -a $W/a/store $W/snapshot-store; say "   backup: cp -a of the stopped store -> snapshot-store"
start a
art 3; step post-a-3 0 $FN operator $A post --message-id '<walk-3@example.invalid>' --payload $W/p/3 --group local.test
art 4; step post-a-4 0 $FN operator $A post --message-id '<walk-4@example.invalid>' --payload $W/p/4 --group local.test
stop a

# Upgrade rehearsal on a copy (rewritten paths, loopback), then rollback.
mkdir -p $W/copy; cp -a $W/a/store $W/copy/store; cp -a $W/a/tls $W/copy/tls; mkdir -p $W/copy/log
sed -e "s|$W/a/|$W/copy/|g" -e 's/^port=31601/port=31611/' $A > $W/copy/fn.toml
C=$W/copy/fn.toml
cp -p $W/copy/store/config.json $W/copy/config.json.kept
step needs-upgrade 0 $FN operator $C store needs-upgrade
step upgrade-profile-scale 1 $FN operator $C store upgrade-profile scale
step upgrade-profile-raise 0 $FN operator $C store upgrade-profile --max-history-octets 2199023255552
step rollback-check-kept 0 $FN operator $C store rollback-check $W/copy/config.json.kept
step upgrade-required 0 $FN operator $C store upgrade-profile --history-marker required
step rollback-check-kept-required 1 $FN operator $C store rollback-check $W/copy/config.json.kept
step rollback-check-snapshot 0 $FN operator $C store rollback-check --snapshot $W/snapshot-store
step rollback-check-foreign 1 $FN operator $C store rollback-check --snapshot $W/b/store
# The rollback itself: the snapshot replaces the copy's store.
rm -rf $W/copy/store; cp -a $W/snapshot-store $W/copy/store
step recover-after-rollback 0 $FN operator $C recover
step status-after-rollback 0 $FN operator $C status

# Crash and recovery on A: SIGKILL the owner, then recover and run.
start a
systemctl --user kill -s KILL fn-oa-a; sleep 2; say "   crash: SIGKILL, unit $(systemctl --user is-active fn-oa-a)"
systemctl --user reset-failed fn-oa-a 2>/dev/null
say "   after crash: stale control socket $([ -S $W/a/store/control.sock ] && echo present || echo absent)"
step status-after-crash 0 $FN operator $A status
step recover-after-crash 0 $FN operator $A recover
start a
step health-recovered 26 $FN operator $A health
step status-recovered 0 $FN operator $A status
stop a; stop b
cp $W/a/log/fn.log $O/a-fn.log
(cd $O && sha256sum * > SHA256SUMS)
say "done"
