#!/bin/bash
# operator-health native run on hbox (scratch only; never /tank/fn/node).
# usage: native.sh TREE   (TREE holds build/fn-host-developer built from the lane)
# Produces each health state the native image can reach on a scratch node;
# every `health' run records its stdout, stderr and exit code.
set -u
T=$1
IMG=${FN_IMG:-$T/build/fn-host-developer}
W=/tank/fn/scratch/operator-health/run
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export ACL2_CUSTOMIZATION=NONE
for u in scale strand; do systemctl --user stop fn-oh-$u 2>/dev/null; systemctl --user reset-failed fn-oh-$u 2>/dev/null; done
rm -rf $W; mkdir -p $W/out $W/p
O=$W/out
say() { echo "$*" | tee -a $O/summary.txt; }
fnop() { cfg=$1; shift; $IMG --fn operator $cfg "$@"; }
fn() { $IMG --fn "$@"; }
cert() { n=$1; mkdir -p $n/tls; openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 \
  -subj "/CN=127.0.0.1" -addext "subjectAltName=IP:127.0.0.1" \
  -keyout $n/tls/key.pem -out $n/tls/cert.pem >/dev/null 2>&1; chmod 600 $n/tls/key.pem; }
art() { printf 'From: oh@example.invalid\r\nNewsgroups: local.test\r\nSubject: oh %s\r\nDate: Fri, 25 Sep 2026 23:00:00 +0000\r\nMessage-ID: <oh-%s@example.invalid>\r\n\r\nbody %s\r\n' "$1" "$1" "$1" > $W/p/$1; }
health() { # LABEL CONFIG
  local label=$1 cfg=$2
  timeout 60 $IMG --fn operator $cfg health > $O/$label.out 2> $O/$label.err
  local code=$?
  say "$label exit=$code first=$(head -1 $O/$label.out) held=[$(grep -E '^[a-z-]+ held' $O/$label.out | cut -d' ' -f1 | tr '\n' ' ')] unobserved=[$(grep -E '^[a-z-]+ unobserved' $O/$label.out | cut -d' ' -f1 | tr '\n' ' ')]"
}
node() { # NAME PORT PROFILE -> $W/NAME with fn.toml, tls, store
  local N=$W/$1; mkdir -p $N; fnop $N/fn.toml mission small-community --port $2 > $O/$1-mission.out 2>&1
  cert $N
  if [ $3 = mission ]; then
    fnop $N/fn.toml init > $O/$1-init.out 2>&1; say "$1 init (mission profile) exit=$?"
  else # a mission fixes the profile: drop it to choose one
    sed -i '/^mission=/d' $N/fn.toml
    fnop $N/fn.toml init --profile $3 local.test > $O/$1-init.out 2>&1; say "$1 init --profile $3 exit=$?"
  fi
}
start() { # NAME
  local N=$W/$1
  systemd-run --user --unit fn-oh-$1 -p MemoryMax=24G --setenv FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX \
    --setenv LD_LIBRARY_PATH=$LD_LIBRARY_PATH --setenv ACL2_CUSTOMIZATION=NONE \
    $IMG --fn operator $N/fn.toml run > /dev/null 2>&1
  for i in $(seq 200); do [ -S $N/store/control.sock ] && break; sleep 0.1; done
  say "$1 started: control-socket=$([ -S $N/store/control.sock ] && echo yes || echo no)"
}
stop() { systemctl --user stop fn-oh-$1; }

# 1. unqualified-profile (22), offline: the development profile.
node dev 31501 development
health unqualified-offline $W/dev/fn.toml

# 2. space-pressure (23), offline: the mission profile, headroom_min_percent 100.
node scale 31502 mission
health clear-offline $W/scale/fn.toml
art 0; fn store $W/scale/store post "<oh-0@example.invalid>" $W/p/0 - - local.test > $O/scale-post0.out 2>&1; say "offline post exit=$?"
sed -i 's/^headroom_min_percent=.*/headroom_min_percent=100/' $W/scale/fn.toml
say "scale alerts.headroom_min_percent=$(fnop $W/scale/fn.toml show alerts headroom_min_percent 2>/dev/null)"
health pressure-offline $W/scale/fn.toml
sed -i 's/^headroom_min_percent=.*/headroom_min_percent=10/' $W/scale/fn.toml

# 3. unavailable-peer (26), live: an outbound peer on a closed port, one post.
fnop $W/scale/fn.toml peer add hub hub.example 127.0.0.1 31599 - 'local.*' 127.0.0.1 true > $O/peer-add.out 2>&1; say "peer add exit=$? $(tail -1 $O/peer-add.out)"
start scale
health clear-live $W/scale/fn.toml
art 1; fnop $W/scale/fn.toml post --message-id "<oh-1@example.invalid>" --payload $W/p/1 --group local.test > $O/post1.out 2>&1; say "post exit=$?"
sleep 2
health unavailable-live $W/scale/fn.toml

# 4. fenced (20), store-held: the owner runs and the configured socket is gone.
mv $W/scale/store/control.sock $W/scale/store/control.sock.moved
health fenced-store-held $W/scale/fn.toml
mv $W/scale/store/control.sock.moved $W/scale/store/control.sock
# owner-unanswering: the owner is stopped (SIGSTOP) with its socket present.
PID=$(systemctl --user show -p MainPID --value fn-oh-scale)
if [ "${PID:-0}" -gt 1 ]; then kill -STOP $PID; health fenced-unanswering $W/scale/fn.toml; kill -CONT $PID; else say "no owner pid; fenced-unanswering not run"; fi
stop scale

# 5. stranded-transfer (25), live: a peer that answers 436 to every offer.
node strand 31503 mission
python3 $T/planning/evidence/operator-health-2026-09-25/defer_peer.py 31598 > $O/defer-peer.log 2>&1 &
DP=$!
fnop $W/strand/fn.toml peer add sink sink.example 127.0.0.1 31598 - 'local.*' 127.0.0.1 true > $O/peer-add-sink.out 2>&1; say "peer add sink exit=$?"
start strand
art 2; fnop $W/strand/fn.toml post --message-id "<oh-2@example.invalid>" --payload $W/p/2 --group local.test > $O/post2.out 2>&1; say "post exit=$?"
for i in $(seq 60); do
  timeout 60 $IMG --fn operator $W/strand/fn.toml health > $O/strand-poll.out 2>/dev/null
  [ $? = 25 ] && break; sleep 10
done
health stranded-live $W/strand/fn.toml
stop strand; kill $DP

# 6. no-route (24) then receipt-debt (27), offline: a forwarding obligation.
node fwd 31504 mission
S=$W/fwd/store
art 3; fn store $S post "<oh-3@example.invalid>" $W/p/3 - - local.test > $O/fwd-post.out 2>&1; say "fwd post exit=$?"
fn app-journal workflow-init $S $W/fwd/workflow dtn://fn-a/ dtn://fn-b/ policy-a authority-a 3600000 incarnation-a authorization-a > $O/wf-init.out 2>&1; say "workflow-init exit=$?"
fn app-journal workflow-enqueue $S $W/fwd/workflow 1 0 work-a "<oh-3@example.invalid>" forward-a dtn://fn-b/ policy-a terms-a > $O/wf-enq.out 2>&1; say "workflow-enqueue exit=$?"
fn bp-obligation undertake $S $W/fwd/workflow work-a 3 > $O/undertake.out 2>&1; say "undertake exit=$? $(tail -1 $O/undertake.out)"
health no-route-offline $W/fwd/fn.toml
fnop $W/fwd/fn.toml bp-boundary add fn-b fn-b.example dtn://fn-b/ 31597 > $O/bpb.out 2>&1; say "bp-boundary add exit=$? $(tail -1 $O/bpb.out)"
fnop $W/fwd/fn.toml bp-route add 'dtn://fn-b/*' fn-b > $O/bpr.out 2>&1; say "bp-route add exit=$? $(tail -1 $O/bpr.out)"
health receipt-debt-offline $W/fwd/fn.toml

say "units: $(for u in scale strand; do systemctl --user is-active fn-oh-$u; done | tr '\n' ' ')"
( cd $O && sha256sum *.out *.err > SHA256SUMS )
