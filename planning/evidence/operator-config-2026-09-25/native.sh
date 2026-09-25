#!/bin/bash
# operator-config native run on hbox (scratch only; never /tank/fn/node).
# usage: native.sh TREE   (TREE holds build/fn-host built from the lane)
set -u
T=$1
IMG=${FN_IMG:-$T/build/fn-host-developer}
W=/tank/fn/scratch/operator-config/run
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
rm -rf $W; mkdir -p $W/out $W/p
O=$W/out
say() { echo "$*" | tee -a $O/summary.txt; }
fnop() { cfg=$1; shift; ACL2_CUSTOMIZATION=NONE $IMG --fn operator $cfg "$@"; }
cert() { n=$1; openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 \
  -subj "/CN=127.0.0.1" -addext "subjectAltName=IP:127.0.0.1" \
  -keyout $n/tls/key.pem -out $n/tls/cert.pem >/dev/null 2>&1; chmod 600 $n/tls/key.pem; }
art() { printf 'From: oc@example.invalid\r\nNewsgroups: local.test\r\nSubject: oc %s\r\nDate: Fri, 25 Sep 2026 20:00:00 +0000\r\nMessage-ID: <oc-%s@example.invalid>\r\n\r\nbody %s\r\n' "$1" "$1" "$1" > $W/p/$1; }
PORT=11960
for M in small-community relay archive; do
  N=$W/$M; mkdir -p $N; PORT=$((PORT+1)); C=$N/fn.toml
  fnop $C mission $M --port $PORT > $O/$M-mission.out 2> $O/$M-mission.err; say "$M mission exit=$?"
  fnop $C mission $M --port $PORT > /dev/null 2> $O/$M-mission-again.err; say "$M mission again exit=$? $(tail -1 $O/$M-mission-again.err)"
  cp $C $O/$M-fn.toml
  cert $N
  fnop $C show > $O/$M-show.out 2> $O/$M-show.err; say "$M show exit=$? same-as-file=$(cmp -s $C $O/$M-show.out && echo yes || echo no)"
  say "$M show alerts.headroom_min_percent=$(fnop $C show alerts headroom_min_percent 2>/dev/null) ops.mission=$(fnop $C show ops mission 2>/dev/null) posting.enabled=$(fnop $C show posting enabled 2>/dev/null)"
  if [ $M = small-community ]; then fnop $C init > $O/$M-init.out 2>&1; else fnop $C init fn.test > $O/$M-init.out 2>&1; fi
  say "$M init exit=$?"
  fnop $C status > $O/$M-status.out 2>&1; say "$M status: $(tr ' ' '\n' < $O/$M-status.out | grep -E '^(max-article-octets|max-groups-per-article)=' | tr '\n' ' ')"
  systemd-run --user --unit fn-oc-$M -p MemoryMax=24G --setenv FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX --setenv ACL2_CUSTOMIZATION=NONE $IMG --fn operator $C run > /dev/null 2>&1
  for i in $(seq 100); do [ -S $N/store/control.sock ] && break; sleep 0.1; done
  say "$M started: control-socket=$([ -S $N/store/control.sock ] && echo yes || echo no) listening=$(ss -ltnH | awk '{print $4}' | grep -cx 127.0.0.1:$PORT)"
done
# PKT-101: rotate by rename + SIGHUP on the small-community node while posting.
N=$W/small-community; C=$N/fn.toml; L=$N/log/fn.log
PID=$(systemctl --user show -p MainPID --value fn-oc-small-community)
( for i in $(seq 1 60); do art $i; fnop $C post --message-id "<oc-$i@example.invalid>" --payload $W/p/$i --group local.test; echo "post $i exit=$?"; done > $O/posts.txt 2>&1 ) &
BP=$!
sleep 3; mv $L $L.1; kill -HUP $PID; say "rotated at $(grep -c 'accepted post' $L.1) accepted lines; HUP sent to $PID"
sleep 3; mv $L $L.2 2>/dev/null; kill -HUP $PID; say "second rotation"
wait $BP
sleep 2
ACC=$(grep -c "exit=0" $O/posts.txt)
LINES=$(cat $L.1 $L.2 $L 2>/dev/null | grep -c '^accepted post')
say "posts exit0=$ACC accepted-post lines across fn.log.1 fn.log.2 fn.log = $LINES"
say "reopen lines: $(cat $L.1 $L.2 $L 2>/dev/null | grep -c '^reopened log')"
say "fn.log first line: $(head -1 $L)"
cp $L.1 $O/fn.log.1; cp $L.2 $O/fn.log.2 2>/dev/null; cp $L $O/fn.log
# the relay refuses posting by configuration
art relay1; fnop $W/relay/fn.toml post --message-id "<oc-relay1@example.invalid>" --payload $W/p/relay1 --group fn.test > $O/relay-post.out 2>&1; say "relay post exit=$? $(tail -1 $O/relay-post.out)"
# node-probe assertions over the small-community node (STARTTLS, login, post, read back)
printf 'probe-pass-1234\nprobe-pass-1234\n' | fnop $C principal set-password prober --posting > $O/principal.out 2>&1; say "principal exit=$?"
systemctl --user restart fn-oc-small-community; for i in $(seq 100); do [ -S $N/store/control.sock ] && ss -ltnH | grep -q 127.0.0.1:11961 && break; sleep 0.1; done
FN_PROBE_USER=prober FN_PROBE_PASSWORD=probe-pass-1234 python3 $T/tools/node_probe.py 127.0.0.1 11961 --cafile $N/tls/cert.pem --group local.test > $O/node-probe.out 2>&1; say "node_probe exit=$?"
for M in small-community relay archive; do systemctl --user stop fn-oc-$M; done
say "units: $(for M in small-community relay archive; do systemctl --user is-active fn-oc-$M; done | tr '\n' ' ')"
# PKT-069 file first: the signed-author ingress commits through the bound
# commit gate (fn-owner-bound-commit-gate): the signed cancel lands only in
# control.cancel, the signed ordinary article in fn.test.
( cd $T && FN_NATIVE_HOST=$IMG FN_RUN_HYBRID_E2E=1 FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl \
  python3 -m unittest -v tests.test_native_control_filing.NativeControlFilingTests.test_signed_author ) > $O/file-first.out 2>&1
say "file-first signed-author exit=$? $(grep -o 'NATIVE-CONTROL-WITNESS.*' $O/file-first.out | head -c 400)"
cd $O && sha256sum * > SHA256SUMS
