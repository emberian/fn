#!/bin/bash
# live-status native run on hbox; scratch only.
set -u
T=/tank/fn/scratch/live-status/cert-d73908ee
IMG=$T/build/fn-host-developer
R=/tank/fn/scratch/live-status/run
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
rm -rf $R; mkdir -p $R/out $R/p
cat > $R/fn.toml <<TOML
[store]
path = "$R/store"
[listener]
host = "127.0.0.1"
port = 11961
[auth]
required = false
protected_only = false
[posting]
enabled = true
[log]
path = "$R/fn.log"
[control]
path = "$R/control.sock"
TOML
op() { $IMG --fn operator $R/fn.toml "$@"; }
art() { printf 'From: live@example.invalid\r\nNewsgroups: fn.test\r\nSubject: live %s\r\nDate: Fri, 25 Sep 2026 09:00:00 +0000\r\nMessage-ID: <live-%s@example.invalid>\r\n\r\nbody %s\r\n' "$1" "$1" "$1" > $R/p/$1; }
post() { art $1; op post --message-id "<live-$1@example.invalid>" --payload $R/p/$1 --group fn.test; }
run() { name=$1; shift; s=$(date +%s.%N); op "$@" > $R/out/$name.out 2> $R/out/$name.err; c=$?; e=$(date +%s.%N); echo "$name exit=$c secs=$(echo "$e - $s" | bc)" | tee -a $R/out/summary.txt; }
op init --max-history-octets 1073741824 fn.test > $R/out/init.out 2>&1; echo "init exit=$?" | tee $R/out/summary.txt
run offline0-status status
systemd-run --user --unit fn-live-status-owner -p MemoryMax=24G --setenv FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX $IMG --fn operator $R/fn.toml run
for i in $(seq 100); do [ -S $R/control.sock ] && break; sleep 0.1; done
for i in 1 2 3; do post $i >> $R/out/posts0.txt 2>&1; done
run live-peer-add peer add far far.example 192.0.2.44 1119 "fn.*" "fn.*" 192.0.2.44 false
run live-status status
run live-pins pins
run live-obligations obligations
run live-peers peer list
# a held NNTP connection shows as a connection pin
python3 - <<PY &
import socket,time
s=socket.create_connection(("127.0.0.1",11961)); s.recv(512); time.sleep(4); s.close()
PY
sleep 1; run live-pins-connected pins; wait
timeout 3.6 $IMG --fn operator $R/fn.toml status --watch 1 > $R/out/watch.out 2> $R/out/watch.err; echo "watch reports=$(grep -c '^transactions=' $R/out/watch.out) tags=$(grep -c 'accepted operator status' $R/out/watch.err)" | tee -a $R/out/summary.txt
# POST burst with status asked throughout
( s=$(date +%s.%N); for i in $(seq 100 159); do post $i; echo "post $i exit=$?"; done > $R/out/burst-posts.txt 2>&1; e=$(date +%s.%N); echo "burst-with-status secs=$(echo "$e - $s" | bc)" >> $R/out/summary.txt ) &
BP=$!
for i in $(seq 1 20); do s=$(date +%s.%N); op status > $R/out/burst-status-$i.out 2>/dev/null; c=$?; e=$(date +%s.%N); echo "burst-status $i exit=$c secs=$(echo "$e - $s" | bc) tx=$(head -1 $R/out/burst-status-$i.out | cut -d' ' -f1)" >> $R/out/burst-status.txt; done
wait $BP
( s=$(date +%s.%N); for i in $(seq 200 259); do post $i; echo "post $i exit=$?"; done > $R/out/control-posts.txt 2>&1; e=$(date +%s.%N); echo "burst-without-status secs=$(echo "$e - $s" | bc)" >> $R/out/summary.txt )
run live-final-status status
run live-final-pins pins
run live-final-obligations obligations
run live-final-peers peer list
systemctl --user stop fn-live-status-owner; sleep 1
echo "owner unit: $(systemctl --user is-active fn-live-status-owner)" | tee -a $R/out/summary.txt
run off-status status
run off-pins pins
run off-obligations obligations
run off-peers peer list
for k in status pins obligations peers; do if cmp -s $R/out/live-final-$k.out $R/out/off-$k.out; then echo "equal $k" ; else echo "DIFF $k"; diff $R/out/live-final-$k.out $R/out/off-$k.out; fi; done | tee -a $R/out/summary.txt
echo "burst posts accepted: $(grep -c 'exit=0' $R/out/burst-posts.txt)/60 control: $(grep -c 'exit=0' $R/out/control-posts.txt)/60" | tee -a $R/out/summary.txt
sort -t= -k3 -n $R/out/burst-status.txt | tail -2 | tee -a $R/out/summary.txt
grep -c "exit=0" $R/out/burst-status.txt | sed 's/^/burst statuses ok: /' | tee -a $R/out/summary.txt
cd $R/out && sha256sum *.out *.txt > SHA256SUMS
