#!/bin/bash
# status-join native run on hbox; scratch only.  Offline and live status,
# byte for byte, on a store with max-history-octets = 2^40, before and after
# a published state checkpoint.
set -u
T=/tank/fn/scratch/status-join/tree
IMG=$T/build/fn-host-developer
R=/tank/fn/scratch/status-join/run
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $R; mkdir -p $R/out $R/p
cat > $R/fn.toml <<TOML
[store]
path = "$R/store"
[listener]
host = "127.0.0.1"
port = 11963
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
art() { printf 'From: sj@example.invalid\r\nNewsgroups: fn.test\r\nSubject: sj %s\r\nDate: Fri, 25 Sep 2026 09:00:00 +0000\r\nMessage-ID: <sj-%s@example.invalid>\r\n\r\nbody %s\r\n' "$1" "$1" "$1" > $R/p/$1; }
post() { art $1; op post --message-id "<sj-$1@example.invalid>" --payload $R/p/$1 --group fn.test; }
run() { name=$1; shift; op "$@" > $R/out/$name.out 2> $R/out/$name.err; echo "$name exit=$?" | tee -a $R/out/summary.txt; }
start() { systemd-run --user --unit fn-status-join-owner -p MemoryMax=24G --setenv FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX --setenv LD_LIBRARY_PATH=$LD_LIBRARY_PATH $IMG --fn operator $R/fn.toml run; for i in $(seq 100); do [ -S $R/control.sock ] && break; sleep 0.1; done; }
stop() { systemctl --user stop fn-status-join-owner; sleep 1; echo "owner unit: $(systemctl --user is-active fn-status-join-owner)" | tee -a $R/out/summary.txt; }
op init --max-history-octets 1099511627776 fn.test > $R/out/init.out 2>&1; echo "init exit=$?" | tee $R/out/summary.txt
start
for i in 1 2 3; do post $i >> $R/out/posts.txt 2>&1; done
run live-a-status status
stop
run off-a-status status
run checkpoint store checkpoint
start
run live-b-status status
stop
run off-b-status status
for k in a b; do if cmp -s $R/out/live-$k-status.out $R/out/off-$k-status.out; then echo "equal $k"; else echo "DIFF $k"; diff $R/out/live-$k-status.out $R/out/off-$k-status.out; fi; done | tee -a $R/out/summary.txt
for k in live-a off-a live-b off-b; do echo "== $k"; grep -E 'history-marker|max-history-octets|history-bound|^checkpoint-file|^open-cost' $R/out/$k-status.out; done | tee -a $R/out/summary.txt
ls -l $R/store/state 2>/dev/null | tee -a $R/out/summary.txt
cd $R/out && sha256sum *.out *.txt > SHA256SUMS
