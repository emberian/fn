#!/bin/sh
# usage: probe_measure.sh N [profile flags...]
set -u
S=/tank/fn/scratch/bounds-p5
T=$S/${TREE:-tree}
N=$1; shift
W=${BASE:-$S/measure}/n$N; rm -rf $W; mkdir -p $W
cd $T
export ACL2_CUSTOMIZATION=NONE
P=/tank/fn/toolchains/openssl-3.5.8; L=$P/lib64; [ -d $L ] || L=$P/lib; export LD_LIBRARY_PATH=$L
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
./build/fn-host-developer --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1
echo "init rc=$?"
/usr/bin/time -v ./build/fn-host-developer --fn store $W/store probe $N > $W/probe.out 2> $W/probe.err
echo "probe rc=$?"; cat $W/probe.out; grep -E "Elapsed|Maximum resident" $W/probe.err
