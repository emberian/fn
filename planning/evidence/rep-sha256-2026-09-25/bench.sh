#!/bin/sh
# usage: bench.sh TREE -- the digest microbenchmark in one ACL2 over the certified books, under a memory cap
T=$1; S=/tank/fn/scratch/rep-sha256
cd $T
systemd-run --user --wait --pipe -p MemoryMax=24G /tank/fn/toolchains/w28/acl2-literal-4g < $S/bench.lisp > $S/bench.out 2>&1
echo bench rc=$?; grep -E "^BENCH|list-model:|stobj:|string:|attached:|ASSERT|Error" $S/bench.out
