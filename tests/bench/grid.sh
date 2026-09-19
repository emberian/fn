#!/bin/bash
# fn wave-3 scale grid.  Cheapest points first so a partial run is still a curve.
cd /tank/fn/scale
export FN_ACL2=/tank/fn/acl2-8.7/saved_acl2
B=build/bench
S=build/stores
mkdir -p $B $S
run() {  # name articles groups fanout payload profile runs extra...
  local name=$1 n=$2 g=$3 f=$4 p=$5 prof=$6 runs=$7; shift 7
  echo "=== $name n=$n g=$g fanout=$f p=$p profile=$prof $* $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)"
  rm -rf $S/$name
  timeout 5400 python3 tests/bench/generate.py --root $S/$name --articles $n \
      --groups $g --fanout $f --payload $p --seed 1 --profile $prof \
      --json $B/$name-gen.json "$@" >/dev/null || { echo "GEN FAILED $name"; return; }
  timeout 5400 python3 tests/bench/measure.py --root $S/$name --articles $n \
      --seed 1 --runs $runs --json $B/$name-meas.json >/dev/null || echo "MEAS FAILED $name"
  rm -rf $S/$name
}
for n in 16 32 64 128; do run n$n $n 2 2 1024 dev 5; done
for n in 256 512 1024; do run n$n $n 2 2 1024 scale 3; done
for p in 512 4096 16384 32768; do run p$p 64 2 2 $p dev 5; done
run g1 64 1 1 1024 dev 5
run g2f1 64 2 1 1024 dev 5
run stress-maxpayload 32 2 2 32768 dev 5
run stress-maxmsgid 32 2 2 4096 dev 5 --message-id-octets 250
run stress-folded 32 2 2 16384 dev 5 --payload-kind folded
run stress-all 32 2 2 32768 dev 5 --message-id-octets 250 --payload-kind folded
echo "=== grid complete $(date -Is)"
