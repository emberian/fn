#!/bin/sh
# Time `store probe N` (x payload) against `store probe N article` on the 59654ce8 image.
set -u
T=/tank/fn/scratch/bounds-p5/tree5; M=/tank/fn/scratch/bounds-p5/measure2
export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf $M; mkdir -p $M; cd $T
port=41900
for n in 2000 4000 8000; do for f in plain article; do
  S=$M/$f-$n; port=$((port+1))
  printf "[store]\npath = \"%s\"\n[listener]\nhost = \"127.0.0.1\"\nport = %d\n[control]\npath = \"%s\"\n" $S $port $M/$f-$n.sock > $S.toml
  build/fn-host-developer --fn operator $S.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test >/dev/null 2>&1
  a=""; [ $f = article ] && a=article
  s=$(date +%s.%N); build/fn-host-developer --fn store $S probe $n $a > $S.out 2>&1; rc=$?; e=$(date +%s.%N)
  echo "n=$n form=$f rc=$rc wall=$(echo "$e - $s" | bc) $(cat $S.out | tail -1)"
  rm -rf $S
done; done
