#!/bin/sh
# runcap.sh TAG LIMIT(0=none)
tag=$1; L=$2
if [ $tag = conv ]; then B=/tank/fn/scratch/integrate-20261011a/native-3119f7d3253e/tree/build; else B=/tank/fn/scratch/drain/native-drain-c0e35e156/tree/build; fi
d=/tank/fn/scratch/m19/fresh/$tag; out=/tank/fn/scratch/m19/fresh/run-$tag-$L
rm -f $out.*
pre=""; [ "$L" != 0 ] && pre="systemd-run --user --scope --quiet -p MemoryMax=${L}M -p MemorySwapMax=0"
SBCL_HOME=/tank/fn/sbcl/lib/sbcl/ $pre timeout 150 /tank/fn/sbcl/bin/sbcl --tls-limit 16384 --dynamic-space-size 1068MB --control-stack-size 1024KB --disable-ldb --core $B/fn-host.core --noinform --end-runtime-options --no-userinit --load /tank/fn/scratch/m19/fresh/cap.lisp --eval "(acl2::sbcl-restart)" --disable-debugger --end-toplevel-options --fn operator $d/fn.toml run > $out.stdout 2> $out.stderr &
echo $! > $out.pid
i=0; while [ $i -lt 120 ]; do grep -q LISTENING $out.stdout 2>/dev/null && break; kill -0 $(cat $out.pid) 2>/dev/null || break; sleep 1; i=$((i+1)); done
grep -q LISTENING $out.stdout && echo "$tag $L LISTENING after ${i}s" || echo "$tag $L no LISTENING"
grep -h "VmRSS\|VmHWM\|RssAnon\|RssFile" /proc/$(cat $out.pid)/status 2>/dev/null | tr -s " " | tr "\n" " "; echo
kill -0 $(cat $out.pid) 2>/dev/null && kill $(cat $out.pid)
sleep 3
grep -ih "capacity\|refused" $out.stdout $out.stderr | head -5
