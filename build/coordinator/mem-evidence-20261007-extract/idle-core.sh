#!/bin/sh
# usage: idle-core.sh CORE TLS HEAPMB  -- stock sbcl runtime on CORE, fn launcher options, idle (sleep 9), read at 6 s
SB=/tank/fn/sbcl; export SBCL_HOME=$SB/lib/sbcl/
$SB/bin/sbcl --tls-limit $2 --dynamic-space-size ${3}MB --control-stack-size 1024KB --disable-ldb \
  --core $1 --noinform --end-runtime-options --no-userinit --no-sysinit --eval '(sleep 9)' \
  --disable-debugger --end-toplevel-options >/dev/null 2>&1 &
P=$!; sleep 6
echo "core=$1 tls=$2 heap=${3}MB load=$(cut -d' ' -f1-3 /proc/loadavg)"
grep -E 'VmRSS|VmHWM' /proc/$P/status | tr -s ' \t' ' ' | tr '\n' ' '; echo
grep -E '^(Rss|Anonymous|Pss_File)' /proc/$P/smaps_rollup | tr -s ' ' | tr '\n' ' '; echo
awk -v c="$1" '$6==c{f=1;next} /^[0-9a-f]+-[0-9a-f]+ /{f=0} f&&/^Rss:/{s+=$2} END{print "core-mapping Rss kB:",s+0}' /proc/$P/smaps
wait $P
