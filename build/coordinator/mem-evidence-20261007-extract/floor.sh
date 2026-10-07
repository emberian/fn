#!/bin/sh
# usage: floor.sh TLS HEAPMB   -- plain SBCL, stock core, fn launcher options, idle 6 s
# prints VmRSS/VmHWM, smaps Rss of the core mapping, anon (smaps_rollup), at 4 s.
SB=/tank/fn/sbcl; export SBCL_HOME=$SB/lib/sbcl/
CORE=$SB/lib/sbcl/sbcl.core
$SB/bin/sbcl --tls-limit $1 --dynamic-space-size ${2}MB --control-stack-size 1024KB --disable-ldb \
  --core $CORE --noinform --end-runtime-options --no-userinit --no-sysinit --eval '(sleep 6)' \
  --disable-debugger --end-toplevel-options >/dev/null 2>&1 &
P=$!; sleep 4
echo "tls=$1 heap=${2}MB load=$(cut -d' ' -f1-3 /proc/loadavg)"
grep -E 'VmRSS|VmHWM' /proc/$P/status | tr -s ' \t' ' ' | tr '\n' ' '; echo
grep -E '^(Rss|Anonymous|Pss_File|Pss_Anon)' /proc/$P/smaps_rollup | tr -s ' ' | tr '\n' ' '; echo
awk -v c="$CORE" '$6==c{f=1;next} /^[0-9a-f]+-[0-9a-f]+ /{f=0} f&&/^Rss:/{s+=$2} END{print "core-mapping Rss kB:",s+0}' /proc/$P/smaps
wait $P
