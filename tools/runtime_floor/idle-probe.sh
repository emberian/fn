#!/bin/sh
# idle-probe.sh LABEL CMD...: start CMD, after 2 s print its memory lines
label=$1; shift
"$@" > /dev/null 2>&1 &
p=$!
sleep 2
echo "$label $(grep -E "VmSize|VmRSS|RssAnon|RssFile" /proc/$p/status | tr -s " \t" " " | tr "\n" " ")"
wait $p
