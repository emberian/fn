#!/bin/sh
# fresh_core.sh IMG TAG LIMIT : start IMG on the conv store under MemoryMax, POST and ARTICLE once, stop by PID file
IMG=$1; tag=$2; L=$3; d=/tank/fn/scratch/m19/fresh/conv; out=/tank/fn/scratch/m19/fresh/fc-$tag-$L
rm -f $out.*
timeout 200 systemd-run --user --scope --quiet -p MemoryMax=${L}M -p MemorySwapMax=0 $IMG --fn operator $d/fn.toml run > $out.stdout 2> $out.stderr &
echo $! > $out.pid
i=0; while [ $i -lt 150 ]; do grep -q LISTENING $out.stdout 2>/dev/null && break; kill -0 $(cat $out.pid) 2>/dev/null || break; sleep 1; i=$((i+1)); done
if grep -q LISTENING $out.stdout; then
  port=$(grep -o "port = [0-9]*" $d/fn.toml | grep -o "[0-9]*$")
  python3 - $port <<"PY"
import socket,sys,time
s=socket.create_connection(("127.0.0.1",int(sys.argv[1])),timeout=30); f=s.makefile("rwb")
def line(): return f.readline().decode().strip()
print("greet",line())
mid="<m19-%d@fresh.invalid>"%time.time_ns()
f.write(b"POST\r\n"); f.flush(); print("post?",line())
body=("From: m19 <m19@fresh.invalid>\r\nNewsgroups: fn.test\r\nSubject: fresh\r\nMessage-ID: %s\r\n\r\n%s\r\n.\r\n"%(mid,"x"*2000)).encode()
f.write(body); f.flush(); print("post",line())
f.write(("ARTICLE %s\r\n"%mid).encode()); f.flush(); print("article",line())
PY
  pid=$(pgrep -P $(cat $out.pid) | head -1); [ -n "$pid" ] && grep -h "VmHWM\|VmRSS\|RssAnon\|RssFile" /proc/$pid/status | tr -s " \t" " " | tr "\n" " "; echo
else echo "$tag $L no LISTENING after ${i}s"; fi
kill -0 $(cat $out.pid) 2>/dev/null && kill $(cat $out.pid); sleep 3
grep -h "capacity\|refused\|LISTENING" $out.stdout $out.stderr | head -4
