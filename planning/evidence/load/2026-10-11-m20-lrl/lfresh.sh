#!/bin/sh
# lfresh.sh LAUNCHER TAG LIMIT_MB : L-FRESH as an installed node starts: a fresh small-preset store (operator init
# with the cell's flags), the launcher's own heap probe under systemd-run MemoryMax=LIMIT, one POST and one ARTICLE,
# VmHWM of the image process; stops the run by the PID file it wrote.
IMG=$1; tag=$2; L=$3
W=/dev/shm/m20/lf-$tag-$L; rm -rf $W; mkdir -p $W
port=$((39800 + L % 97)); printf '[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/c.sock"\n' $W $port $W > $W/fn.toml
timeout 300 $IMG --fn operator $W/fn.toml init --profile development --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128 fn.letters fn.test > $W/init.log 2>&1
timeout 120 systemd-run --user --scope --quiet -p MemoryMax=${L}M -p MemorySwapMax=0 $IMG --fn heap -- operator $W/fn.toml run > $W/probe.out 2>&1
echo "probe: $(cat $W/probe.out | tr '\n' ' ')"
timeout 200 systemd-run --user --scope --quiet -p MemoryMax=${L}M -p MemorySwapMax=0 $IMG --fn operator $W/fn.toml run > $W/stdout 2> $W/stderr &
echo $! > $W/pid
i=0; while [ $i -lt 150 ]; do grep -q LISTENING $W/stdout 2>/dev/null && break; kill -0 $(cat $W/pid) 2>/dev/null || break; sleep 1; i=$((i+1)); done
if grep -q LISTENING $W/stdout; then
python3 - $port <<"PY"
import socket,sys,time
s=socket.create_connection(("127.0.0.1",int(sys.argv[1])),timeout=30); f=s.makefile("rwb")
def line(): return f.readline().decode().strip()
print("greet",line())
mid="<m20-%d@fresh.invalid>"%time.time_ns()
f.write(b"POST\r\n"); f.flush(); print("post?",line())
body=("From: m20 <m20@fresh.invalid>\r\nNewsgroups: fn.test\r\nSubject: fresh\r\nMessage-ID: %s\r\n\r\n%s\r\n.\r\n"%(mid,"x"*2000)).encode()
f.write(body); f.flush(); print("post",line())
f.write(("ARTICLE %s\r\n"%mid).encode()); f.flush(); print("article",line())
PY
for c in $(pgrep -P $(cat $W/pid)) ; do grep -h "VmHWM\|VmRSS\|RssAnon\|RssFile" /proc/$c/status 2>/dev/null | tr -s " \t" " " | tr "\n" " "; done; echo
else echo "$tag $L no LISTENING after ${i}s"; fi
kill -0 $(cat $W/pid) 2>/dev/null && kill $(cat $W/pid); sleep 3
grep -h "capacity\|refused" $W/stdout $W/stderr | head -4
