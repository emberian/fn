#!/bin/sh
# e1.sh IMGCORE TAG LIMIT_MB DYN_MB [patch] : start the core directly at DYN under MemoryMax=LIMIT on a copy of the base store, POST+ARTICLE, stop by PID file
CORE=$1; tag=$2; L=$3; DYN=$4; P=${5:-/tank/fn/scratch/m20/e2.lisp}; LIM=$6
W=/dev/shm/m20/e2-$tag-$L; rm -rf $W; mkdir -p $W; cp -r --reflink=never --preserve=mode /dev/shm/m20/base/store $W/store
port=$((39700 + L % 97)); printf '[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s/c.sock"\n' $W $port $W > $W/fn.toml
case $CORE in *fn-core.core) TOP="--no-sysinit --load $P --eval (cl-user::xl-toplevel)";; *) TOP="--load $P --eval (acl2::sbcl-restart)";; esac
M20_LIMIT=$LIM SBCL_HOME=/tank/fn/sbcl/lib/sbcl/ timeout 200 systemd-run --user --scope --quiet -p MemoryMax=${L}M -p MemorySwapMax=0 /tank/fn/sbcl/bin/sbcl --tls-limit 20480 --dynamic-space-size ${DYN}MB --control-stack-size 1024KB --disable-ldb --core $CORE --noinform --end-runtime-options --no-userinit $TOP --disable-debugger --end-toplevel-options --fn operator $W/fn.toml run > $W/stdout 2> $W/stderr &
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
c=$(pgrep -P $(cat $W/pid) | head -1); grep -h "VmHWM\|VmRSS\|RssAnon\|RssFile" /proc/$c/status | tr -s " \t" " " | tr "\n" " "; echo
else echo "$tag $L no LISTENING after ${i}s"; fi
kill -0 $(cat $W/pid) 2>/dev/null && kill $(cat $W/pid); sleep 3
grep -h "capacity\|refused" $W/stdout $W/stderr | head -4
