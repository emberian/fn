#!/bin/bash
# usage: repro.sh <image> <dir>
set -u
IMG=$1; D=$2
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib ACL2_CUSTOMIZATION=NONE
unset ACL2_SYSTEM_BOOKS
H=/tank/fn/scratch/transit-436
rm -rf $D; mkdir -p $D; cd $D
PORT=$(python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1])')
cat > fn.toml <<T
[store]
path = "$D/store"
[listener]
host = "127.0.0.1"
port = $PORT
[control]
path = "$D/control.sock"
T
fnh() { "$IMG" --fn "$@"; }
fnh store $D/store init fn.letters > init.log 2>&1; echo "init rc=$?"
fnh operator $D/fn.toml peer add a a.gate.example.invalid 127.0.0.1 11190 'fn.*' - 127.0.0.1 true > peer.log 2>&1; echo "peer rc=$? $(cat peer.log)"
fnh operator $D/fn.toml policy set path-identity b.gate.example.invalid > pol.log 2>&1; echo "policy rc=$? $(cat pol.log)"
start() { nohup "$IMG" --fn operator $D/fn.toml run > $1 2>&1 < /dev/null & echo $! > pid; for i in $(seq 60); do python3 -c "import socket;socket.create_connection(('127.0.0.1',$PORT),1)" 2>/dev/null && break; sleep 0.5; done; }
start run1.log
sed "s/<delta@/<eps@/" $H/delta.article > eps.article
python3 $H/ihave.py eps.article '<eps@a.example.invalid>' $PORT
sleep 2
if kill -0 $(cat pid) 2>/dev/null; then echo "service UP"; kill $(cat pid); wait $(cat pid) 2>/dev/null; else echo "service DOWN"; fi
echo "--- run1.log"; cat run1.log; sha256sum run1.log
fnh operator $D/fn.toml status 2>&1 | tail -2
