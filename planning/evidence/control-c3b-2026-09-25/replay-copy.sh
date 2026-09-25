#!/bin/bash
# Replay a read-only COPY of the deployed node's store on the control-c3 image (C3 binding).
set -u
D=/tank/fn/scratch/control-c3b
IMG=/tank/fn/scratch/control-c3/gate-52b7b816/build/fn-host-developer
cd $D; export LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
rm -rf replay && mkdir replay && cp -a store-copy replay/store
printf '[store]\npath = "%s/replay/store"\n[listener]\nhost = "127.0.0.1"\nport = 11397\n[control]\npath = "%s/replay/control.sock"\n[log]\npath = "%s/replay/fn.log"\n' $D $D $D > replay/fn.toml
sha256sum $IMG ${IMG}.core
timeout 90 systemd-run --user --scope -p MemoryMax=24G $IMG --fn operator $D/replay/fn.toml run > replay/run.out 2>&1 &
PID=$!
python3 - <<'PY'
import socket,time
for i in range(60):
    try:
        s=socket.create_connection(("127.0.0.1",11397),timeout=5); break
    except OSError: time.sleep(1)
else:
    print("NO LISTENER"); raise SystemExit(1)
f=s.makefile("rb")
print(f.readline().decode().strip())
for cmd in ["GROUP fn.agents","GROUP fn.announce","LISTGROUP fn.agents","QUIT"]:
    s.sendall((cmd+"\r\n").encode())
    line=f.readline().decode().strip(); print(cmd,"->",line)
    if cmd.startswith("LISTGROUP") and line.startswith("211"):
        while True:
            l=f.readline().decode().strip()
            if l==".": break
            print("  ",l)
PY
kill $PID 2>/dev/null; sleep 2
echo "--- run.out"; tail -20 replay/run.out; echo "--- fn.log"; tail -20 replay/fn.log 2>/dev/null
