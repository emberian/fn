#!/bin/bash
IMG=$1; D=$2
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib ACL2_CUSTOMIZATION=NONE
rm -rf $D; mkdir -p $D; cd $D
PORT=$(python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1])')
printf '[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s/control.sock"\n' $D $PORT $D > fn.toml
"$IMG" --fn store $D/store init fn.letters >/dev/null 2>&1
FN_NATIVE_CONTROL_FAULT=postpublish nohup "$IMG" --fn operator $D/fn.toml run > run.log 2>&1 < /dev/null & P=$!
for i in $(seq 60); do grep -q LISTENING run.log 2>/dev/null && break; sleep 0.5; done
printf 'From: a@example.invalid\r\nNewsgroups: fn.letters\r\nSubject: u\r\nMessage-ID: <unc@example.invalid>\r\n\r\nbody\r\n' > p.article
"$IMG" --fn operator $D/fn.toml post --message-id '<unc@example.invalid>' --payload p.article --group fn.letters; echo "post rc=$?"
sleep 2; kill -0 $P 2>/dev/null && { echo UP; kill $P; } || echo DOWN
cat run.log; sha256sum run.log
