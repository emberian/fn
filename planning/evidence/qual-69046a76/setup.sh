#!/bin/sh
# qual-69046a76 setup: scratch trees (copies of the frozen gate), bin/, image check, build-log scan, gate-vs-archive.
set -u
. /tank/fn/scratch/qual-69046a76/env.sh
mkdir -p $S/bin $S/logs $S/diag
ln -sfn $I/runtime/sbcl $S/bin/sbcl
cp /tank/fn/scratch/qual-b6759850/bin/test-openssl $S/bin/test-openssl
cp /tank/fn/scratch/qual-bbf52159/poll-source-dated.eml $S/poll-source-dated.eml 2>/dev/null
for t in tree ctree; do rsync -a --exclude /build/images --exclude /build/farm --exclude /build/freeze $G/ $S/$t/; done
( cd $I && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
cp $I/image.sha256 $S/image-full.sha256
P='ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified'
{ for f in $G/build/image-build.log $G/build/freeze/*; do [ -f "$f" ] && echo "$f sha256=$(sha256sum $f | cut -d' ' -f1) errors=$(grep -c -E "$P" $f)"; done
  grep -n -E "$P" $G/build/image-build.log $G/build/freeze/* 2>/dev/null | head -20; } > $S/build-log-scan.txt 2>&1
python3 -c 'import dilithium_py, cryptography; print("dilithium_py", dilithium_py.__file__, "cryptography", cryptography.__version__)' > $S/pylib.txt 2>&1
echo SETUP-DONE
