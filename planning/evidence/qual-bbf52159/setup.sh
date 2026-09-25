#!/bin/sh
# qual-bbf52159 setup: scratch trees (copies of the frozen gate), bin/, image check.
set -u
S=/tank/fn/scratch/qual-bbf52159
G=/tank/fn/gates/qual-bbf52159-20260925
I=$G/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d
mkdir -p $S/bin $S/logs $S/diag
ln -sfn $I/runtime/sbcl $S/bin/sbcl
cp /tank/fn/scratch/qual-c3420013/bin/test-openssl $S/bin/test-openssl
cp /tank/fn/scratch/qual-c3420013/poll-source-dated.eml $S/poll-source-dated.eml
for t in tree ctree; do rsync -a --exclude /build/images --exclude /build/farm --exclude /build/freeze $G/ $S/$t/; done
( cd $I && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
cp $I/image.sha256 $S/image-full.sha256
python3 -c 'import dilithium_py, cryptography; print("dilithium_py", dilithium_py.__file__, "cryptography", cryptography.__version__)' > $S/pylib.txt 2>&1
echo SETUP-DONE
