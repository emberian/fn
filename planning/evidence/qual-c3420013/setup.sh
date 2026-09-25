#!/bin/sh
# qual-c3420013 setup: scratch trees (copies of the frozen gate), bin/, image check.
set -u
S=/tank/fn/scratch/qual-c3420013
G=/tank/fn/gates/qual-c3420013-20260925
I=$G/build/images/c3420013
mkdir -p $S/bin $S/logs $S/diag
ln -sfn $I/runtime/sbcl $S/bin/sbcl
cp /tank/fn/scratch/qual-4eca4148/bin/test-openssl $S/bin/test-openssl
cp /tank/fn/scratch/qual-4eca4148/poll-source-dated.eml $S/poll-source-dated.eml
for t in tree ctree; do rsync -a --exclude /build/images --exclude /build/farm --exclude /build/freeze $G/ $S/$t/; done
( cd $I && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
cp $I/image.sha256 $S/image-full.sha256
python3 -c 'import dilithium_py, cryptography; print("dilithium_py", dilithium_py.__file__, "cryptography", cryptography.__version__)' > $S/pylib.txt 2>&1
echo SETUP-DONE
