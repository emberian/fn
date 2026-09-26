#!/bin/sh
# qual-b6759850 setup: scratch trees (copies of the frozen gate), bin/, image check, build-log scan.
set -u
. /tank/fn/scratch/qual-b6759850/env.sh
mkdir -p $S/bin $S/logs $S/diag
ln -sfn $I/runtime/sbcl $S/bin/sbcl
cp /tank/fn/scratch/qual-bbf52159/bin/test-openssl $S/bin/test-openssl
cp /tank/fn/scratch/qual-bbf52159/poll-source-dated.eml $S/poll-source-dated.eml
for t in tree ctree; do rsync -a --exclude /build/images --exclude /build/farm --exclude /build/freeze $G/ $S/$t/; done
( cd $I && sha256sum -c image.sha256 ) > $S/image-check.log 2>&1; echo "rc=$?" >> $S/image-check.log
cp $I/image.sha256 $S/image-full.sha256
{ echo "# build log $G/build/image-build.log sha256 $(sha256sum $G/build/image-build.log | cut -d' ' -f1)";
  echo "# ACL2 error lines (PKT-284 patterns):";
  grep -n -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' $G/build/image-build.log | head -40;
  echo "# count $(grep -c -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' $G/build/image-build.log)";
  echo "# freeze logs:"; ls -la $G/build/freeze/ 2>&1;
  for f in $G/build/freeze/*.log $G/build/freeze/*.txt; do [ -f "$f" ] && echo "$f $(grep -c -E 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp|Uncertified' $f)"; done; } > $S/build-log-scan.txt 2>&1
# the gate tree vs git archive b6759850 (host tests tools books packaging Makefile)
python3 -c 'import dilithium_py, cryptography; print("dilithium_py", dilithium_py.__file__, "cryptography", cryptography.__version__)' > $S/pylib.txt 2>&1
echo SETUP-DONE
