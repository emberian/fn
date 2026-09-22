#!/bin/sh
# Post-certification image build for one frozen tree on hbox.  Run ON hbox:
#   sh hbox-image-build.sh /tank/fn/gates/freeze-dev-<rev> <full-40-char-rev>
set -eu
ROOT=$1; REV=$2
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
cd "$ROOT"
mkdir -p build/freeze
echo "== acquire default"
python3 tools/proof_artifacts.py acquire --profile default --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" | tee build/freeze/acquire-default.txt
echo "== acquire dtn"
python3 tools/proof_artifacts.py acquire --profile dtn --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" | tee build/freeze/acquire-dtn.txt
echo "== validate default"
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" | tee build/freeze/validate-default.txt
echo "== validate dtn"
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile dtn --acl2 "$ACL2" | tee build/freeze/validate-dtn.txt
echo "== build production"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=build/freeze/native-build-production.log swarm-build sh tools/build_native_host.sh
echo "== build developer"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh
echo "== build dtn"
FN_ACL2=$ACL2 FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn FN_NATIVE_LOG=build/freeze/native-build-dtn.log swarm-build sh tools/build_native_host.sh
echo "== freeze"
IMG=build/images/$REV; mkdir -p "$IMG"
cp -p build/fn-host build/fn-host.core build/fn-host-developer build/fn-host-developer.core build/fn-host-dtn build/fn-host-dtn.core "$IMG/"
find books host Makefile tools/build_native_host.sh -type f \( -name '*.lisp' -o -name Makefile -o -name '*.sh' \) | sort | xargs sha256sum > "$IMG/build-source.sha256"
sha256sum "$IMG"/* /tank/fn/sbcl/bin/sbcl "$ACL2" /tank/fn/acl2-8.7/saved_acl2.core | tee build/freeze/image-hashes.txt
ls -la "$IMG"
echo "== done"
