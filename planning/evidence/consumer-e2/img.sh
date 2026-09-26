#!/bin/sh
# consumer-e2 image build: production + developer from one frozen tree (after tools/runbooks/hbox-image-build.sh).
set -eu
ROOT=/tank/fn/gates/consumer-e2-img2; REV=d68f78c4b99f2c1d40a6eb13e28a2152d99771d8
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g; CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
cd "$ROOT"; mkdir -p build/freeze
python3 tools/proof_artifacts.py acquire --profile default --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2" > build/freeze/acquire-default.txt 2>&1
FN_ACL2=$ACL2 python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2" > build/freeze/validate-default.txt 2>&1
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=build/freeze/native-build-production.log swarm-build sh tools/build_native_host.sh
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh
IMG="$ROOT/build/images/$REV"
FN_FREEZE_VARIANTS="fn-host fn-host-developer" sh packaging/freeze-native-image.sh "$ROOT/build" "$IMG" "$FN_OPENSSL_PREFIX"
find books host Makefile tools/build_native_host.sh -type f \( -name '*.lisp' -o -name Makefile -o -name '*.sh' \) | sort | xargs sha256sum > "$IMG/build-source.sha256"
(cd "$IMG" && sha256sum -c image.sha256) > build/freeze/image-validation.txt
sha256sum "$IMG"/*.core "$IMG"/runtime/sbcl > build/freeze/image-hashes.txt
echo done > build/freeze/DONE
