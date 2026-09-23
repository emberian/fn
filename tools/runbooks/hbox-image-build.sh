#!/bin/sh
# Post-certification image build for one frozen tree on hbox.  Run ON hbox:
#   sh hbox-image-build.sh /tank/fn/gates/freeze-dev-<rev> <full-40-char-rev>
set -eu
ROOT=$1; REV=$2
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
# The images refuse to build without an OpenSSL pair that provides ML-DSA-65
# (host/native/signatures.lisp, OpenSSL >= 3.5); hbox's system library is
# 3.3.1.  This is the matched pair built from the openssl-3.5.8 release
# tarball (SHA-256 a8f84a39918ec6415ce765d9b429d313ba97b8143169c172e734b9514464f5b2);
# a running image needs the same variable.
FN_OPENSSL_PREFIX=${FN_OPENSSL_PREFIX:-/tank/fn/toolchains/openssl-3.5.8}
export FN_OPENSSL_PREFIX
cd "$ROOT"
mkdir -p build/freeze
# POSIX sh has no pipefail: piping a failed acquisition/validation through tee
# would allow the build to continue. Preserve the command's failure status.
run_logged() {
    log_path=$1
    shift
    if "$@" >"$log_path" 2>&1; then
        cat "$log_path"
    else
        command_status=$?
        cat "$log_path" >&2
        return "$command_status"
    fi
}
echo "== acquire default"
run_logged build/freeze/acquire-default.txt python3 tools/proof_artifacts.py acquire --profile default --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2"
echo "== acquire dtn"
run_logged build/freeze/acquire-dtn.txt python3 tools/proof_artifacts.py acquire --profile dtn --root "$ROOT" --cache "$CACHE" --acl2 "$ACL2"
echo "== validate default"
FN_ACL2=$ACL2 run_logged build/freeze/validate-default.txt python3 tools/proof_artifacts.py validate --profile default --acl2 "$ACL2"
echo "== validate dtn"
FN_ACL2=$ACL2 run_logged build/freeze/validate-dtn.txt python3 tools/proof_artifacts.py validate --profile dtn --acl2 "$ACL2"
echo "== build production"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG=build/freeze/native-build-production.log swarm-build sh tools/build_native_host.sh
echo "== build developer"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host-developer FN_NATIVE_LOG=build/freeze/native-build-developer.log swarm-build sh tools/build_native_host.sh
echo "== build dtn"
FN_ACL2=$ACL2 FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn FN_NATIVE_LOG=build/freeze/native-build-dtn.log swarm-build sh tools/build_native_host.sh
echo "== build dtn developer"
FN_ACL2=$ACL2 FN_NATIVE_PROFILE=developer FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn-developer FN_NATIVE_LOG=build/freeze/native-build-dtn-developer.log swarm-build sh tools/build_native_host.sh
echo "== freeze"
IMG="$ROOT/build/images/$REV"
sh packaging/freeze-native-image.sh "$ROOT/build" "$IMG" "$FN_OPENSSL_PREFIX"
find books host Makefile tools/build_native_host.sh -type f \( -name '*.lisp' -o -name Makefile -o -name '*.sh' \) | sort | xargs sha256sum > "$IMG/build-source.sha256"
run_logged build/freeze/image-validation.txt sh -c 'cd "$1" && sha256sum -c image.sha256' sh "$IMG"
sha256sum "$IMG"/*.core "$IMG"/runtime/sbcl "$IMG"/openssl/lib/*.so.3 "$IMG"/lib/libsodium.so.23 "$ACL2" | tee build/freeze/image-hashes.txt
ls -la "$IMG"
echo "== done"
