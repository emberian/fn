#!/bin/sh
# Post-certification image build for one frozen tree on hbox.  Run ON hbox:
#   sh hbox-image-build.sh /tank/fn/gates/freeze-dev-<rev> <full-40-char-rev>
set -eu
ROOT=$1; REV=$2
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
# TLS is hbox's system libssl (OpenSSL 3.3.1); ML-DSA-65 is the vendored
# PQClean library tools/build_native_host.sh builds into build/lib (HST-016).
# No OpenSSL prefix is needed.
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
sh packaging/freeze-native-image.sh "$ROOT/build" "$IMG"
printf '%s\n' "$REV" > "$IMG/source-revision"   # `fn --version` (PKT-403)
find books host Makefile tools/build_native_host.sh -type f \( -name '*.lisp' -o -name Makefile -o -name '*.sh' \) | sort | xargs sha256sum > "$IMG/build-source.sha256"
run_logged build/freeze/image-validation.txt sh -c 'cd "$1" && sha256sum -c image.sha256' sh "$IMG"
run_logged build/freeze/image-hashes.txt sha256sum "$IMG"/*.core "$IMG"/runtime/sbcl "$IMG"/lib/libsodium.so.23 "$IMG"/lib/libfn-mldsa65.so "$ACL2"
ls -la "$IMG"
echo "== done"
