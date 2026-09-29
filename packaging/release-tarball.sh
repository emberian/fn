#!/bin/sh
# Build the release a stranger downloads: one tarball per platform (D35).
#
#   packaging/release-tarball.sh [--runtime-from DIR] PLATFORM REV OUT_DIR [SOURCE_ARCHIVE]
#   packaging/release-tarball.sh --frozen FROZEN_DIR PLATFORM REV OUT_DIR
#
# PLATFORM is linux-x86_64 or openbsd-amd64 and must be the system this runs
# on (the image is built here, and the installer executes it).  REV is the
# full 40-digit commit.  OUT_DIR (absolute) receives
#   fn-VERSION-PLATFORM.tar.gz one top directory fn/ (below); VERSION is the
#                              release version (D37's sequence: 6.6.0 first),
#                              read from the file
#                              VERSION at the root of REV's tree (the one
#                              place it is written; the image build reads
#                              the same file, host/native/io.lisp
#                              fnn-select-release-version).  The --frozen
#                              form names its tarball
#                              fn-VERSION+REV12-PLATFORM.tar.gz (VERSION from
#                              the current tree): it is not the release.
#   SHA256SUMS                 the tarballs in OUT_DIR (sha256sum lines on
#                              Linux, sha256's BSD lines on OpenBSD)
# and the work directory build-REV12-PLATFORM/ with every step's log.
#
# The first form builds from a `git archive' of REV, never a worktree:
# SOURCE_ARCHIVE is that archive (its pax header must name REV), or, without
# it, this runs `git archive REV' in the current checkout.  In the unpacked
# source it then
#   1. refuses unless every book in the default image profile's include
#      closure is green at its current digest (tools/green_check.py
#      --profile default --strict; the line goes into the release),
#   2. acquires and load-checks that closure's certificates from the cache
#      (tools/proof_artifacts.py acquire/validate --profile default;
#      FN_CERT_CACHE and FN_ACL2 name the cache and ACL2; nothing is
#      certified here),
#   3. builds the PRODUCTION image (tools/build_native_host.sh, under
#      swarm-build where it exists; FN_IMAGE_ACL2, when set, is the ACL2
#      launcher the image load runs under, e.g. the toolchain's at
#      --tls-limit 65536) and freezes it,
#   4. stages it (packaging/install-native.sh), checks that no Python is on
#      the deployed path (tools/runpath_check.py --tree) and that
#      `bin/fn --version' prints `fn VERSION (REV12)', and packs it.
# --runtime-from DIR bundles DIR/sbcl as the SBCL runtime (the freeze's
# FN_FREEZE_RUNTIME): on Linux, DIR is packaging/floor-runtime.sh's output,
# the build's SBCL rebuilt in Debian 12 so the release runs on glibc 2.36
# (tools/runpath_check.py GLIBC_FLOOR; step 4 refuses a bundled object above
# it, so a Linux release built on a newer glibc needs this).
# The second form packages an already frozen production image (tests,
# tests/friends_tarball.sh); its share/fn/release-gate.txt says it was not
# gated, and it is not a release.
#
# The tarball's layout (HST-017):
#   fn/SHA256SUMS                every file below
#   fn/install.sh                the installer (packaging/install.sh)
#   fn/bin/fn                    the one command (packaging/fn)
#   fn/libexec/fn/               the frozen launcher, the production core,
#                                source-revision, runtime/ (SBCL) and lib/
#                                (libsodium, libfn-mldsa65, libfn-blake3, libfn-deflate; libzstd on
#                                OpenBSD).  TLS is the system's libssl.
#   fn/share/fn/                 fn.toml.example, systemd/fn.service.in or
#                                rc.d/fn.rc.in, caddy/fn-web.caddy (HTTPS
#                                in front of the node's own web face,
#                                install.sh --reader), docs/install.md, web.md,
#                                agents.md, the guides' articles
#                                (docs/articles/*.txt), native-artifacts.txt,
#                                release-gate.txt, runpath-check.txt
#   fn/clients/                  fn's client programs, separate from the node
#                                (packaging/install-clients.sh): fn-client,
#                                fn-agent, fn-consumer, fn-verify.  No
#                                service: the web page is the node's own
#                                face.  They need Python 3.9+
#                                (clients/README.txt); the node never runs
#                                them, and the runpath check holds the rest
#                                of the tree to that (its clients rule).
#
# Building the OpenBSD release (openbsd-amd64).  It is built on OpenBSD 7.9
# amd64 itself, with SBCL (pkg_add sbcl), libsodium, zstd and python3, and an
# ACL2 8.7 built there with its system books certified.  Three requirements
# no error message states plainly (each cost a failed build, 2026-09-27):
#   a. FN_ACL2 must be a LITERAL launcher: a sh script that execs sbcl with
#      every runtime option written out (--tls-limit, --dynamic-space-size,
#      --control-stack-size, --core PATH/saved_acl2.core ...), not ACL2's
#      generated saved_acl2, which expands ${SBCL_USER_ARGS}.  Certificates
#      made under the generated one carry no qualified launcher/core/runtime
#      fingerprint: nothing publishes to FN_CERT_CACHE and step 2 acquires
#      nothing (`no qualified ACL2 launcher/core/runtime fingerprint').
#   b. FN_IMAGE_ACL2 must name the same launcher at --tls-limit 65536 (a
#      copy of (a) with only that number changed): the production world
#      passes SBCL's default 16384 (`Thread local storage exhausted' in
#      native-build.log).
#   c. Where step 4 stages and runs bin/fn must be on a file system mounted
#      wxallowed (`mount -o wxallowed,nodev DEV DIR', or under /usr/local):
#      OUT_DIR for the first form, TMPDIR (default /tmp, never wxallowed)
#      for --frozen.  Otherwise install-native's probe dies with `RWX mmap
#      not supported' (under --frozen, then `GC invariant lost'), and step 4
#      may report only `image did not identify itself as the production
#      profile'.
# The order: certify the default closure with (a) into FN_CERT_CACHE, from a
# git archive of REV unpacked on its own (python3 tools/certify_books.py
# --jobs N --closure $(python3 tools/proof_artifacts.py roots --profile
# default), FN_ACL2, ACL2_SYSTEM_BOOKS and FN_CERT_CACHE set); move that
# certifying tree aside (rename it), since a live origin is not acquired for
# another tree (tools/certs.py usable_origin); then run this script with
# FN_ACL2=(a), FN_IMAGE_ACL2=(b), FN_CERT_CACHE,
# FN_FREEZE_SODIUM=/usr/local/lib/libsodium.so.11.1 (the 7.9 package) and
# FN_FREEZE_DYNAMIC_SPACE_MB=1024 (the launchers' default heap; the node
# replaces it with the figure from the store's profile).  Raise the data
# size limit first (`ulimit -d unlimited', or the login class's hard
# limit): root's class caps it at 4 GiB and the literal launchers ask for
# 4096 MB.  Step 1 still needs REV's committed manifests to cover the
# closure (tools/green_check.py); the guest's own certification does not
# replace them.
set -eu
usage() {
  echo 'usage: release-tarball.sh [--runtime-from DIR] PLATFORM REV OUT_DIR [SOURCE_ARCHIVE]' >&2
  echo '       release-tarball.sh --frozen FROZEN_DIR PLATFORM REV OUT_DIR' >&2
  exit 2
}
frozen='' runtime_from=''
if [ "${1:-}" = --runtime-from ]; then
  [ "$#" -ge 2 ] || usage
  runtime_from=$2; shift 2
  case $runtime_from in /*) ;; *) echo 'release-tarball: --runtime-from DIR must be absolute' >&2; exit 2;; esac
  [ -x "$runtime_from/sbcl" ] || { echo "release-tarball: no runtime $runtime_from/sbcl" >&2; exit 4; }
  [ "$#" -eq 3 ] || [ "$#" -eq 4 ] || usage
elif [ "${1:-}" = --frozen ]; then
  [ "$#" -eq 5 ] || usage
  frozen=$2; shift 2
  [ "$#" -eq 3 ] || usage
else
  [ "$#" -eq 3 ] || [ "$#" -eq 4 ] || usage
fi
platform=$1 rev=$2 out=$3 archive=${4:-}
case $platform in
  linux-x86_64) system=Linux base=/opt ;;
  openbsd-amd64) system=OpenBSD base=/usr/local ;;
  *) echo "release-tarball: unknown platform $platform (linux-x86_64, openbsd-amd64)" >&2; exit 2 ;;
esac
[ "$(uname -s)" = "$system" ] || { echo "release-tarball: $platform is built on $system" >&2; exit 2; }
case $rev in *[!0-9a-f]*|'') echo 'release-tarball: REV must be a lowercase hex commit' >&2; exit 2;; esac
[ "${#rev}" -eq 40 ] || { echo 'release-tarball: REV must be the full 40-digit commit' >&2; exit 2; }
case $out in /*) ;; *) echo 'release-tarball: OUT_DIR must be absolute' >&2; exit 2;; esac
short=$(printf '%s' "$rev" | cut -c1-12)
# The release version: an entry of the release sequence (D37,
# planning/release-sequence.json; tools/release_sequence.py decides it, any
# number of dotted components, never compared as numbers).
release_version() {
  [ -r "$1" ] || { echo "release-tarball: no $1" >&2; exit 4; }
  v=$(sed -n 1p "$1")
  "${PYTHON:-python3}" tools/release_sequence.py position "$v" >/dev/null || {
    echo "release-tarball: $1 holds '$v', not an entry of the release sequence" >&2; exit 4; }
  printf '%s\n' "$v"
}
if [ "$system" = Linux ]; then sums=sha256sum; else sums=sha256; fi
if [ -n "$frozen" ]; then
  version=$(release_version VERSION)
  tarball=$out/fn-$version+$short-$platform.tar.gz
  [ ! -e "$tarball" ] || { echo "release-tarball: exists: $tarball" >&2; exit 4; }
fi
mkdir -p "$out"

if [ -z "$frozen" ]; then
  work=$out/build-$short-$platform
  [ ! -e "$work" ] || { echo "release-tarball: exists: $work" >&2; exit 4; }
  : "${FN_CERT_CACHE:?set FN_CERT_CACHE to the certificate cache}"
  : "${FN_ACL2:?set FN_ACL2 to the ACL2 executable the cache was certified with}"
  mkdir -p "$work/src"
  if [ -z "$archive" ]; then
    archive=$work/source.tar
    git archive --format=tar "$rev" > "$archive"
  fi
  # git archive's first header is a pax global header whose record
  # `52 comment=REV' names the commit (git get-tar-commit-id reads the same).
  named=$(dd if="$archive" bs=512 skip=1 count=1 2>/dev/null | tr '\0' '\n' | sed -n 's/^52 comment=//p')
  [ "$named" = "$rev" ] || {
    echo "release-tarball: $archive is not a git archive of $rev (it names ${named:-no commit})" >&2; exit 4; }
  tar -xf "$archive" -C "$work/src"
  cd "$work/src"
  version=$(release_version VERSION)
  tarball=$out/fn-$version-$platform.tar.gz
  [ ! -e "$tarball" ] || { echo "release-tarball: exists: $tarball" >&2; exit 4; }
  python=${PYTHON:-python3}
  echo "== 1. release gate: the default profile's closure green at REV's digests"
  "$python" tools/green_check.py --profile default --strict > "$work/green-check.txt" 2>&1 || {
    cat "$work/green-check.txt" >&2; echo 'release-tarball: the closure is not green at REV' >&2; exit 4; }
  cat "$work/green-check.txt"
  echo "== 2. certificates from the cache: acquire and validate"
  "$python" tools/proof_artifacts.py acquire --profile default --root "$work/src" \
    --cache "$FN_CERT_CACHE" --acl2 "$FN_ACL2" > "$work/acquire.txt" 2>&1 || {
      tail -20 "$work/acquire.txt" >&2; echo 'release-tarball: acquire failed' >&2; exit 4; }
  tail -1 "$work/acquire.txt"
  "$python" tools/proof_artifacts.py validate --profile default --acl2 "$FN_ACL2" \
    > "$work/validate.txt" 2>&1 || {
      tail -20 "$work/validate.txt" >&2; echo 'release-tarball: validate failed' >&2; exit 4; }
  tail -1 "$work/validate.txt"
  echo "== 3. the production image"
  wrap=
  command -v swarm-build >/dev/null 2>&1 && wrap=swarm-build
  # The image load runs under FN_IMAGE_ACL2 when set: the same ACL2 at a
  # larger --tls-limit (the production world passed SBCL's 16384 on
  # 2026-09-27, "Thread local storage exhausted"; tools/hbox_native.sh's
  # --image-acl2).  Certificates stay keyed on FN_ACL2's toolchain.
  image_acl2=${FN_IMAGE_ACL2:-$FN_ACL2}
  FN_ACL2=$image_acl2 FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp \
    FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG="$work/native-build.log" \
    $wrap sh tools/build_native_host.sh
  FN_FREEZE_VARIANTS=fn-host FN_FREEZE_RUNTIME=${runtime_from:+$runtime_from/sbcl} \
    sh packaging/freeze-native-image.sh "$work/src/build" "$work/frozen"
  frozen=$work/frozen
  stage=$work/stage
  {
    echo "version=$version"
    echo "source=$rev (git archive, $(wc -c < "$archive" | tr -d ' ') octets)"
    cat "$work/green-check.txt"
    echo "acquire: $(tail -1 "$work/acquire.txt")"
    echo "validate: $(tail -1 "$work/validate.txt")"
    echo "acl2: $FN_ACL2"
    [ "$image_acl2" = "$FN_ACL2" ] || echo "image-acl2: $image_acl2"
    [ -z "$runtime_from" ] || echo "runtime-from: $($sums "$runtime_from/sbcl")"
  } > "$work/release-gate.txt"
  gate=$work/release-gate.txt
else
  [ -x "$frozen/fn-host" ] && [ -s "$frozen/fn-host.core" ] || {
    echo "release-tarball: no frozen production image in $frozen" >&2; exit 4; }
  stage=$(mktemp -d "${TMPDIR:-/tmp}/fn-release.XXXXXX")
  trap 'rm -rf "$stage"' EXIT HUP INT TERM
  gate=$stage/release-gate.txt
  echo "ungated: packaged with --frozen from $frozen; not a release" > "$gate"
fi

echo "== 4. stage, check, pack"
[ ! -e "$stage$base/fn" ] || { echo "release-tarball: exists: $stage$base/fn" >&2; exit 4; }
FN_NATIVE_HOST=$frozen/fn-host FN_NATIVE_CORE=$frozen/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=$rev DESTDIR=$stage PREFIX=$base/fn \
  sh packaging/install-native.sh
top=$stage$base/fn
sh packaging/install-clients.sh "$top"
mkdir -p "$top/share/fn/docs"
install -m 0644 packaging/fn.toml.example "$top/share/fn/fn.toml.example"
install -m 0644 docs/install.md "$top/share/fn/docs/install.md"
install -m 0644 docs/articles/*.txt "$top/share/fn/docs/"
install -m 0644 "$gate" "$top/share/fn/release-gate.txt"
printed=$(env -i PATH=/usr/bin:/bin "$top/bin/fn" --version)
[ "$printed" = "fn $version ($short)" ] || {
  echo "release-tarball: bin/fn --version printed '$printed', not 'fn $version ($short)'" >&2; exit 4; }
"${PYTHON:-python3}" tools/runpath_check.py --tree "$top" --platform "${platform%%-*}" > "$stage/runpath-check.txt" 2>&1 || {
  cat "$stage/runpath-check.txt" >&2
  echo 'release-tarball: the runpath check failed (Python on the deployed path, a client the node could run, or a bundled object above the glibc floor: --runtime-from)' >&2; exit 4; }
install -m 0644 "$stage/runpath-check.txt" "$top/share/fn/runpath-check.txt"
tail -1 "$stage/runpath-check.txt"
(cd "$top" && find . -type f ! -name SHA256SUMS | LC_ALL=C sort | xargs $sums > SHA256SUMS)
if [ "$system" = Linux ]; then
  tar -C "$stage$base" --owner=0 --group=0 --numeric-owner --sort=name -czf "$tarball" fn
else
  # pax(1) in ustar format from a sorted list; -d keeps it from descending.
  (cd "$stage$base" && find fn | LC_ALL=C sort | pax -w -d -x ustar | gzip -n -9 > "$tarball")
fi
(cd "$out" && ls fn-*.tar.gz | LC_ALL=C sort | xargs $sums > SHA256SUMS)
echo "release $tarball"
echo "version $printed"
grep -F "$(basename -- "$tarball")" "$out/SHA256SUMS"
