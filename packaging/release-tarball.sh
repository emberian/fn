#!/bin/sh
# Build the release a stranger downloads: one tarball per platform (D35).
#
#   packaging/release-tarball.sh PLATFORM REV OUT_DIR [SOURCE_ARCHIVE]
#   packaging/release-tarball.sh --frozen FROZEN_DIR PLATFORM REV OUT_DIR
#
# PLATFORM is linux-x86_64 or openbsd-amd64 and must be the system this runs
# on (the image is built here, and the installer executes it).  REV is the
# full 40-digit commit.  OUT_DIR (absolute) receives
#   fn-REV12-PLATFORM.tar.gz   one top directory fn/ (below)
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
#      swarm-build where it exists) and freezes it,
#   4. stages it (packaging/install-native.sh), checks that no Python is on
#      the deployed path (tools/runpath_check.py --tree) and that
#      `bin/fn --version' prints REV, and packs it.
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
#                                (libsodium, libfn-mldsa65; libzstd on
#                                OpenBSD).  TLS is the system's libssl.
#   fn/share/fn/                 fn.toml.example, systemd/fn.service.in or
#                                rc.d/fn.rc.in, docs/install.md,
#                                native-artifacts.txt, release-gate.txt,
#                                runpath-check.txt
set -eu
usage() {
  echo 'usage: release-tarball.sh PLATFORM REV OUT_DIR [SOURCE_ARCHIVE]' >&2
  echo '       release-tarball.sh --frozen FROZEN_DIR PLATFORM REV OUT_DIR' >&2
  exit 2
}
frozen=
if [ "${1:-}" = --frozen ]; then
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
tarball=$out/fn-$short-$platform.tar.gz
[ ! -e "$tarball" ] || { echo "release-tarball: exists: $tarball" >&2; exit 4; }
if [ "$system" = Linux ]; then sums=sha256sum; else sums=sha256; fi
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
  FN_NATIVE_PROFILE=production FN_NATIVE_BUILD=host/native/build.lisp \
    FN_NATIVE_IMAGE=build/fn-host FN_NATIVE_LOG="$work/native-build.log" \
    $wrap sh tools/build_native_host.sh
  FN_FREEZE_VARIANTS=fn-host sh packaging/freeze-native-image.sh "$work/src/build" "$work/frozen"
  frozen=$work/frozen
  stage=$work/stage
  {
    echo "source=$rev (git archive, $(wc -c < "$archive" | tr -d ' ') octets)"
    cat "$work/green-check.txt"
    echo "acquire: $(tail -1 "$work/acquire.txt")"
    echo "validate: $(tail -1 "$work/validate.txt")"
    echo "acl2: $FN_ACL2"
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
mkdir -p "$top/share/fn/docs"
install -m 0644 packaging/fn.toml.example "$top/share/fn/fn.toml.example"
install -m 0644 docs/install.md "$top/share/fn/docs/install.md"
install -m 0644 "$gate" "$top/share/fn/release-gate.txt"
version=$(env -i PATH=/usr/bin:/bin "$top/bin/fn" --version)
[ "$version" = "fn $rev" ] || {
  echo "release-tarball: bin/fn --version printed '$version', not 'fn $rev'" >&2; exit 4; }
"${PYTHON:-python3}" tools/runpath_check.py --tree "$top" > "$stage/runpath-check.txt" 2>&1 || {
  cat "$stage/runpath-check.txt" >&2; echo 'release-tarball: Python on the deployed path' >&2; exit 4; }
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
echo "version $version"
grep -F "fn-$short-$platform.tar.gz" "$out/SHA256SUMS"
