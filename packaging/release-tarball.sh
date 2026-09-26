#!/bin/sh
# Package one frozen native image as the release tarball a stranger downloads.
#
#   packaging/release-tarball.sh FROZEN_DIR REVISION OUT_DIR
#
# FROZEN_DIR is the output of packaging/freeze-native-image.sh (its production
# fn-host, fn-host.core, runtime/, openssl/lib and lib/libsodium.so.23 checked
# by image.sha256).  The tarball is the installed layout of
# packaging/install-native.sh under one top directory, fn-REV12/, plus the
# operator documentation and SHA256SUMS:
#
#   fn-REV12/bin/fn                      the one command (packaging/fn)
#   fn-REV12/libexec/fn/                 launcher, core, SBCL runtime,
#                                        OpenSSL 3.5 and libsodium
#   fn-REV12/share/fn/                   native-artifacts.txt, unit templates
#   fn-REV12/share/doc/fn/               operator.md, peering-with-a-friend.md,
#                                        agents.md, fn.toml.example
#   fn-REV12/SHA256SUMS                  every file above
#
# The frozen launcher finds its runtime and libraries beside itself, so the
# directory runs from wherever it is unpacked; nothing is read from the build
# box or from the system's OpenSSL.  The rendered unit files name the
# placeholder prefix /opt/fn-REV12: move the directory there, or render
# share/fn/systemd/fn.service.in yourself.  Run from the repository root.
set -eu
[ "$#" -eq 3 ] || { echo 'usage: release-tarball.sh FROZEN_DIR REVISION OUT_DIR' >&2; exit 2; }
frozen=$1 rev=$2 out=$3
case $rev in *[!0-9a-f]*|'') echo 'release-tarball: REVISION must be a lowercase hex commit' >&2; exit 2;; esac
[ "${#rev}" -eq 40 ] || { echo 'release-tarball: REVISION must be the full 40-digit commit' >&2; exit 2; }
case $out in /*) ;; *) echo 'release-tarball: OUT_DIR must be absolute' >&2; exit 2;; esac
short=$(printf '%s' "$rev" | cut -c1-12)
name=fn-$short
[ -x "$frozen/fn-host" ] && [ -s "$frozen/fn-host.core" ] || {
  echo "release-tarball: no frozen production image in $frozen" >&2; exit 4; }
mkdir -p "$out"
tarball=$out/$name-linux-x86_64.tar.gz
[ ! -e "$tarball" ] || { echo "release-tarball: exists: $tarball" >&2; exit 4; }
stage=$(mktemp -d "${TMPDIR:-/tmp}/fn-release.XXXXXX")
trap 'rm -rf "$stage"' EXIT HUP INT TERM
FN_NATIVE_HOST=$frozen/fn-host FN_NATIVE_CORE=$frozen/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=$rev DESTDIR=$stage PREFIX=/opt/$name \
  sh packaging/install-native.sh
top=$stage/opt/$name
install -m 0644 packaging/fn-native.service.in "$top/share/fn/systemd/fn.service.in"
mkdir -p "$top/share/doc/fn"
for doc in docs/operator.md docs/peering-with-a-friend.md docs/agents.md packaging/fn.toml.example; do
  [ -r "$doc" ] || { echo "release-tarball: missing document $doc" >&2; exit 4; }
  install -m 0644 "$doc" "$top/share/doc/fn/"
done
printf '%s\n' "$rev" > "$top/share/fn/source-revision"
(cd "$top" && find . -type f ! -name SHA256SUMS | LC_ALL=C sort | xargs sha256sum > SHA256SUMS)
tar -C "$stage/opt" --owner=0 --group=0 --numeric-owner --sort=name \
    -czf "$tarball" "$name"
(cd "$out" && sha256sum "$(basename "$tarball")" > "$(basename "$tarball").sha256")
echo "release $tarball"
cat "$tarball.sha256"
