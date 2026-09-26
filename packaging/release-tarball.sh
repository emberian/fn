#!/bin/sh
# Package one frozen native image as the release tarball a stranger downloads.
#
#   packaging/release-tarball.sh [PLATFORM] FROZEN_DIR REVISION OUT_DIR
#
# PLATFORM is linux-x86_64 (the default) or openbsd-amd64, and must be the
# system this runs on: the installer executes the image to check its profile.
# FROZEN_DIR is the output of packaging/freeze-native-image.sh (its production
# fn-host, fn-host.core, runtime/ and lib/, plus openssl/lib on Linux, checked
# by image.sha256).  The tarball is the installed layout of
# packaging/install-native.sh under one top directory, fn-REV12/, plus the
# operator documentation and SHA256SUMS:
#
#   fn-REV12/bin/fn                      the one command (packaging/fn)
#   fn-REV12/libexec/fn/                 launcher, core, SBCL runtime and the
#                                        libraries it loads: libsodium, and on
#                                        Linux OpenSSL 3.5, on OpenBSD libzstd
#                                        (TLS is the system LibreSSL)
#   fn-REV12/share/fn/                   native-artifacts.txt, the service file:
#                                        systemd/ and launchd/ (Linux), rc.d/fn
#                                        (OpenBSD)
#   fn-REV12/share/doc/fn/               operator.md, peering-with-a-friend.md,
#                                        agents.md, fn.toml.example
#   fn-REV12/SHA256SUMS                  every file above (OpenBSD: sha256's
#                                        BSD format, `sha256 -c SHA256SUMS')
#
# The frozen launcher finds its runtime and libraries beside itself, so the
# directory runs from wherever it is unpacked -- on OpenBSD, wherever the
# mount allows W^X mappings (SBCL is linked wxneeded; /usr/local is mounted
# wxallowed by default).  The rendered service files name the placeholder
# prefix: /opt/fn-REV12 on Linux, /usr/local/fn-REV12 on OpenBSD.  Before
# packing, tools/runpath_check.py --tree checks that no Python is on the
# deployed path.  Run from the repository root.
set -eu
platform=linux-x86_64
if [ "$#" -eq 4 ]; then platform=$1; shift; fi
[ "$#" -eq 3 ] || { echo 'usage: release-tarball.sh [linux-x86_64|openbsd-amd64] FROZEN_DIR REVISION OUT_DIR' >&2; exit 2; }
frozen=$1 rev=$2 out=$3
case $platform in
  linux-x86_64) system=Linux base=/opt ;;
  openbsd-amd64) system=OpenBSD base=/usr/local ;;
  *) echo "release-tarball: unknown platform $platform" >&2; exit 2 ;;
esac
[ "$(uname -s)" = "$system" ] || { echo "release-tarball: $platform is packaged on $system" >&2; exit 2; }
case $rev in *[!0-9a-f]*|'') echo 'release-tarball: REVISION must be a lowercase hex commit' >&2; exit 2;; esac
[ "${#rev}" -eq 40 ] || { echo 'release-tarball: REVISION must be the full 40-digit commit' >&2; exit 2; }
case $out in /*) ;; *) echo 'release-tarball: OUT_DIR must be absolute' >&2; exit 2;; esac
short=$(printf '%s' "$rev" | cut -c1-12)
name=fn-$short
[ -x "$frozen/fn-host" ] && [ -s "$frozen/fn-host.core" ] || {
  echo "release-tarball: no frozen production image in $frozen" >&2; exit 4; }
mkdir -p "$out"
tarball=$out/$name-$platform.tar.gz
[ ! -e "$tarball" ] || { echo "release-tarball: exists: $tarball" >&2; exit 4; }
stage=$(mktemp -d "${TMPDIR:-/tmp}/fn-release.XXXXXX")
trap 'rm -rf "$stage"' EXIT HUP INT TERM
FN_NATIVE_HOST=$frozen/fn-host FN_NATIVE_CORE=$frozen/fn-host.core \
  FN_NATIVE_SOURCE_REVISION=$rev DESTDIR=$stage PREFIX=$base/$name \
  sh packaging/install-native.sh
top=$stage$base/$name
if [ "$system" = Linux ]; then
  install -m 0644 packaging/fn-native.service.in "$top/share/fn/systemd/fn.service.in"
else
  install -m 0644 packaging/fn.rc.in "$top/share/fn/rc.d/fn.rc.in"
fi
mkdir -p "$top/share/doc/fn"
for doc in docs/operator.md docs/peering-with-a-friend.md docs/agents.md packaging/fn.toml.example; do
  [ -r "$doc" ] || { echo "release-tarball: missing document $doc" >&2; exit 4; }
  install -m 0644 "$doc" "$top/share/doc/fn/"
done
printf '%s\n' "$rev" > "$top/share/fn/source-revision"
"${PYTHON:-python3}" tools/runpath_check.py --tree "$top" >&2
if [ "$system" = Linux ]; then
  (cd "$top" && find . -type f ! -name SHA256SUMS | LC_ALL=C sort | xargs sha256sum > SHA256SUMS)
  tar -C "$stage/opt" --owner=0 --group=0 --numeric-owner --sort=name \
      -czf "$tarball" "$name"
  (cd "$out" && sha256sum "$(basename "$tarball")" > "$(basename "$tarball").sha256")
else
  (cd "$top" && find . -type f ! -name SHA256SUMS | LC_ALL=C sort | xargs sha256 > SHA256SUMS)
  # pax(1) in ustar format from a sorted list; -d keeps it from descending, so
  # the order is the list's.  Owners are the builder's (root in the VM).
  (cd "$stage$base" && find "$name" | LC_ALL=C sort | pax -w -d -x ustar | gzip -n -9 > "$tarball")
  (cd "$out" && sha256 "$(basename "$tarball")" > "$(basename "$tarball").sha256")
fi
echo "release $tarball"
cat "$tarball.sha256"
