#!/bin/sh
# Build the Linux release's SBCL runtime against the glibc floor.
#
#   packaging/floor-runtime.sh SBCL SOURCE_TARBALL OUT_DIR
#
# The floor is tools/runpath_check.py's GLIBC_FLOOR (Debian 12's glibc 2.36).
# A runtime built on a newer glibc can need newer symbol versions (SBCL
# 2.6.8's binary release needs __isoc23_strtol@GLIBC_2.38), and a saved core
# starts only on a runtime with its build-id, so this rebuilds the SAME
# runtime in a Debian 12 container:
#
#   SBCL            the runtime that saved the image's core (the generated
#                   launcher's exec path, e.g. /tank/fn/sbcl/bin/sbcl)
#   SOURCE_TARBALL  that version's sbcl-X.Y.Z-source.tar.bz2; check its
#                   sha256 against the release's signed sbcl-X.Y.Z-crhodes.asc
#   OUT_DIR         (absolute, new) receives sbcl, sbcl.core (the rebuilt
#                   base core), build-id.inc, make.log, floor-runtime.txt
#
# In `docker run debian:12' (FN_FLOOR_IMAGE overrides; its glibc must not
# exceed the floor) it installs Debian's sbcl (the cross-compilation host),
# gcc and libc6-dev, unpacks the source, changes ONE line of make-config.sh
# so output/build-id.inc is SBCL's own build-id, runs make.sh, and copies
# the runtime out.  It then checks, outside the container, that the new
# runtime prints SBCL's --version and starts SBCL's own core (a build-id or
# layout mismatch is fatal there).  packaging/release-tarball.sh
# --runtime-from OUT_DIR bundles it; freeze-native-image.sh checks that it
# starts the image's core before it copies it.
set -eu
if [ "${1:-}" = --inside ]; then
  # In the container: /work holds the source tarball and this script.
  : "${BUILD_ID:?}" "${SOURCE:?}" "${OWNER:?}"
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -qq
  apt-get install -y -qq --no-install-recommends sbcl gcc make libc6-dev bzip2 >/dev/null
  {
    echo "container glibc: $(ldd --version | head -1)"
    echo "xc host: $(sbcl --version)"
    echo "cc: $(gcc --version | head -1)"
  } > /work/out/floor-runtime.txt
  mkdir /build && cd /build
  tar -xjf "/work/$SOURCE"
  cd sbcl-*
  # The one change: SBCL's build-id instead of hostname-user-date.
  sed "s|^  echo '\"'\`hostname\`-\`id -un\`-\`date +%Y-%m-%d-%H-%M-%S\`'\"' > output/build-id.inc\$|  echo '\"$BUILD_ID\"' > output/build-id.inc|" \
    make-config.sh > make-config.sh.new
  [ "$(diff make-config.sh make-config.sh.new | grep -c '^>')" = 1 ] || {
    echo 'floor-runtime: make-config.sh has no build-id line to replace' >&2; exit 4; }
  mv make-config.sh.new make-config.sh
  sh make.sh --xc-host='sbcl --no-sysinit --no-userinit --disable-debugger' > /work/out/make.log 2>&1 || {
    tail -40 /work/out/make.log >&2; exit 4; }
  cp -p src/runtime/sbcl output/sbcl.core output/build-id.inc /work/out/
  chown -R "$OWNER" /work/out
  exit 0
fi
[ "$#" -eq 3 ] || { echo 'usage: floor-runtime.sh SBCL SOURCE_TARBALL OUT_DIR' >&2; exit 2; }
sbcl=$1 source=$2 out=$3
case $out in /*) ;; *) echo 'floor-runtime: OUT_DIR must be absolute' >&2; exit 2;; esac
[ ! -e "$out" ] || { echo "floor-runtime: exists: $out" >&2; exit 4; }
[ -x "$sbcl" ] && [ -s "$source" ] || { echo 'floor-runtime: SBCL or SOURCE_TARBALL missing' >&2; exit 4; }
version=$("$sbcl" --version)
case $(basename "$source") in "sbcl-${version#SBCL }-source.tar.bz2") ;; *)
  echo "floor-runtime: $source is not the source of $version" >&2; exit 4;; esac
# The build-id is the one string in the runtime of make-config.sh's form.
build_id=$(strings -a "$sbcl" | grep -E '^[A-Za-z0-9._+-]+-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}$|^hostname-id-[0-9]+$' | sort -u)
[ -n "$build_id" ] && [ "$(printf '%s\n' "$build_id" | wc -l | tr -d ' ')" = 1 ] || {
  echo "floor-runtime: no single build-id in $sbcl" >&2; exit 4; }
sbcl_home=$(CDPATH='' cd -- "$(dirname -- "$sbcl")/../lib/sbcl" && pwd)
[ -s "$sbcl_home/sbcl.core" ] || { echo "floor-runtime: no $sbcl_home/sbcl.core" >&2; exit 4; }
image=${FN_FLOOR_IMAGE:-debian:12}
mkdir -p "$out/work/out"
cp "$source" "$0" "$out/work/"
docker run --rm --memory "${FN_FLOOR_MEMORY:-16g}" \
  -e BUILD_ID="$build_id" -e SOURCE="$(basename "$source")" -e OWNER="$(id -u):$(id -g)" \
  -v "$out/work:/work" "$image" sh "/work/$(basename "$0")" --inside
mv "$out/work/out"/* "$out/"
rm -rf "$out/work"
[ "$("$out/sbcl" --version)" = "$version" ] || { echo 'floor-runtime: --version differs' >&2; exit 4; }
SBCL_HOME=$sbcl_home/ "$out/sbcl" --core "$sbcl_home/sbcl.core" --noinform --disable-ldb \
  --end-runtime-options --no-sysinit --no-userinit --non-interactive \
  --eval '(sb-ext:exit :code 0)' || { echo "floor-runtime: the new runtime does not start $sbcl_home/sbcl.core" >&2; exit 4; }
{
  echo "sbcl: $version, build-id $build_id"
  echo "source: $(basename "$source") $(sha256sum "$source" | cut -d' ' -f1)"
  echo "image: $image"
  echo "runtime: $(sha256sum "$out/sbcl" | cut -d' ' -f1)"
} >> "$out/floor-runtime.txt"
cat "$out/floor-runtime.txt"
