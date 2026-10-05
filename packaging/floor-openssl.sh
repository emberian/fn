#!/bin/sh
# Build the Linux release's OpenSSL 3.5.8 against the glibc floor (D59).
#
#   packaging/floor-openssl.sh SOURCE_TARBALL SHA256 OUT_DIR
#
# The release ships its own OpenSSL (libexec/fn/openssl/lib, PRF-1327), and
# tools/runpath_check.py holds every bundled object to GLIBC_FLOOR (Debian
# 12's 2.36).  A build on a newer glibc needs newer symbol versions (the
# build boxes' /tank/fn/toolchains/openssl-3.5.8, built on glibc 2.40,
# needs GLIBC_2.38), so this builds the same version in a Debian 12
# container, as packaging/floor-runtime.sh does for SBCL:
#
#   SOURCE_TARBALL  openssl-3.5.8.tar.gz
#   SHA256          its sha256 (checked before it is unpacked)
#   OUT_DIR         (absolute, new) receives lib/libcrypto.so.3,
#                   lib/libssl.so.3, make.log and floor-openssl.txt
#
# OPENSSLDIR is /etc/ssl, where Debian and Ubuntu keep the system's trust
# store (certs/, hashed) and openssl.cnf: a node whose peer is verified
# under the system's public roots (`peer add ... starttls - -', PKT-613)
# reads the machine's roots, never a directory of the build box.
# SSL_CERT_FILE and SSL_CERT_DIR still name others.  The engines and
# provider modules are not shipped; fn loads neither.
#
# packaging/release-tarball.sh bundles it with FN_FREEZE_OPENSSL=OUT_DIR
# (packaging/freeze-native-image.sh).  FN_FLOOR_IMAGE overrides the
# container (its glibc must not exceed the floor).
set -eu
if [ "${1:-}" = --inside ]; then
  : "${SOURCE:?}" "${OWNER:?}" "${JOBS:?}"
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -qq
  apt-get install -y -qq --no-install-recommends gcc make perl libc6-dev ca-certificates >/dev/null
  {
    echo "container glibc: $(ldd --version | head -1)"
    echo "cc: $(gcc --version | head -1)"
  } > /work/out/floor-openssl.txt
  mkdir /build && cd /build
  tar -xzf "/work/$SOURCE"
  cd openssl-*
  ./Configure linux-x86_64 shared no-tests no-docs --prefix=/opt/fn-openssl \
    --openssldir=/etc/ssl --libdir=lib > /work/out/make.log 2>&1 || {
      tail -40 /work/out/make.log >&2; exit 4; }
  make -j"$JOBS" >> /work/out/make.log 2>&1 || { tail -40 /work/out/make.log >&2; exit 4; }
  mkdir -p /work/out/lib
  cp -L libcrypto.so.3 libssl.so.3 /work/out/lib/
  # The library's own report of where it reads, beside the version.
  LD_LIBRARY_PATH=/work/out/lib ./apps/openssl version -a >> /work/out/floor-openssl.txt
  chown -R "$OWNER" /work/out
  exit 0
fi
[ "$#" -eq 3 ] || { echo 'usage: floor-openssl.sh SOURCE_TARBALL SHA256 OUT_DIR' >&2; exit 2; }
source=$1 digest=$2 out=$3
case $out in /*) ;; *) echo 'floor-openssl: OUT_DIR must be absolute' >&2; exit 2;; esac
[ ! -e "$out" ] || { echo "floor-openssl: exists: $out" >&2; exit 4; }
[ -s "$source" ] || { echo "floor-openssl: no $source" >&2; exit 4; }
case $(basename "$source") in openssl-3.5.8.tar.gz) ;; *)
  echo "floor-openssl: $source is not openssl-3.5.8.tar.gz" >&2; exit 4;; esac
[ "$(sha256sum "$source" | cut -d' ' -f1)" = "$digest" ] || {
  echo "floor-openssl: $source does not have sha256 $digest" >&2; exit 4; }
image=${FN_FLOOR_IMAGE:-debian:12}
mkdir -p "$out/work/out"
cp "$source" "$0" "$out/work/"
docker run --rm --memory "${FN_FLOOR_MEMORY:-8g}" \
  -e SOURCE="$(basename "$source")" -e OWNER="$(id -u):$(id -g)" -e JOBS="${FN_FLOOR_JOBS:-4}" \
  -v "$out/work:/work" "$image" sh "/work/$(basename "$0")" --inside
mv "$out/work/out"/* "$out/"
rm -rf "$out/work"
grep -aq 'OpenSSL 3\.5\.8 ' "$out/lib/libcrypto.so.3" || {
  echo 'floor-openssl: the built libcrypto is not OpenSSL 3.5.8' >&2; exit 4; }
{
  echo "source: $(basename "$source") $digest"
  echo "image: $image"
  sha256sum "$out/lib/libcrypto.so.3" "$out/lib/libssl.so.3"
} >> "$out/floor-openssl.txt"
cat "$out/floor-openssl.txt"
