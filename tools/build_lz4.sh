#!/bin/sh
# Build lib/libfn-lz4 (the LZ4 block ENCODER seam: host/native/fn-lz4.c over
# the vendored LZ4 1.10.0 sources in third_party/lz4) into OUT_DIR.
#
#   tools/build_lz4.sh OUT_DIR
#
# Portable C99 plus _Thread_local (C11): Linux (glibc, musl), OpenBSD (clang),
# macOS.  CC and CFLAGS are honoured.  The image loads the library from the
# lib/ directory beside its core (host/native/lz4.lisp), as it loads
# libfn-mldsa65 (tools/build_mldsa65.sh), so tools/build_native_host.sh builds
# it into build/lib and the frozen and installed layouts carry it in lib/.
# The encoder produces CANDIDATES only; ACL2's proved decoder checks each one
# before a record is taken (books/payload-lz-append.lisp).
set -eu
[ "$#" -eq 1 ] || { echo 'usage: build_lz4.sh OUT_DIR' >&2; exit 2; }
out=$1
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
vendor=$root/third_party/lz4
cc=${CC:-cc}
case $(uname -s) in
  Darwin) name=libfn-lz4.dylib; shared="-dynamiclib -install_name @rpath/libfn-lz4.dylib" ;;
  *) name=libfn-lz4.so; shared="-shared -Wl,-soname,libfn-lz4.so" ;;
esac
mkdir -p "$out"
tmp=$out/.$name.$$
# lz4hc.c includes lz4.c's common definitions itself; both are compiled.
# LZ4LIB_VISIBILITY= keeps every LZ4 symbol hidden (lz4.h marks them
# "default" otherwise): the library exports fn_lz4_* only, so no caller can
# reach the unverified decoder and no other liblz4 in the process can
# interpose on the encoder.
# shellcheck disable=SC2086
$cc -std=c11 -O2 -fPIC -fvisibility=hidden -DLZ4LIB_VISIBILITY= -Wall -Wextra ${CFLAGS:-} \
    -I"$vendor" $shared -o "$tmp" \
    "$root/host/native/fn-lz4.c" "$vendor/lz4.c" "$vendor/lz4hc.c"
mv -f "$tmp" "$out/$name"
echo "built $out/$name"
