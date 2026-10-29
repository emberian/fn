#!/bin/sh
# Build fn2's stateless exported seams over the same vendored C as fn1.
# Usage: sh fn2/host/build-blake3.sh build/lib
set -eu
[ "$#" -eq 1 ] || { echo 'usage: build_blake3.sh OUT_DIR' >&2; exit 2; }
out=$1
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
v=$root/third_party/blake3
cc=${CC:-cc}
case $(uname -s) in
  Darwin) name=libfn-blake3.dylib; shared="-dynamiclib -install_name @rpath/libfn-blake3.dylib" ;;
  *) name=libfn-blake3.so; shared="-shared -Wl,-soname,libfn-blake3.so" ;;
esac
mkdir -p "$out"
tmp=$(mktemp -d "$out/.blake3.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
flags="-std=c11 -O3 -fPIC -fvisibility=hidden ${CFLAGS:-}"
arch=$(uname -m)
case $arch in
  x86_64|amd64|arm64|aarch64) ;;
  *) flags="$flags -DBLAKE3_NO_SSE2 -DBLAKE3_NO_SSE41 -DBLAKE3_NO_AVX2 -DBLAKE3_NO_AVX512" ;;
esac
objs=
compile() { # SOURCE OBJECT EXTRA-FLAGS...
  src=$1; obj=$2; shift 2
  # shellcheck disable=SC2086
  $cc $flags "$@" -I"$v" -c "$src" -o "$tmp/$obj"
  objs="$objs $tmp/$obj"
}
compile "$root/fn2/host/fn2-blake3.c" fn-blake3.o
compile "$v/blake3_dispatch.c" dispatch.o
compile "$v/blake3_portable.c" portable.o
case $arch in
  x86_64|amd64)
    compile "$v/blake3_sse2.c" sse2.o -msse2
    compile "$v/blake3_sse41.c" sse41.o -msse4.1
    compile "$v/blake3_avx2.c" avx2.o -mavx2
    compile "$v/blake3_avx512.c" avx512.o -mavx512f -mavx512vl ;;
  arm64|aarch64)
    compile "$v/blake3_neon.c" neon.o ;;
esac
# shellcheck disable=SC2086
$cc $shared -o "$tmp/$name" $objs
mv -f "$tmp/$name" "$out/$name"
echo "built $out/$name"
