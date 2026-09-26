#!/bin/sh
# Build lib/libfn-mldsa65 (the ML-DSA-65 seam: host/native/fn-mldsa65.c over
# the vendored PQClean sources in third_party/pqclean-ml-dsa-65) into OUT_DIR.
#
#   tools/build_mldsa65.sh OUT_DIR
#
# Portable C99 plus getentropy(2): Linux (glibc >= 2.25, musl), OpenBSD,
# macOS.  CC and CFLAGS are honoured.  The image loads the library from the
# lib/ directory beside its core (host/native/signatures.lisp), so
# tools/build_native_host.sh builds it into build/lib and the frozen and
# installed layouts carry it in their lib/.
set -eu
[ "$#" -eq 1 ] || { echo 'usage: build_mldsa65.sh OUT_DIR' >&2; exit 2; }
out=$1
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
vendor=$root/third_party/pqclean-ml-dsa-65
cc=${CC:-cc}
case $(uname -s) in
  Darwin) name=libfn-mldsa65.dylib; shared="-dynamiclib -install_name @rpath/libfn-mldsa65.dylib" ;;
  *) name=libfn-mldsa65.so; shared="-shared -Wl,-soname,libfn-mldsa65.so" ;;
esac
mkdir -p "$out"
tmp=$out/.$name.$$
# -std=c11 for the shim's _Thread_local; the vendored sources are C99 and
# compile unchanged under it.
# shellcheck disable=SC2086
$cc -std=c11 -O2 -fPIC -fvisibility=hidden -Wall -Wextra ${CFLAGS:-} \
    -I"$vendor/clean" -I"$vendor/common" \
    $shared -o "$tmp" \
    "$root/host/native/fn-mldsa65.c" "$vendor/common/fips202.c" \
    "$vendor/clean/ntt.c" "$vendor/clean/packing.c" "$vendor/clean/poly.c" \
    "$vendor/clean/polyvec.c" "$vendor/clean/reduce.c" \
    "$vendor/clean/rounding.c" "$vendor/clean/sign.c" \
    "$vendor/clean/symmetric-shake.c"
mv -f "$tmp" "$out/$name"
echo "built $out/$name"
