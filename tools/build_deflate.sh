#!/bin/sh
# Build lib/libfn-deflate (the COMPRESS DEFLATE outbound compressor:
# host/native/fn-deflate.c over the vendored zlib 1.3.2 deflate sources in
# third_party/zlib) into OUT_DIR.
#
#   tools/build_deflate.sh OUT_DIR
#
# Portable C99: Linux, OpenBSD (clang), macOS.  CC and CFLAGS are honoured.
# The image loads it from the lib/ directory beside its core
# (host/native/deflate.lisp), as it loads libfn-lz4 (tools/build_lz4.sh).
# Z_SOLO leaves out the gzip file layer (the allocator is fn-deflate.c's).
# -fvisibility=hidden hides every zlib symbol but the fn_deflate_* entries, so no
# other libz in the process can interpose on it and no caller reaches zlib.
set -eu
[ "$#" -eq 1 ] || { echo 'usage: build_deflate.sh OUT_DIR' >&2; exit 2; }
out=$1
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
vendor=$root/third_party/zlib
cc=${CC:-cc}
case $(uname -s) in
  Darwin) name=libfn-deflate.dylib; shared="-dynamiclib -install_name @rpath/libfn-deflate.dylib" ;;
  *) name=libfn-deflate.so; shared="-shared -Wl,-soname,libfn-deflate.so" ;;
esac
mkdir -p "$out"
tmp=$out/.$name.$$
# shellcheck disable=SC2086
$cc -std=c99 -O2 -fPIC -fvisibility=hidden -DZ_SOLO -Wall ${CFLAGS:-} \
    -I"$vendor" $shared -o "$tmp" \
    "$root/host/native/fn-deflate.c" "$vendor/deflate.c" "$vendor/trees.c" \
    "$vendor/zutil.c" "$vendor/adler32.c" "$vendor/crc32.c"
mv -f "$tmp" "$out/$name"
echo "built $out/$name"
