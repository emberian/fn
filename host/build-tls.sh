#!/bin/sh
# Build the physical OpenSSL 3 primitive; no listener is opened.
set -eu
[ "$#" -eq 1 ] || { echo 'usage: build-tls.sh OUT_DIR' >&2; exit 2; }
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out=$1
cc=${CC:-cc}
if command -v pkg-config >/dev/null 2>&1; then
  pkg-config --atleast-version=3 openssl
  tls_cflags=$(pkg-config --cflags openssl)
  tls_libs=$(pkg-config --libs openssl)
else
  # The C source checks the actual OpenSSL header version on minimal hosts.
  tls_cflags=${OPENSSL_CFLAGS:-}
  tls_libs=${OPENSSL_LIBS:--lssl -lcrypto}
fi
case $(uname -s) in
  Darwin) name=libfn2-tls.dylib; shared=-dynamiclib ;;
  *) name=libfn2-tls.so; shared=-shared ;;
esac
mkdir -p "$out"
# OpenSSL's pkg-config flags are compiler arguments, not source/config input.
# shellcheck disable=SC2046,SC2086
$cc -std=c11 -O2 -Wall -Wextra -Werror -fPIC $shared ${CFLAGS:-} \
  $tls_cflags "$root/host/fn2-tls.c" \
  $tls_libs -o "$out/$name"
printf 'built %s/%s\n' "$out" "$name"
