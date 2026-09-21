#!/bin/sh
set -eu

prefix=${PREFIX:-/usr/local}
destdir=${DESTDIR:-}
image=${FN_NATIVE_HOST:-build/fn-host}
core=${FN_NATIVE_CORE:-$image.core}

case $prefix in /*) ;; *) echo "install-native: PREFIX must be absolute" >&2; exit 2;; esac
[ -x "$image" ] || { echo "install-native: missing executable image: $image" >&2; exit 4; }
[ -s "$core" ] || { echo "install-native: missing image core: $core" >&2; exit 4; }

bindir=$destdir$prefix/bin
libdir=$destdir$prefix/libexec/fn
sharedir=$destdir$prefix/share/fn
mkdir -p "$bindir" "$libdir" "$sharedir" "$sharedir/systemd" "$sharedir/launchd"
install -m 0755 "$image" "$libdir/fn-host"
install -m 0644 "$core" "$libdir/fn-host.core"
install -m 0755 packaging/fn-native "$bindir/fn"

sed "s|@PREFIX@|$prefix|g" packaging/fn-native.service.in > "$sharedir/systemd/fn.service"
sed "s|@PREFIX@|$prefix|g" packaging/net.fn.native.plist.in > "$sharedir/launchd/net.fn.plist"

hash_command=sha256sum
command -v "$hash_command" >/dev/null 2>&1 || hash_command='shasum -a 256'
{
  echo "profile=production"
  echo "launcher=$prefix/libexec/fn/fn-host"
  echo "core=$prefix/libexec/fn/fn-host.core"
  $hash_command "$libdir/fn-host" "$libdir/fn-host.core"
  if command -v otool >/dev/null 2>&1; then otool -L "$libdir/fn-host"
  elif command -v ldd >/dev/null 2>&1; then ldd "$libdir/fn-host"
  fi
} > "$sharedir/native-artifacts.txt"

echo "installed native fn under $destdir$prefix"
