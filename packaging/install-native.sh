#!/bin/sh
set -eu

prefix=${PREFIX:-/usr/local}
destdir=${DESTDIR:-}
image=${FN_NATIVE_HOST:-build/fn-host}
core=${FN_NATIVE_CORE:-$image.core}
source_revision=${FN_NATIVE_SOURCE_REVISION:-}

case $prefix in /*) ;; *) echo "install-native: PREFIX must be absolute" >&2; exit 2;; esac
[ -x "$image" ] || { echo "install-native: missing executable image: $image" >&2; exit 4; }
[ -s "$core" ] || { echo "install-native: missing image core: $core" >&2; exit 4; }
[ -n "$source_revision" ] || { echo "install-native: FN_NATIVE_SOURCE_REVISION is required" >&2; exit 2; }

bindir=$destdir$prefix/bin
libdir=$destdir$prefix/libexec/fn
sharedir=$destdir$prefix/share/fn
mkdir -p "$bindir" "$libdir" "$sharedir" "$sharedir/systemd" "$sharedir/launchd"
grep -q '^#!.*sh' "$image" || { echo "install-native: image launcher is not the generated shell form" >&2; exit 4; }
core_refs=$(grep -o -- '--core "[^"]*"' "$image" | wc -l | tr -d ' ')
[ "$core_refs" = 1 ] || { echo "install-native: image launcher must name exactly one core" >&2; exit 4; }
runtime=$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$image")
[ -n "$runtime" ] && [ -x "$runtime" ] || { echo "install-native: generated launcher runtime is unavailable" >&2; exit 4; }
sed "s|--core \"[^\"]*\"|--core \"$prefix/libexec/fn/fn-host.core\"|" "$image" > "$libdir/fn-host"
chmod 0755 "$libdir/fn-host"
install -m 0644 "$core" "$libdir/fn-host.core"
install -m 0755 packaging/fn-native "$bindir/fn"

sed "s|@PREFIX@|$prefix|g" packaging/fn-native.service.in > "$sharedir/systemd/fn.service"
sed "s|@PREFIX@|$prefix|g" packaging/net.fn.native.plist.in > "$sharedir/launchd/net.fn.plist"

hash_command=sha256sum
command -v "$hash_command" >/dev/null 2>&1 || hash_command='shasum -a 256'
{
  echo "profile=production"
  echo "source_revision=$source_revision"
  echo "launcher=$prefix/libexec/fn/fn-host"
  echo "core=$prefix/libexec/fn/fn-host.core"
  echo "runtime=$runtime"
  echo "source-launcher-and-core:"
  $hash_command "$image" "$core"
  echo "installed-launcher-and-core:"
  $hash_command "$libdir/fn-host" "$libdir/fn-host.core"
  echo "runtime-identity:"
  $hash_command "$runtime"
  if command -v otool >/dev/null 2>&1; then otool -L "$runtime"
  elif command -v ldd >/dev/null 2>&1; then ldd "$runtime"
  fi
} > "$sharedir/native-artifacts.txt"

echo "installed native fn under $destdir$prefix"
