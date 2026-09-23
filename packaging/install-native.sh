#!/bin/sh
set -eu

prefix=${PREFIX:-/usr/local}
destdir=${DESTDIR:-}
image=${FN_NATIVE_HOST:-build/fn-host}
core=${FN_NATIVE_CORE:-$image.core}
source_revision=${FN_NATIVE_SOURCE_REVISION:-}

case $prefix in /*) ;; *) echo "install-native: PREFIX must be absolute" >&2; exit 2;; esac
case $prefix in *[!A-Za-z0-9_./-]*) echo "install-native: PREFIX contains unsupported characters" >&2; exit 2;; esac
case $source_revision in ''|*[!A-Za-z0-9._-]*) echo "install-native: invalid FN_NATIVE_SOURCE_REVISION" >&2; exit 2;; esac
[ -x "$image" ] || { echo "install-native: missing executable image: $image" >&2; exit 4; }
[ -s "$core" ] || { echo "install-native: missing image core: $core" >&2; exit 4; }
for support in packaging/fn-native packaging/fn-native.service.in packaging/net.fn.native.plist.in; do
  [ -r "$support" ] || { echo "install-native: missing package input: $support" >&2; exit 4; }
done
grep -q '^#!.*sh' "$image" || { echo "install-native: image launcher is not the generated shell form" >&2; exit 4; }
if grep -q '^# fn frozen image launcher v1$' "$image"; then
  image_dir=$(CDPATH= cd -- "$(dirname -- "$image")" && pwd)
  launcher_core=$image_dir/$(basename -- "$image").core
  runtime=$image_dir/runtime/sbcl
  sbcl_home=$image_dir/runtime/sbcl-home
  [ -s "$image_dir/image.sha256" ] &&
    (cd "$image_dir" && sha256sum -c image.sha256 >/dev/null) || {
      echo "install-native: frozen image digest check failed" >&2; exit 4; }
  [ -s "$image_dir/openssl/lib/libcrypto.so.3" ] &&
  [ -s "$image_dir/openssl/lib/libssl.so.3" ] &&
  [ -s "$image_dir/lib/libsodium.so.23" ] || {
    echo "install-native: frozen crypto dependencies missing" >&2; exit 4; }
  frozen=yes
else
  core_refs=$(grep -o -- '--core "[^"]*"' "$image" | wc -l | tr -d ' ')
  [ "$core_refs" = 1 ] || { echo "install-native: image launcher must name exactly one core" >&2; exit 4; }
  launcher_core=$(sed -n 's/.*--core "\([^"]*\)".*/\1/p' "$image")
  runtime=$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$image")
  sbcl_home=$(sed -n "s/^export SBCL_HOME='\([^']*\)'/\1/p" "$image")
  frozen=no
fi
[ -s "$launcher_core" ] || { echo "install-native: generated launcher core is unavailable" >&2; exit 4; }
cmp -s "$core" "$launcher_core" || {
  echo "install-native: FN_NATIVE_CORE does not match the generated launcher core" >&2; exit 4; }
[ -n "$runtime" ] && [ -x "$runtime" ] || { echo "install-native: generated launcher runtime is unavailable" >&2; exit 4; }
[ -n "$sbcl_home" ] && [ -d "$sbcl_home" ] || { echo "install-native: generated launcher SBCL_HOME is unavailable" >&2; exit 4; }

hash_command=sha256sum
command -v "$hash_command" >/dev/null 2>&1 || hash_command='shasum -a 256'
crypto_inventory=
if [ "$frozen" = yes ]; then
  : # The frozen launcher loads the pinned libraries in its own directory.
elif command -v ldconfig >/dev/null 2>&1; then
  crypto_inventory=$(ldconfig -p 2>/dev/null || true)
  printf '%s\n' "$crypto_inventory" | grep -Eq 'libsodium\.so(\.23)? ' || {
    echo "install-native: libsodium shared library is unavailable" >&2; exit 4; }
  printf '%s\n' "$crypto_inventory" | grep -q 'libcrypto\.so\.3 ' || {
    echo "install-native: OpenSSL 3 libcrypto is unavailable" >&2; exit 4; }
  printf '%s\n' "$crypto_inventory" | grep -q 'libssl\.so\.3 ' || {
    echo "install-native: OpenSSL 3 libssl is unavailable" >&2; exit 4; }
else
  sodium_path=
  crypto_path=
  ssl_path=
  for dependency in /opt/homebrew/opt/libsodium/lib/libsodium.dylib /usr/local/opt/libsodium/lib/libsodium.dylib; do
    [ ! -f "$dependency" ] || sodium_path=$dependency
  done
  for dependency in /opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib /usr/local/opt/openssl@3/lib/libcrypto.3.dylib; do
    [ ! -f "$dependency" ] || crypto_path=$dependency
  done
  for dependency in /opt/homebrew/opt/openssl@3/lib/libssl.3.dylib /usr/local/opt/openssl@3/lib/libssl.3.dylib; do
    [ ! -f "$dependency" ] || ssl_path=$dependency
  done
  [ -n "$sodium_path" ] || { echo "install-native: libsodium shared library is unavailable" >&2; exit 4; }
  [ -n "$crypto_path" ] && [ -n "$ssl_path" ] || {
    echo "install-native: OpenSSL 3 shared libraries are unavailable" >&2; exit 4; }
fi

profile_out=$(mktemp "${TMPDIR:-/tmp}/fn-native-profile.XXXXXX") || exit 4
trap 'rm -f "$profile_out"' EXIT HUP INT TERM
set +e
ACL2_CUSTOMIZATION=NONE env -u ACL2_SYSTEM_BOOKS "$image" --fn reader invalid-port 1 - \
  > /dev/null 2> "$profile_out"
profile_rc=$?
set -e
if [ "$profile_rc" -ne 5 ] || ! grep -Fq 'reader is available only in the developer image' "$profile_out"; then
  echo "install-native: image did not identify itself as the production profile" >&2
  exit 4
fi
rm -f "$profile_out"
trap - EXIT HUP INT TERM

bindir=$destdir$prefix/bin
libdir=$destdir$prefix/libexec/fn
sharedir=$destdir$prefix/share/fn
mkdir -p "$bindir" "$libdir" "$sharedir" "$sharedir/systemd" "$sharedir/launchd"
mkdir -p "$libdir/runtime/sbcl-home"
install -m 0755 "$runtime" "$libdir/runtime/sbcl"
cp -RL "$sbcl_home"/. "$libdir/runtime/sbcl-home"/
if [ "$frozen" = yes ]; then
  mkdir -p "$libdir/openssl/lib" "$libdir/lib"
  cp -p "$image_dir/openssl/lib/"* "$libdir/openssl/lib/"
  cp -p "$image_dir/lib/"* "$libdir/lib/"
  cp -p "$image" "$libdir/fn-host"
else
  sed -e "s|^export SBCL_HOME='[^']*'|export SBCL_HOME='$prefix/libexec/fn/runtime/sbcl-home/'|" \
      -e "s|^exec \"[^\"]*\"|exec \"$prefix/libexec/fn/runtime/sbcl\"|" \
      -e "s|--core \"[^\"]*\"|--core \"$prefix/libexec/fn/fn-host.core\"|" \
      "$image" > "$libdir/fn-host"
fi
chmod 0755 "$libdir/fn-host"
install -m 0644 "$core" "$libdir/fn-host.core"
install -m 0755 packaging/fn-native "$bindir/fn"

sed "s|@PREFIX@|$prefix|g" packaging/fn-native.service.in > "$sharedir/systemd/fn.service"
sed "s|@PREFIX@|$prefix|g" packaging/net.fn.native.plist.in > "$sharedir/launchd/net.fn.plist"

{
  echo "profile=production (verified by disabled reader entrypoint)"
  echo "source_revision=$source_revision"
  echo "launcher=$prefix/libexec/fn/fn-host"
  echo "core=$prefix/libexec/fn/fn-host.core"
  echo "runtime=$runtime"
  echo "installed_runtime=$prefix/libexec/fn/runtime/sbcl"
  echo "installed_sbcl_home=$prefix/libexec/fn/runtime/sbcl-home"
  echo "source-launcher-and-core:"
  $hash_command "$image" "$core"
  echo "installed-launcher-and-core:"
  $hash_command "$libdir/fn-host" "$libdir/fn-host.core"
  echo "runtime-identity:"
  $hash_command "$runtime" "$libdir/runtime/sbcl"
  if command -v otool >/dev/null 2>&1; then otool -L "$runtime"
  elif command -v ldd >/dev/null 2>&1; then ldd "$runtime"
  fi
  echo "dlopen-requirements: libsodium.so.23|libsodium.so libcrypto.so.3 libssl.so.3"
  if [ "$frozen" = yes ]; then
    $hash_command "$image_dir/openssl/lib/libcrypto.so.3" "$image_dir/openssl/lib/libssl.so.3" "$image_dir/lib/libsodium.so.23"
    $hash_command "$libdir/openssl/lib/libcrypto.so.3" "$libdir/openssl/lib/libssl.so.3" "$libdir/lib/libsodium.so.23"
  elif [ -n "$crypto_inventory" ]; then
    printf '%s\n' "$crypto_inventory" | grep -E 'libsodium\.so(\.23)?|libcrypto\.so\.3|libssl\.so\.3'
  else
    $hash_command "$sodium_path" "$crypto_path" "$ssl_path"
  fi
} > "$sharedir/native-artifacts.txt"

echo "installed native fn under $destdir$prefix"
