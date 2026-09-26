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
for support in packaging/fn packaging/fn-native.service.in packaging/net.fn.native.plist.in packaging/fn.rc.in; do
  [ -r "$support" ] || { echo "install-native: missing package input: $support" >&2; exit 4; }
done
grep -q '^#!.*sh' "$image" || { echo "install-native: image launcher is not the generated shell form" >&2; exit 4; }
if grep -q '^# fn frozen image launcher v2$' "$image"; then
  image_dir=$(CDPATH= cd -- "$(dirname -- "$image")" && pwd)
  launcher_core=$image_dir/$(basename -- "$image").core
  runtime=$image_dir/runtime/sbcl
  sbcl_home=$image_dir/runtime/sbcl-home
  # Linux freezes list `sha256sum' lines; OpenBSD's base `sha256' writes
  # and checks its own BSD-format lines (packaging/freeze-native-image.sh).
  if command -v sha256sum >/dev/null 2>&1; then check_sums='sha256sum -c'; else check_sums='sha256 -c'; fi
  [ -s "$image_dir/image.sha256" ] &&
    (cd "$image_dir" && $check_sums image.sha256 >/dev/null) || {
      echo "install-native: frozen image digest check failed" >&2; exit 4; }
  if [ "$(uname -s)" = OpenBSD ]; then
    # libsodium keeps its OpenBSD name (libsodium.so.MAJOR.MINOR).
    set -- "$image_dir"/lib/libsodium.so.*
    [ -s "$1" ] && [ -s "$image_dir/lib/libfn-mldsa65.so" ] || {
      echo "install-native: frozen crypto dependencies missing" >&2; exit 4; }
  else
    [ -s "$image_dir/lib/libsodium.so.23" ] &&
    [ -s "$image_dir/lib/libfn-mldsa65.so" ] || {
      echo "install-native: frozen crypto dependencies missing" >&2; exit 4; }
  fi
  frozen=yes
else
  core_refs=$(grep -o -- '--core "[^"]*"' "$image" | wc -l | tr -d ' ')
  [ "$core_refs" = 1 ] || { echo "install-native: image launcher must name exactly one core" >&2; exit 4; }
  launcher_core=$(sed -n 's/.*--core "\([^"]*\)".*/\1/p' "$image")
  runtime=$(sed -n 's/^exec "\([^"]*\)" .*/\1/p' "$image")
  sbcl_home=$(sed -n "s/^export SBCL_HOME='\([^']*\)'/\1/p" "$image")
  # The ML-DSA-65 library the image loads from lib/ beside its core.
  mldsa=
  for candidate in "$(dirname -- "$launcher_core")/lib/libfn-mldsa65.so" \
                   "$(dirname -- "$launcher_core")/lib/libfn-mldsa65.dylib"; do
    [ ! -s "$candidate" ] || mldsa=$candidate
  done
  [ -n "$mldsa" ] || {
    echo "install-native: no lib/libfn-mldsa65 beside the core (tools/build_mldsa65.sh)" >&2; exit 4; }
  frozen=no
fi
[ -s "$launcher_core" ] || { echo "install-native: generated launcher core is unavailable" >&2; exit 4; }
cmp -s "$core" "$launcher_core" || {
  echo "install-native: FN_NATIVE_CORE does not match the generated launcher core" >&2; exit 4; }
[ -n "$runtime" ] && [ -x "$runtime" ] || { echo "install-native: generated launcher runtime is unavailable" >&2; exit 4; }
[ -n "$sbcl_home" ] && [ -d "$sbcl_home" ] || { echo "install-native: generated launcher SBCL_HOME is unavailable" >&2; exit 4; }

hash_command=sha256sum
command -v "$hash_command" >/dev/null 2>&1 || hash_command='shasum -a 256'
command -v sha256sum >/dev/null 2>&1 || ! command -v sha256 >/dev/null 2>&1 || hash_command='sha256 -r'
# The system provides the TLS library (OpenSSL 3.0+ or LibreSSL 3+; the
# image checks the version and every function at start).  libsodium comes
# from the frozen lib/ or the system; ML-DSA-65 from lib/ (HST-016).
crypto_inventory=
if [ "$(uname -s)" = OpenBSD ]; then
  ls /usr/lib/libssl.so.* /usr/lib/libcrypto.so.* >/dev/null 2>&1 || {
    echo "install-native: the base system's LibreSSL libssl/libcrypto are unavailable" >&2; exit 4; }
  [ "$frozen" = yes ] || ls /usr/local/lib/libsodium.so.* >/dev/null 2>&1 || {
    echo "install-native: libsodium shared library is unavailable" >&2; exit 4; }
  crypto_inventory=$(ls /usr/lib/libssl.so.* /usr/lib/libcrypto.so.* /usr/local/lib/libsodium.so.* 2>/dev/null || true)
elif command -v ldconfig >/dev/null 2>&1; then
  crypto_inventory=$(ldconfig -p 2>/dev/null || true)
  [ "$frozen" = yes ] || printf '%s\n' "$crypto_inventory" | grep -Eq 'libsodium\.so(\.23)? ' || {
    echo "install-native: libsodium shared library is unavailable" >&2; exit 4; }
  printf '%s\n' "$crypto_inventory" | grep -q 'libcrypto\.so\.3 ' || {
    echo "install-native: the system's OpenSSL 3 libcrypto is unavailable" >&2; exit 4; }
  printf '%s\n' "$crypto_inventory" | grep -q 'libssl\.so\.3 ' || {
    echo "install-native: the system's OpenSSL 3 libssl is unavailable" >&2; exit 4; }
elif [ "$frozen" = yes ]; then
  echo "install-native: cannot check the system's TLS library (no ldconfig)" >&2; exit 4
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
mkdir -p "$bindir" "$libdir" "$sharedir"
mkdir -p "$libdir/runtime/sbcl-home"
install -m 0755 "$runtime" "$libdir/runtime/sbcl"
cp -RL "$sbcl_home"/. "$libdir/runtime/sbcl-home"/
mkdir -p "$libdir/lib"
if [ "$frozen" = yes ]; then
  cp -p "$image_dir/lib/"* "$libdir/lib/"
  cp -p "$image" "$libdir/fn-host"
else
  cp -p "$mldsa" "$libdir/lib/"

  sed -e "s|^export SBCL_HOME='[^']*'|export SBCL_HOME='$prefix/libexec/fn/runtime/sbcl-home/'|" \
      -e "s|^exec \"[^\"]*\"|exec \"$prefix/libexec/fn/runtime/sbcl\"|" \
      -e "s|--core \"[^\"]*\"|--core \"$prefix/libexec/fn/fn-host.core\"|" \
      "$image" > "$libdir/fn-host"
fi
chmod 0755 "$libdir/fn-host"
install -m 0644 "$core" "$libdir/fn-host.core"
install -m 0755 packaging/fn "$bindir/fn"
# `fn --version' reads the revision beside the core (host/native/io.lisp
# fnn-source-revision); a non-commit revision word leaves it absent.
case $source_revision in
  *[!0-9a-f]*) ;;
  *) if [ "${#source_revision}" -eq 40 ]; then
       printf '%s\n' "$source_revision" > "$libdir/source-revision"
     fi ;;
esac

if [ "$(uname -s)" = OpenBSD ]; then
  mkdir -p "$sharedir/rc.d"
  sed "s|@PREFIX@|$prefix|g" packaging/fn.rc.in > "$sharedir/rc.d/fn"
  chmod 0555 "$sharedir/rc.d/fn"
else
  mkdir -p "$sharedir/systemd" "$sharedir/launchd"
  sed "s|@PREFIX@|$prefix|g" packaging/fn-native.service.in > "$sharedir/systemd/fn.service"
  sed "s|@PREFIX@|$prefix|g" packaging/net.fn.native.plist.in > "$sharedir/launchd/net.fn.plist"
fi

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
  if [ "$(uname -s)" = OpenBSD ]; then objdump -p "$runtime" | awk '$1 == "NEEDED"'
  elif command -v otool >/dev/null 2>&1; then otool -L "$runtime"
  elif command -v ldd >/dev/null 2>&1; then ldd "$runtime"
  fi
  echo "dlopen-requirements: system libcrypto+libssl (OpenSSL 3.0+ or LibreSSL 3+), libsodium, lib/libfn-mldsa65 (bundled)"
  if [ "$frozen" = yes ]; then
    $hash_command "$image_dir"/lib/*
    $hash_command "$libdir"/lib/*
  else
    $hash_command "$mldsa" "$libdir/lib/$(basename -- "$mldsa")"
  fi
  if [ -n "$crypto_inventory" ]; then
    printf '%s\n' "$crypto_inventory" | grep -E 'libsodium\.so|libcrypto\.so|libssl\.so'
  elif [ "$frozen" = no ]; then
    $hash_command "$sodium_path" "$crypto_path" "$ssl_path"
  fi
} > "$sharedir/native-artifacts.txt"

echo "installed native fn under $destdir$prefix"
