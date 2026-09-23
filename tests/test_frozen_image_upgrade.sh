#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fn-image-upgrade.XXXXXX")
tmp=$(CDPATH= cd -- "$tmp" && pwd)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
mkdir -p "$tmp/build" "$tmp/openssl/lib" "$tmp/home" "$tmp/node/releases" "$tmp/node/store" "$tmp/node/tls" "$tmp/mock"
printf core > "$tmp/home/sbcl.core"
printf crypto > "$tmp/openssl/lib/libcrypto.so.3"
printf ssl > "$tmp/openssl/lib/libssl.so.3"
printf sodium > "$tmp/libsodium.so.23"
cat > "$tmp/runtime" <<'RUNTIME'
#!/bin/sh
if [ "${3:-}" = --fn ] && [ "${4:-}" = reader ]; then
  echo 'reader is available only in the developer image' >&2
  exit 5
fi
[ -s "$2" ] && [ -s "$SBCL_HOME/sbcl.core" ] && [ -s "$FN_OPENSSL_PREFIX/lib/libcrypto.so.3" ] || exit 8
printf '%s\n' "$2"
RUNTIME
chmod +x "$tmp/runtime"
for name in fn-host fn-host-developer fn-host-dtn fn-host-dtn-developer; do
  cat > "$tmp/build/$name" <<LAUNCHER
#!/bin/sh
export SBCL_HOME='$tmp/home/'
exec "$tmp/runtime" --core "$tmp/build/$name.core" "\$@"
LAUNCHER
  chmod +x "$tmp/build/$name"
  printf '%s' "$name-core" > "$tmp/build/$name.core"
done
FN_FREEZE_SODIUM="$tmp/libsodium.so.23" sh "$root/packaging/freeze-native-image.sh" \
  "$tmp/build" "$tmp/image" "$tmp/openssl"
# The source core and runtime can vanish without changing the frozen launch.
mv "$tmp/build" "$tmp/removed-build"
mv "$tmp/runtime" "$tmp/removed-runtime"
for name in fn-host fn-host-developer fn-host-dtn fn-host-dtn-developer; do
  output=$("$tmp/image/$name" --fn operator /none status)
  test "$output" = "$tmp/image/$name.core"
done
cat > "$tmp/mock/ldconfig" <<'LDCONFIG'
#!/bin/sh
printf '%s\n' 'libsodium.so.23 (libc6) => /mock/libsodium.so.23' 'libcrypto.so.3 (libc6) => /mock/libcrypto.so.3' 'libssl.so.3 (libc6) => /mock/libssl.so.3'
LDCONFIG
chmod +x "$tmp/mock/ldconfig"
PATH="$tmp/mock:$PATH" PREFIX="$tmp/node/releases/old" FN_NATIVE_HOST="$tmp/image/fn-host" \
  FN_NATIVE_SOURCE_REVISION=old sh "$root/packaging/install-native.sh" >/dev/null
ln -s "$tmp/node/releases/old" "$tmp/node/current"
for file in fn.toml credentials.txt tls/cert.pem tls/key.pem; do printf '%s' "$file-stable" > "$tmp/node/$file"; done
printf article-octets > "$tmp/node/store/article.octets"
cat > "$tmp/control" <<'CONTROL'
#!/bin/sh
case "$1" in
  stop) : > "$2/stopped" ;;
  start) : > "$2/started" ;;
  check) [ -s "$2/current/libexec/fn/fn-host.core" ] || exit 1
         [ ! -e "$2/fail-next" ] || { rm "$2/fail-next"; exit 1; } ;;
esac
CONTROL
chmod +x "$tmp/control"
PATH="$tmp/mock:$PATH" FN_UPGRADE_CONTROL="$tmp/control" \
  sh "$root/packaging/upgrade-native.sh" "$tmp/node" "$tmp/image" good >/dev/null
[ "$(readlink "$tmp/node/current")" = "$tmp/node/releases/good" ]
test "$("$tmp/node/current/bin/fn" operator /none status)" = "$tmp/node/current/libexec/fn/fn-host.core"
: > "$tmp/node/fail-next"
set +e
PATH="$tmp/mock:$PATH" FN_UPGRADE_CONTROL="$tmp/control" \
  sh "$root/packaging/upgrade-native.sh" "$tmp/node" "$tmp/image" bad > "$tmp/out" 2> "$tmp/err"
rc=$?
set -e
test "$rc" -eq 5
[ "$(readlink "$tmp/node/current")" = "$tmp/node/releases/good" ]
test "$("$tmp/node/current/bin/fn" operator /none status)" = "$tmp/node/current/libexec/fn/fn-host.core"
for file in fn.toml credentials.txt tls/cert.pem tls/key.pem; do test "$(cat "$tmp/node/$file")" = "$file-stable"; done
test "$(cat "$tmp/node/store/article.octets")" = article-octets
# A modified frozen core fails preflight without switching the running release.
printf tamper >> "$tmp/image/fn-host.core"
set +e
PATH="$tmp/mock:$PATH" FN_UPGRADE_CONTROL="$tmp/control" \
  sh "$root/packaging/upgrade-native.sh" "$tmp/node" "$tmp/image" tampered > "$tmp/out" 2> "$tmp/err"
rc=$?
set -e
test "$rc" -eq 4
grep -q 'frozen image digest check failed' "$tmp/err"
[ "$(readlink "$tmp/node/current")" = "$tmp/node/releases/good" ]
