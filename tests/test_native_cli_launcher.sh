#!/bin/sh
# The installed direct-native entry is an exec boundary, not a Python launcher.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fn-native-cli.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

cat > "$tmp/fn-host" <<'EOF'
#!/bin/sh
test "$1" = --fn
shift
printf 'native argv:'
for word in "$@"; do printf ' <%s>' "$word"; done
printf '\n'
EOF
chmod 700 "$tmp/fn-host"
printf core > "$tmp/fn-host.core"

actual=$(FN_NATIVE_HOST="$tmp/fn-host" "$root/packaging/fn-native" store /var/lib/fn/store status)
test "$actual" = 'native argv: <store> </var/lib/fn/store> <status>'

set +e
FN_NATIVE_HOST="$tmp/missing" "$root/packaging/fn-native" status >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 4
grep -q 'native host image missing' "$tmp/err"

# PKT-481 (a): an installed bin/fn (libexec/fn beside it) runs its own
# release's image whatever FN_NATIVE_HOST says; the variable is a checkout's
# override only.
mkdir -p "$tmp/opt/fn/bin" "$tmp/opt/fn/libexec/fn"
cp "$root/packaging/fn" "$tmp/opt/fn/bin/fn"
printf '#!/bin/sh\nprintf "installed image\\n"\n' > "$tmp/opt/fn/libexec/fn/fn-host"
chmod 700 "$tmp/opt/fn/libexec/fn/fn-host"
printf core > "$tmp/opt/fn/libexec/fn/fn-host.core"
actual=$(FN_NATIVE_HOST="$tmp/fn-host" "$tmp/opt/fn/bin/fn" --version)
test "$actual" = 'installed image'
actual=$(env -u FN_NATIVE_HOST "$tmp/opt/fn/bin/fn" --version)
test "$actual" = 'installed image'
# A missing installed image is exit 4 naming it, never a fallback to the variable.
rm "$tmp/opt/fn/libexec/fn/fn-host"
set +e
FN_NATIVE_HOST="$tmp/fn-host" "$tmp/opt/fn/bin/fn" status >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 4
grep -q "native host image missing: .*/opt/fn/libexec/fn/fn-host (run" "$tmp/err"
test ! -s "$tmp/out"
