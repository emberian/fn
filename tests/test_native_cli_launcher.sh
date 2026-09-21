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
