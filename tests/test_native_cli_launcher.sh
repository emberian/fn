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
# The installed image answers the heap probe (PKT-016) with the line
# FAKE_HEAP names, then runs with the figure the launcher passed.
cat > "$tmp/opt/fn/libexec/fn/fn-host" <<'EOF'
#!/bin/sh
if [ "$2" = heap ]; then
  case ${FAKE_HEAP:-ok} in
    ok) printf 'heap=777 MB profile=small machine=2048 MB\n' ;;
    refuse) printf 'fn: refused machine-cannot-hold-profile heap=2671 MB machine=2048 MB\n' >&2; exit 1 ;;
    garbage) printf 'no figure\n' ;;
  esac
  exit 0
fi
printf 'installed image\n'
printf 'args=%s\n' "$SBCL_USER_ARGS" >&2
EOF
chmod 700 "$tmp/opt/fn/libexec/fn/fn-host"
printf core > "$tmp/opt/fn/libexec/fn/fn-host.core"
actual=$(FN_NATIVE_HOST="$tmp/fn-host" "$tmp/opt/fn/bin/fn" --version)
test "$actual" = 'installed image'
actual=$(env -u FN_NATIVE_HOST "$tmp/opt/fn/bin/fn" --version)
test "$actual" = 'installed image'
# The heap figure: the probe's, whatever the caller exported.
FN_TEST_HEAP_MB=32000 SBCL_USER_ARGS='--dynamic-space-size 9' \
  "$tmp/opt/fn/bin/fn" operator /x/fn.toml run >"$tmp/out" 2>"$tmp/err"
grep -q '^args=--dynamic-space-size 777$' "$tmp/err"
# A refusal at the probe is its exit code, and nothing else runs.
set +e
FAKE_HEAP=refuse "$tmp/opt/fn/bin/fn" operator /x/fn.toml run >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 1
grep -q 'refused machine-cannot-hold-profile heap=2671 MB machine=2048 MB' "$tmp/err"
test ! -s "$tmp/out"
# A probe that prints no figure is a fault (4), never a default figure.
set +e
FAKE_HEAP=garbage "$tmp/opt/fn/bin/fn" status >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 4
grep -q 'the heap probe printed no figure' "$tmp/err"
# A checkout's launcher takes FN_TEST_HEAP_MB, and only a decimal.
cat > "$tmp/fn-host-args" <<'EOF'
#!/bin/sh
printf 'args=%s\n' "$SBCL_USER_ARGS"
EOF
chmod 700 "$tmp/fn-host-args"
printf core > "$tmp/fn-host-args.core"
actual=$(FN_TEST_HEAP_MB=32000 FN_NATIVE_HOST="$tmp/fn-host-args" "$root/packaging/fn" status)
test "$actual" = 'args=--dynamic-space-size 32000'
set +e
FN_TEST_HEAP_MB=32g FN_NATIVE_HOST="$tmp/fn-host-args" "$root/packaging/fn" status >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 5
# A missing installed image is exit 4 naming it, never a fallback to the variable.
rm "$tmp/opt/fn/libexec/fn/fn-host"
set +e
FN_NATIVE_HOST="$tmp/fn-host" "$tmp/opt/fn/bin/fn" status >"$tmp/out" 2>"$tmp/err"
code=$?
set -e
test "$code" -eq 4
grep -q "native host image missing: .*/opt/fn/libexec/fn/fn-host (run" "$tmp/err"
test ! -s "$tmp/out"
