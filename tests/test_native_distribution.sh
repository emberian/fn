#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fn-native-dist.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
cat > "$tmp/host.c" <<'EOF'
#include <stdio.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libproc.h>
#endif
int main(int argc, char **argv) {
  char exe[4096];
#ifdef __APPLE__
  int n = proc_pidpath(getpid(), exe, sizeof(exe));
#else
  ssize_t n = readlink("/proc/self/exe", exe, sizeof(exe)-1);
  if (n > 0) exe[n] = 0;
#endif
  if (n > 0) printf("exe=%s\n", exe);
  printf("pid=%ld ppid=%ld", (long)getpid(), (long)getppid());
  for (int i=1; i<argc; i++) printf(" arg=%s", argv[i]);
  putchar('\n'); return 3;
}
EOF
cc "$tmp/host.c" -o "$tmp/fn-host"
printf core > "$tmp/fn-host.core"
DESTDIR="$tmp/root" PREFIX=/opt/fn FN_NATIVE_HOST="$tmp/fn-host" \
  FN_NATIVE_CORE="$tmp/fn-host.core" sh "$root/packaging/install-native.sh"
test -x "$tmp/root/opt/fn/bin/fn"
test -s "$tmp/root/opt/fn/libexec/fn/fn-host.core"
grep -q '^profile=production$' "$tmp/root/opt/fn/share/fn/native-artifacts.txt"
grep -q 'ExecStart=/opt/fn/bin/fn operator /etc/fn/fn.toml run' "$tmp/root/opt/fn/share/fn/systemd/fn.service"
grep -q '<string>/opt/fn/bin/fn</string>' "$tmp/root/opt/fn/share/fn/launchd/net.fn.plist"
set +e
out=$("$tmp/root/opt/fn/bin/fn" operator /etc/fn/fn.toml status)
rc=$?
set -e
test "$rc" -eq 3
printf '%s\n' "$out" | grep -q 'arg=--fn arg=operator arg=/etc/fn/fn.toml arg=status'
printf '%s\n' "$out" | grep -q 'exe=.*/opt/fn/libexec/fn/fn-host'
! printf '%s\n' "$out" | grep -qi python
