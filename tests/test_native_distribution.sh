#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fn-native-dist.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
cat > "$tmp/host.c" <<'EOF'
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libproc.h>
#endif
int main(int argc, char **argv) {
  for (int i=1; i+1<argc; i++) {
    if (!strcmp(argv[i], "--fn") && !strcmp(argv[i+1], "reader")) {
      fputs("reader is available only in the developer image\n", stderr);
      return 5;
    }
  }
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
  putchar('\n'); fflush(stdout); sleep(2); return 3;
}
EOF
cc "$tmp/host.c" -o "$tmp/host-runtime"
mkdir "$tmp/sbcl-home"
printf runtime-support > "$tmp/sbcl-home/sbcl.core"
cat > "$tmp/fn-host" <<EOF
#!/bin/sh
export SBCL_HOME='$tmp/sbcl-home/'
exec "$tmp/host-runtime" --core "$tmp/fn-host.core" "\$@"
EOF
chmod 755 "$tmp/fn-host"
printf core > "$tmp/fn-host.core"
PREFIX="$tmp/root/opt/fn" FN_NATIVE_HOST="$tmp/fn-host" \
  FN_NATIVE_SOURCE_REVISION=0123456789abcdef \
  FN_NATIVE_CORE="$tmp/fn-host.core" sh "$root/packaging/install-native.sh"
test -x "$tmp/root/opt/fn/bin/fn"
test -s "$tmp/root/opt/fn/libexec/fn/fn-host.core"
test -x "$tmp/root/opt/fn/libexec/fn/runtime/sbcl"
test -s "$tmp/root/opt/fn/libexec/fn/runtime/sbcl-home/sbcl.core"
grep -q '^source_revision=0123456789abcdef$' "$tmp/root/opt/fn/share/fn/native-artifacts.txt"
grep -q '^profile=production (verified by disabled reader entrypoint)$' "$tmp/root/opt/fn/share/fn/native-artifacts.txt"
grep -q -- "--core \"$tmp/root/opt/fn/libexec/fn/fn-host.core\"" "$tmp/root/opt/fn/libexec/fn/fn-host"
grep -q "SBCL_HOME='$tmp/root/opt/fn/libexec/fn/runtime/sbcl-home/'" "$tmp/root/opt/fn/libexec/fn/fn-host"
grep -q "ExecStart=$tmp/root/opt/fn/bin/fn operator /etc/fn/fn.toml run" "$tmp/root/opt/fn/share/fn/systemd/fn.service"
grep -q "<string>$tmp/root/opt/fn/bin/fn</string>" "$tmp/root/opt/fn/share/fn/launchd/net.fn.plist"
set +e
"$tmp/root/opt/fn/bin/fn" operator /etc/fn/fn.toml status > "$tmp/out" &
native_pid=$!
sleep 1
ps -p "$native_pid" -o command= > "$tmp/process"
children=$(pgrep -P "$native_pid" 2>/dev/null || true)
wait "$native_pid"; rc=$?
set -e
out=$(cat "$tmp/out")
test "$rc" -eq 3
printf '%s\n' "$out" | grep -q "arg=--core arg=$tmp/root/opt/fn/libexec/fn/fn-host.core arg=--fn arg=operator arg=/etc/fn/fn.toml arg=status"
printf '%s\n' "$out" | grep -q 'exe=.*/libexec/fn/runtime/sbcl'
! printf '%s\n' "$out" | grep -qi python
! grep -qi python "$tmp/process"
test -z "$children"
