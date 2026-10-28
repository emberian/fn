#!/bin/sh
# Paths are relative to fn2/: books/pool.lisp tests/pool-unit.lisp.
# Root-relative fn2/... paths are accepted too. One cert.pl per worktree.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
# Use the same slot pool and project map as source iteration. A direct
# binary misses :FN when a dependency was certified through tools/acl2.
: "${ACL2:=$root/tools/acl2}"
: "${ACL2_SYSTEM_BOOKS:=$HOME/tools/acl2-fn/acl2-8.7/books}"
ACL2_BOOK_HASH_ALISTP=NIL
export ACL2 ACL2_SYSTEM_BOOKS ACL2_BOOK_HASH_ALISTP
mkdir -p "$root/build"
lock="$root/build/fn2-certify.lock"
until mkdir "$lock" 2>/dev/null; do sleep 1; done
trap 'rmdir "$lock" 2>/dev/null || :' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cd "$root/fn2"
# Rotate arguments through the positional parameters without word splitting.
export_owed=0
n=$#
while [ "$n" -gt 0 ]; do
  arg=$1; shift
  case "$arg" in
    --export-owed) export_owed=1 ;;
    fn2/*) set -- "$@" "${arg#fn2/}" ;;
    *) set -- "$@" "$arg" ;;
  esac
  n=$((n-1))
done
log=$(mktemp "$root/build/fn2-certify-XXXXXX")
# Keep cert.pl's exit status out of the verdict: ACL2 also exits zero on errors.
if [ "$#" -gt 0 ]; then
  perl "$ACL2_SYSTEM_BOOKS/build/cert.pl" --acl2 "$ACL2" "$@" > "$log" 2>&1 || :
fi
cat "$log"
if grep -F '**CERTIFICATION FAILED**' "$log" >/dev/null; then exit 1; fi
for arg do
  case "$arg" in
    *.lisp) test -f "${arg%.lisp}.cert" || exit 1 ;;
    *.cert) test -f "$arg" || exit 1 ;;
  esac
done

# Export only from the admitted world; LD stops at any include/check error.
if [ "$export_owed" -eq 1 ]; then
  cd "$root"
  export_log=$(mktemp "$root/build/fn2-owed-export-XXXXXX")
  timeout 300 "$ACL2" > "$export_log" 2>&1 <<'EOF'
(ld "fn2/tools/owed-export.lsp" :ld-error-action :return)
(good-bye)
EOF
  cat "$export_log"
  grep -F 'FN2-OWED-EXPORT PASS' "$export_log" >/dev/null || exit 1
fi
