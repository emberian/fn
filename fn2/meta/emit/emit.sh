#!/bin/sh
# Print layer A's registry with ACL2, then emit Fn2/Instances/LayerA.lean from it.
# Run from anywhere; needs fn2/books/reference certified (fn2/tools/certify.sh books/reference.lisp).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../../.." && pwd)
: "${ACL2:=$root/tools/acl2}"
: "${ACL2_SYSTEM_BOOKS:=$HOME/tools/acl2-fn/acl2-8.7/books}"
export ACL2_SYSTEM_BOOKS
cd "$root"
log=$(mktemp "${TMPDIR:-/tmp}/fn2-meta-print-XXXXXX")
"$ACL2" < fn2/meta/emit/print-registry.lsp > "$log" 2>&1 || :
if ! grep -F 'FN2-META-PRINT-REGISTRY PASS' "$log" >/dev/null; then
  tail -40 "$log"; echo "print-registry FAILED (log $log)"; exit 1
fi
python3 -I "$here/emit_lean.py" "$here/registry.sexp" "$root/fn2/meta/Fn2/Instances/LayerA.lean"
