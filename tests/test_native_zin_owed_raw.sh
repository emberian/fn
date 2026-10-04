#!/bin/sh
# witness: needs-acl2
# The COMPRESS layer's inflater call over ACL2's decoder: plaintext the decoder
# still owes after a :full stop with every input octet read reaches the steps.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
native_root=${1:-$probe_root}
mkdir -p "$probe_root/build/runtime-tests"
input="$probe_root/build/runtime-tests/native-zin-owed.input.lisp"
log="$probe_root/build/runtime-tests/native-zin-owed.log"
python3 - "$probe_root" "$native_root" >"$input" <<'PY'
import pathlib, sys
probe, native = map(pathlib.Path, sys.argv[1:])
def lit(value): return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"') + '"'
print('(include-book "books/deflate-inflate" :uncertified-okp t)')
print('(defttag :fn-zin-owed-native-observation)')
print('(progn! (set-raw-mode t) (defparameter *fnzo-deflate-path* ' + lit(native/'host/native/deflate.lisp') + ') (load ' + lit(probe/'tests/native_zin_owed_raw.lisp') + '))')
print('(good-bye)')
PY
cd "$probe_root"
"$probe_root/tools/acl2" --timeout 300 --wait-seconds 30 --label zin-owed >"$log" 2>&1 <"$input"
if ! rg -q '^native_zin_owed_raw: PASS' "$log"; then
  tail -80 "$log"
  exit 1
fi
rg '^native_zin_owed_raw:' "$log"
