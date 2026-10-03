#!/bin/sh
# Generic typed output protocol test. No fresh-service reachability/heap claim.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
native_root=${1:-$probe_root}
mkdir -p "$probe_root/build/runtime-tests"
input="$probe_root/build/runtime-tests/native-output-retirement.input.lisp"
log="$probe_root/build/runtime-tests/native-output-retirement.log"
python3 - "$probe_root" "$native_root" >"$input" <<'PY'
import pathlib, sys
probe, native = map(pathlib.Path, sys.argv[1:])
def lit(value): return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"') + '"'
print('(include-book "books/resource-output" :uncertified-okp t)')
print('(include-book "books/definterface" :uncertified-okp t)')
print('(definterface create-fn-resource-ledger :class :common-lisp-compliant :raw-guarded (0 nil (fn-resource-ledger)))')
for name in ('fn-rl-install', 'fn-rlo-free-init', 'fn-rlo-issue', 'fn-rlo-output', 'fn-rlo-physical'):
    print('(definterface ' + name + ' :class :common-lisp-compliant)')
print('(defttag :fn-output-retirement-native-observation)')
print('(progn! (set-raw-mode t) (defparameter *fnor-io-path* ' + lit(native/'host/native/io.lisp') + ') (load ' + lit(probe/'tests/native_output_retirement_raw.lisp') + '))')
print('(good-bye)')
PY
cd "$probe_root"
"$probe_root/tools/acl2" --timeout 120 --wait-seconds 30 --label output-retirement >"$log" 2>&1 <"$input"
if ! rg -q '^native_output_retirement_raw: PASS' "$log"; then
  tail -80 "$log"
  exit 1
fi
rg '^native_output_retirement_raw:' "$log"
