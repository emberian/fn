#!/bin/sh
# First actual-host discrimination; does not claim certification or tariff.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
mkdir -p "$probe_root/build/runtime-tests"
log="$probe_root/build/runtime-tests/native-output-response-lease.log"
input="$probe_root/build/runtime-tests/native-output-response-lease.input.lisp"
snapshot="$probe_root/build/runtime-tests/native-output-response-lease-sources.json"
python3 - "$probe_root" "$snapshot" <<'PYDATA'
import hashlib, json, pathlib, subprocess, sys
probe, dest = map(pathlib.Path, sys.argv[1:])
paths = [probe / p for p in ('books/native-config.lisp', 'books/output-reservation.lisp',
    'books/resource-output.lisp', 'books/resource-vector-exec.lisp',
    'books/definterface.lisp', 'books/response-identity.lisp', 'host/interfaces.lisp', 'host/native/io.lisp', 'host/native/owner.lisp', 'host/native/mux.lisp', 'tests/native_output_custody_raw.lisp',
    'tests/native_output_response_lease_counterpart.lisp', 'tests/test_native_output_response_lease_counterpart.sh')]
dest.write_text(json.dumps({'source_head': subprocess.check_output(
    ['git', '-C', str(probe), 'rev-parse', 'HEAD'], text=True).strip(),
    'kind': 'actual native custody discrimination, not certification or full allocation tariff',
    'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}, indent=2) + '\n')
PYDATA
python3 - "$probe_root/tests/native_output_response_lease_counterpart.lisp" "$probe_root" >"$input" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[2]) / "tools"))
from proof_repl import forms
def lit(s): return '"' + s.replace('\\','\\\\').replace('"','\\"') + '"'
print('(include-book "books/resource-output")')
print('(include-book "books/definterface")')
print('(include-book "books/response-identity")')
print('(definterface fn-rid-response :class :common-lisp-compliant)')
print('(definterface create-fn-resource-ledger :class :common-lisp-compliant :raw-guarded (0 nil (fn-resource-ledger)))')
for form in forms((pathlib.Path(sys.argv[2]) / 'host/interfaces.lisp').read_text()):
    if form.startswith('(definterface fn-rlo-'):
        print(form)
print('(defttag :fn-output-custody-native-observation)')
print('(progn! (set-raw-mode t) (load ' + lit(sys.argv[1]) + '))')
print('(good-bye)')
PY
cd "$probe_root"
"$probe_root/tools/acl2" --timeout 120 --wait-seconds 30 --label output-custody >"$log" 2>&1 <"$input"
if ! rg -q '^native_output_response_lease_counterpart: PASS' "$log"; then
  tail -90 "$log"
  exit 1
fi
python3 - "$snapshot" <<'PYDATA'
import hashlib, json, pathlib, sys
for name, expected in json.loads(pathlib.Path(sys.argv[1]).read_text())['sha256'].items():
    if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() != expected:
        raise SystemExit('REFUSED: custody probe source changed: ' + name)
PYDATA
rg '^native_output_response_lease_counterpart:' "$log"
