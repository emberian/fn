#!/bin/sh
# witness: needs-acl2
# First actual-host discrimination; does not claim certification or tariff.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
served_root=${1:-$probe_root}
test -f "$served_root/books/string-line-cursor.lisp"
mkdir -p "$probe_root/build/runtime-tests"
log="$probe_root/build/runtime-tests/native-output-custody.log"
input="$probe_root/build/runtime-tests/native-output-custody.input.lisp"
snapshot="$probe_root/build/runtime-tests/native-output-custody-sources.json"
python3 - "$probe_root" "$served_root" "$snapshot" <<'PYDATA'
import hashlib, json, pathlib, subprocess, sys
probe, served, dest = map(pathlib.Path, sys.argv[1:])
paths = [probe / p for p in ('books/native-config.lisp', 'books/output-reservation.lisp',
    'books/resource-output.lisp', 'books/resource-vector-exec.lisp',
    'books/definterface.lisp', 'host/interfaces.lisp', 'host/native/io.lisp',
    'tests/native_output_custody_raw.lisp', 'tests/test_native_output_custody_raw.sh')]
paths += [served / p for p in ('books/string-line-cursor.lisp', 'books/def-cursor.lisp')]
dest.write_text(json.dumps({'source_head': subprocess.check_output(
    ['git', '-C', str(probe), 'rev-parse', 'HEAD'], text=True).strip(),
    'kind': 'actual native custody discrimination, not certification or full allocation tariff',
    'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}, indent=2) + '\n')
PYDATA
python3 - "$served_root/books/string-line-cursor" "$probe_root/tests/native_output_custody_raw.lisp" "$probe_root" >"$input" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[3]) / "tools"))
from proof_repl import forms
def lit(s): return '"' + s.replace('\\','\\\\').replace('"','\\"') + '"'
print('(include-book "books/resource-output")')
print('(include-book ' + lit(sys.argv[1]) + ')')
print('(include-book "books/definterface")')
print('(definterface create-fn-resource-ledger :class :common-lisp-compliant :raw-guarded (0 nil (fn-resource-ledger)))')
for form in forms((pathlib.Path(sys.argv[3]) / 'host/interfaces.lisp').read_text()):
    if form.startswith('(definterface fn-rlo-'):
        print(form)
print('(definterface fn-sl-step :class :common-lisp-compliant :kinds ((bytes natp)))')
print('(defttag :fn-output-custody-native-observation)')
print('(progn! (set-raw-mode t) (load ' + lit(sys.argv[2]) + '))')
print('(good-bye)')
PY
cd "$probe_root"
"$probe_root/tools/acl2" --timeout 90 --wait-seconds 30 --label output-custody >"$log" 2>&1 <"$input"
if ! rg -q '^native_output_custody_raw: PASS' "$log"; then
  tail -90 "$log"
  exit 1
fi
python3 - "$snapshot" <<'PYDATA'
import hashlib, json, pathlib, sys
for name, expected in json.loads(pathlib.Path(sys.argv[1]).read_text())['sha256'].items():
    if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() != expected:
        raise SystemExit('REFUSED: custody probe source changed: ' + name)
PYDATA
rg '^native_output_custody_raw:' "$log"
