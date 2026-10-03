#!/bin/sh
# Raw allocation observation, deliberately separate from proof/certification.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
source_root=${1:-$probe_root}
test -f "$source_root/books/string-line-cursor.lisp"
mkdir -p "$probe_root/build/runtime-tests"
log="$probe_root/build/runtime-tests/native-string-line-allocation.log"
input="$probe_root/build/runtime-tests/native-string-line-allocation.input.lisp"
snapshot="$probe_root/build/runtime-tests/native-string-line-allocation-sources.json"
python3 - "$source_root" "$probe_root" "$snapshot" <<'PY'
import hashlib, json, pathlib, subprocess, sys
source, probe, dest = map(pathlib.Path, sys.argv[1:])
paths = [source / p for p in ('books/string-line-cursor.lisp',
         'books/def-cursor.lisp', 'books/nntp-session.lisp',
         'books/definterface.lisp', 'host/native/io.lisp')]
paths += [probe / 'tests/native_string_line_allocation_raw.lisp',
          probe / 'tests/test_native_string_line_allocation_raw.sh']
snapshot = {'source_head': subprocess.check_output(
    ['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip(),
    'kind': 'native allocation observation, not certification or heap bound',
    'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
dest.write_text(json.dumps(snapshot, indent=2) + '\n')
PY
python3 - "$probe_root/tests/native_string_line_allocation_raw.lisp" >"$input" <<'PY'
import sys
literal = '"' + sys.argv[1].replace('\\', '\\\\').replace('"', '\\"') + '"'
print('(include-book "books/string-line-cursor")')
print('(include-book "books/definterface")')
print('(definterface fn-sl-step :class :common-lisp-compliant :kinds ((bytes natp)))')
print('(defttag :fn-serializer-allocation-observation)')
print('(progn! (set-raw-mode t) (load ' + literal + '))')
print('(good-bye)')
PY
cd "$source_root"
"$probe_root/tools/acl2" --timeout 90 --wait-seconds 30 --label serializer-allocation >"$log" 2>&1 <"$input"
if ! rg -q '^native_string_line_allocation_raw: PASS' "$log"; then
  tail -70 "$log"
  exit 1
fi
python3 - "$snapshot" <<'PY'
import hashlib, json, pathlib, sys
snapshot = json.loads(pathlib.Path(sys.argv[1]).read_text())
for name, expected in snapshot['sha256'].items():
    if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() != expected:
        raise SystemExit('REFUSED: allocation probe source changed: ' + name)
PY
rg '^native_string_line_allocation' "$log"
