#!/bin/sh
# Normal actual configured factory/plan discriminator; not a heap coverage claim.
set -eu
probe_root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
source_root=${1:?Pass an immutable assembled source tree}
mkdir -p "$probe_root/build/runtime-tests"
log="$probe_root/build/runtime-tests/native-newnews-allocation.log"
input="$probe_root/build/runtime-tests/native-newnews-allocation.input.lisp"
snapshot="$probe_root/build/runtime-tests/native-newnews-allocation-sources.json"
python3 - "$probe_root" "$source_root" "$snapshot" <<'PYDATA'
import hashlib,json,pathlib,sys
probe, source, dest=map(pathlib.Path,sys.argv[1:])
paths=[source/p for p in ('books/newnews-stream-cursor.lisp','books/string-line-cursor.lisp','books/def-cursor.lisp','books/served-plan-cursor.lisp','books/served-plan-window.lisp','books/octets-stobj.lisp','books/definterface.lisp','host/interfaces.lisp','host/native/io.lisp','host/native/owner.lisp')]+[probe/'tests/native_newnews_allocation_raw.lisp',probe/'tests/test_native_newnews_allocation_raw.sh']
dest.write_text(json.dumps({'kind':'normal native configured factory/plan discrimination, not heap coverage or image qualification','sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},indent=2)+'\n')
PYDATA
python3 - "$source_root" "$probe_root" >"$input" <<'PY'
import pathlib,sys
source,probe=map(pathlib.Path,sys.argv[1:])
sys.path.insert(0,str(probe/'tools'));from proof_repl import forms
lit=lambda s:'"'+str(s).replace('\\','\\\\').replace('"','\\"')+'"'
print('(include-book "books/served-plan-cursor")')
print('(include-book "books/served-plan-window")')
print('(include-book "books/definterface")')
subjects=['fn-nntp-newnews-response-stream','fn-splan-of-effects','fn-splan-cursor-step','fn-splan-donep','fn-splan-at-cursorp','fn-splan-window-size','fn-splan-window']
for f in forms((source/'host/interfaces.lisp').read_text()):
 if any(f.startswith('(definterface '+name+' ') or f.startswith('(definterface '+name+'\n') for name in subjects):print(f)
print('(defttag :fn-newnews-allocation-native-observation)')
print('(progn! (set-raw-mode t) (load '+lit(probe/'tests/native_newnews_allocation_raw.lisp')+'))')
print('(good-bye)')
PY
cd "$source_root"
"$probe_root/tools/acl2" --timeout 90 --wait-seconds 30 --label newnews-allocation >"$log" 2>&1 <"$input"
if ! rg -q '^native_newnews_allocation_raw: PASS' "$log"; then
 tail -90 "$log"
 exit 1
fi
python3 - "$snapshot" <<'PYDATA'
import hashlib,json,pathlib,sys
for name,digest in json.loads(pathlib.Path(sys.argv[1]).read_text())['sha256'].items():
 if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()!=digest:raise SystemExit('REFUSED source changed: '+name)
PYDATA
rg '^native_newnews_allocation' "$log"
