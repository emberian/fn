#!/bin/bash
# Run a supplied immutable developer image; never builds or qualifies an image.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
packet=${1:?fresh absolute acceptance packet directory}
image=${2:?matching developer image path}
source=${3:?immutable image source revision}
expected=${4:?image SHA256 supplied by image owner}
key=${5:?unused wmKey pair}
port1=${6:?unused UDP port1}
port2=${7:?unused UDP port2}
case "$packet" in /*) ;; *) echo 'packet path must be absolute' >&2; exit 2;; esac
[ -x "$image" ]
python3 - "$packet" "$image" "$source" "$expected" "$repo" <<'PY'
import hashlib,json,pathlib,sys
packet,image,source,expected,repo=sys.argv[1:]
actual=hashlib.sha256(pathlib.Path(image).read_bytes()).hexdigest()
if actual != expected: raise SystemExit('supplied image SHA256 mismatch')
p=pathlib.Path(packet); p.mkdir(mode=0o700)
subjects=['host/native/workflow.lisp','host/workflow-host.lisp',
          'books/bp-ion-lifetime.lisp','books/bp-ion-workflow.lisp',
          'tests/test_native_ion_workflow.py','tests/test_native_ion_receipt_recovery.py',
          'tests/test_native_ion_ltp.py','tests/ltp/fn_ltp_send.c']
(p/'inputs.json').write_text(json.dumps({
 'image_source':source,'image_path':image,'image_sha256':actual,
 'scope':'caller tests and isolated ION integration; no image qualification',
 'fixture_files':{s:hashlib.sha256((pathlib.Path(repo)/s).read_bytes()).hexdigest()
                  for s in subjects}},indent=2)+'\n')
PY
export FN_NATIVE_DEVELOPER_HOST="$image"
cd "$repo"
python3 -m unittest tests.test_native_ion_workflow.NativeIonWorkflowTests \
  tests.test_native_ion_receipt_recovery.NativeIonReceiptRecoveryTests -v \
  > "$packet/offline.log" 2>&1 || { cat "$packet/offline.log"; exit 1; }
bash "$here/run_native_workflow_lab.sh" "$packet/lab" "$image" "$key" "$port1" "$port2"
cat "$packet/offline.log"
