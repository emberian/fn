"""Execute literal installed native suffix forms with explicit core doubles.
Scope: chunk scheduling, alias forwarding and failure propagation only.
This is not parser, SSR, loader, installation, resource or qualified-native evidence.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile
here=Path(__file__).resolve().parent
root=here.parents[2]
sys.path.insert(0,str(root/'tools'))
import proof_repl
p=argparse.ArgumentParser(); p.add_argument('--output',type=Path,default=root/'build/snapshot-suffix-carries-recording/result.json'); args=p.parse_args()
source=root/'host/native/io.lisp'
names={'fnn-recover-record-chunks-sized','fnn-recover-suffix-intern'}
forms=[f for f in proof_repl.forms(source.read_text()) if proof_repl.head_and_name(f)[1] in names]
assert len(forms)==2, 'Installed actual source must contain both forwarding forms.'
cases=(here/'cases.lisp').read_text()
driver='(defpackage "ACL2" (:use "COMMON-LISP"))\n(in-package "ACL2")\n'+'\n'.join(forms)+'\n'+cases+'\n(check-native-forwarding)\n'
with tempfile.TemporaryDirectory(prefix='fn-installed-suffix-') as td:
    target=Path(td)/'recording.lisp'; target.write_text(driver)
    run=subprocess.run(['sbcl','--noinform','--script',str(target)],text=True,capture_output=True,timeout=30)
report={'scope':'literal installed native forms; decoder/SSR/STATE/arena recording doubles; no parser/loader/funding/install/FFI qualification','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'forms_sha256':{proof_repl.head_and_name(f)[1]:hashlib.sha256(f.encode()).hexdigest() for f in forms},'cases_sha256':hashlib.sha256(cases.encode()).hexdigest(),'returncode':run.returncode,'stdout':run.stdout,'stderr':run.stderr}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(run.stdout,end=''); print(run.stderr,end='',file=sys.stderr)
raise SystemExit(run.returncode)
