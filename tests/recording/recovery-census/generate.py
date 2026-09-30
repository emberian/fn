"""Exercise installed native census plumbing with explicit authority/pipeline doubles.
Not issuer, collector theorem, parser, physical I/O, INITIAL or startup evidence.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,argparse
here=Path(__file__).resolve().parent;root=here.parents[2]
sys.path.insert(0,str(root/'tools'));import proof_repl
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=root/'build/recovery-census-recording/result.json');a=p.parse_args()
source=root/'host/native/snapshot-producer.lisp'
names={'fnn-snapshot-job','%fnn-snapshot-recovery-job-open','fnn-snapshot-recovery-census-step'}
forms=[]
for f in proof_repl.forms(source.read_text()):
 h,n=proof_repl.head_and_name(f)
 if n in names or (h=='defstruct' and 'fnn-snapshot-job' in f): forms.append(f)
assert len(forms)==3
cases=(here/'cases.lisp').read_text()
with tempfile.TemporaryDirectory(prefix='fn-census-recording-') as td:
 target=Path(td)/'run.lisp';target.write_text('(defpackage "ACL2" (:use "COMMON-LISP"))\n(in-package "ACL2")\n'+cases+'\n'+'\n'.join(forms)+'\n(run-census-recordings)\n')
 r=subprocess.run(['sbcl','--noinform','--script',str(target)],text=True,capture_output=True,timeout=30)
report={'scope':__doc__,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'forms_sha256':hashlib.sha256('\n'.join(forms).encode()).hexdigest(),'cases_sha256':hashlib.sha256(cases.encode()).hexdigest(),'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr);raise SystemExit(r.returncode)
