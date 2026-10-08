"""Make the only served START path derived; remove its retired optional arm."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def simplify(form):
 edits=[]
 for h in rw.match('_',rw.parse(form).forms,head='when'):
  test=h.node.items[1]
  if getattr(test,'low','')=='pipeline':
   edits.append((h.node.items[0].start,test.end,'progn'))
  elif isinstance(test,rw.Lst) and any(rw.match('(not pipeline)',[test])):
   edits.append((h.start,h.end,''))
 return rw.write(form,edits)
assert simplify('(when pipeline (work))')=='(progn (work))'
assert simplify('(when (and (not pipeline) seal) (old))')==''
if __name__=='__main__':
 p=ROOT/'host/native/owner.lisp';s=p.read_text();a=s.index('(defun fnn-owner-commit-start-locked ');b=s.index('(defun fnn-owner-job-word ',a)
 form=simplify(s[a:b]).replace('(seal t) pipeline held','(seal t) held')
 form=form.replace('(setf (fnn-owner-job-pipeline job) t\n              (fnn-owner-job-which job)', '(setf (fnn-owner-job-which job)')
 s=s[:a]+form+s[b:]
 s=s.replace(':pipeline t :held',':held').replace(':seal nil :pipeline t',':seal nil')
 p.write_text(s)
