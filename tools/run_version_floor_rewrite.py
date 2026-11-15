"""Extend the actual shared schema-version consumer with a retained floor."""
from pathlib import Path
import lisp_rewrite as lr
HELPER='''; Only the exclusive adopter derives NEXT above its bounded source scan.
; Both ordinary installation constructors independently enforce this floor.
(defun fn2-run-version-floor-advance (next fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :guard (fn2-run-installed-wfp fn2-run-installed)))
 (if (not (and (unsigned-byte-p 60 next) (< (fn2-run-installed-version-floor fn2-run-installed) next)))
     (mv :bounds fn2-run-installed)
  (let ((fn2-run-installed (update-fn2-run-installed-version-floor next fn2-run-installed)))
   (mv :ok fn2-run-installed))))
(fn2-run-installed-preserves fn2-run-version-floor-advance (next fn2-run-installed) :position 1 :raw-rows t)
'''
def rewrite(s):
 forms=lr.parse(s).forms;ed=[]
 decl=lr.match('(defcolumns fn2-run-installed ?*body)',forms,deep=False)[0].node
 extra=next(decl.items[i+1] for i,x in enumerate(decl.items) if getattr(x,'low','')==':extra-fields')
 ed.append((extra.items[-1].end,extra.items[-1].end,'''
  (fn2-run-installed-version-floor :type (unsigned-byte 60) :initially 0
   :why "Exclusive durable-source replacement raises every schema version before retiring old roots, including authenticated empty roots.")'''))
 for name in ['fn2-run-install','fn2-run-install-physical']:
  n=lr.match(f'(defun {name} ?*body)',forms,deep=False)[0].node
  pred=lr.match('(unsigned-byte-p 60 run)',[n])[0].node
  ed.append((pred.end,pred.end,' (< (fn2-run-installed-version-floor fn2-run-installed) run)'))
 version=lr.match('(defun fn2-run-version ?*body)',forms,deep=False)[0].node
 branch=lr.match('(if (zp n) 0 ?rest)',[version])[0].node
 zero=branch.items[2];ed.append((zero.start,zero.end,'(fn2-run-installed-version-floor fn2-run-installed)'))
 ed.append((version.start,version.start,HELPER+'\n'))
 return lr.write(s,ed)
if __name__=='__main__':
 p=Path(__file__).resolve().parents[1]/'books/runs.lisp';p.write_text(rewrite(p.read_text()))
