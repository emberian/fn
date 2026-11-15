"""Extract existing scan providers and initializer declarations, no IO engine."""
from pathlib import Path
import lisp_rewrite as lr

def one(s,pattern):
 m=lr.match(pattern,lr.parse(s).forms,deep=False)
 if len(m)!=1:raise ValueError(pattern)
 return m[0].node

def form(s,pattern):
 n=one(s,pattern);return s[n.start:n.end]

def replace(s,pattern,export):
 n=one(s,pattern);return lr.write(s,[(n.start,n.end,export)])

def machines_b(s,p):
 s=s.replace('(include-book "profile")','(include-book "profile")\n(include-book "run-active-geometry")')
 anchor=one(s,'(defun fn2-b-read-rows ?*body)')
 const=form(p,'(defconst *fn2-b-query-read-rows* ?*body)')
 s=lr.write(s,[(anchor.start,anchor.start,const+'\n')])
 s=replace(s,'(defun fn2-b-read-rows ?*body)',form(p,'(defun fn2-b-read-rows ?*body)'))
 names=['*fn2-b-seal-source-cursors*','*fn2-b-range-source-cursors*','*fn2-b-read-loader-jobs*','*fn2-b-query-loader-jobs*']
 exports='\n'.join(form(p,f'(defconst {n} ?*body)') for n in names)+'\n'+form(p,'(defun fn2-b-run-cursor-rows ?*body)')+'\n'
 anchor=one(s,'(defun fn2-b-upload-windows ?*body)');s=lr.write(s,[(anchor.start,anchor.start,exports)])
 anchor=one(s,'(defun fn2-b-ctl-rows ?*body)');s=lr.write(s,[(anchor.start,anchor.start,form(p,'(defun fn2-b-run-loader-row ?*body)')+'\n')])
 for n in ['fn2-b-ctl-slot','fn2-b-format-floor']:s=replace(s,f'(defun {n} ?*body)',form(p,f'(defun {n} ?*body)'))
 return s

def machines_c(s,p):
 s=s.replace('(include-book "checkpoint-summary-state")','(include-book "checkpoint-summary-state")\n(include-book "run-physical-geometry")\n(include-book "run-physical-harvest")')
 for n in ['fn2-core-run-cursors','fn2-core-checkpoint-summary-leases','fn2-core-run-paths']:
  pat=f'(fn2-idc-child {n} ?*body)';s=replace(s,pat,form(p,pat))
 anchor=one(s,'(fn2-idc-child fn2-core-run-paths ?*body)')
 exports=[form(p,'(fn2-idc-child fn2-core-run-loads ?*body)')]+[form(p,f'(defcorechild {n} ?*body)') for n in ['fn2-core-run-load-ops','fn2-core-run-load-geometry','fn2-core-run-load-readiness']]
 s=lr.write(s,[(anchor.start,anchor.start,'\n'.join(exports)+'\n')])
 # Preserve every existing profile conjunct; add actual new loader bounds.
 n=one(s,'(defun fn2-idc-profilep ?*body)');body=n.items[-1]
 extra='\n      (unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))\n      (unsigned-byte-p 32 (+ 4 (fn2-b-upload-windows profile) (fn2-b-run-cursor-rows profile)))'
 s=lr.write(s,[(body.items[-1].end,body.items[-1].end,extra)])
 return s

if __name__=='__main__':
 root=Path(__file__).resolve().parents[1];fx=root/'tools/fixtures'
 for file,fn in [('machines-b.lisp',machines_b),('machines-c.lisp',machines_c)]:
  p=root/'books'/file;p.write_text(fn(p.read_text(),(fx/('readiness-slice-provider-'+file)).read_text()))
 p=root/'books/runs.lisp';s=p.read_text();provider=(fx/'readiness-slice-provider-runs.lisp').read_text();p.write_text(replace(s,'(defcolumns fn2-run-cursors ?*body)',form(provider,'(defcolumns fn2-run-cursors ?*body)')))
