"""Reproduce the narrow current READ loader port from named actual donor forms.

Writes only three NEW books, retaining the shared bound engine. Requires the
current READ endpoint API, not the historical actor-wide observer layer.
"""
from pathlib import Path
import subprocess,sys
sys.path.insert(0,'tools');import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
for name in ['run-physical-region','run-physical-range']:
 Path('books/'+name+'.lisp').write_text(subprocess.check_output(['git','show','8909df8ea:books/'+name+'.lisp'],text=True))
s=subprocess.check_output(['git','show','bdbf7e9bb:books/machines-c-read-loader.lisp'],text=True)
s=s.replace('(include-book "run-physical-bundle")','(include-book "run-physical-region")\n(include-book "run-physical-range")\n(include-book "run-physical-core-faces")')
p=lr.parse(s); edits=[]
def text(n):return s[n.start:n.end]
def insert(n,x):edits.append((n.end-1,n.end-1,' '+x))
for n in p.forms:
 if not isinstance(n,lr.Lst) or len(n.items)<2:continue
 name=sym(n.items[1]);head=sym(n.items[0])
 if head=='defun' and name in {'fn2-read-loader-selected','fn2-read-loader-owner'}:
  insert(n.items[2],'fn2-c-source-readers')
  xargs=n.items[3].items[1]
  i=next(i for i,a in enumerate(xargs.items) if sym(a)==':stobjs');insert(xargs.items[i+1],'fn2-c-source-readers')
  i=next(i for i,a in enumerate(xargs.items) if sym(a)==':guard');insert(xargs.items[i+1],'(fn2-c-source-readers-wfp fn2-c-source-readers)')
  body=n.items[-1]
  if name=='fn2-read-loader-selected':
   first=body.items[1].items[0]
   check=first.items[0].items[1];insert(check,'(fn2-read-observer-current-p x fn2-reads fn2-c-source-readers)')
  else:
   call=body.items[1].items[0].items[1];insert(call,'fn2-c-source-readers')
 if head=='defun' and name=='fn2-read-loader-range-select':
  edits.append((n.items[-1].start,n.items[-1].end,'(fn2-run-load-range-miss i n x (fn2-reads-sid x fn2-reads) fn2-ranges fn2-range-sources fn2-run-cursors)'))
 if head=='defcost' and name=='fn2-read-loader-owner-op':
  i=next(i for i,a in enumerate(n.items) if sym(a)==':tables');insert(n.items[i+1],'fn2-core-c-source-readers')
 if head=='fn2-rd-shape' and name=='fn2-read-loader-owner':
  insert(n.items[2],'fn2-c-source-readers');insert(n.items[4],'fn2-c-source-readers')
 if head=='defun' and name=='fn2-read-loader-core-face-events':
  edits.append((n.start,n.end,''))
 if head=='defconst' and name=='*fn2-read-loader-core-operations*':
  edits.append((n.items[2].start,n.items[2].end,"'(fn2-run-page-bundle-reserve fn2-read-loader-owner-op fn2-read-loader-drain-op fn2-read-loader-member-release-op)"))
 if head=='defmacro' and name=='fn2-read-loader-core-faces':
  edits.append((n.start,n.end,text(n).replace('fn2-read-loader-core-face-events','fn2-run-loader-core-face-events')))
s=lr.write(s,edits)
s=s.replace('(unsigned-byte-p 32 owner) (unsigned-byte-p 60 generation)', '(unsigned-byte-p 32 owner) (posp generation) (unsigned-byte-p 60 generation)')
# Shared geometry projection: same ordinal recipe, one implementation in region.
anchor='; The bundle\'s declared geometry'
pos=s.index(anchor)
geom='''; The two READ rows occupy two exact-lookup jobs and their contiguous
; range-source jobs. Derive these segments from the actual current row geometry.
(defun fn2-run-query-bundle-cursor (read0 ordinal transactions reads)
 (declare (xargs :guard t))
 (fn2-run-load-region-cursor ordinal (+ (nfix transactions) (nfix read0)) *fn2-b-query-read-rows*
  (+ (nfix transactions) (nfix reads) (* *fn2-b-range-source-cursors* (nfix read0)))
  (* *fn2-b-query-read-rows* *fn2-b-range-source-cursors*) 0 0))
(defun fn2-run-page-bundle-reserve-children (read0 kind owner generation fn2-reads fn2-id-decides
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-reads-wfp fn2-reads) (fn2-id-decides-wfp fn2-id-decides) (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (if (not (and (natp read0) (<= (+ read0 *fn2-b-query-read-rows*) (fn2-reads-rows fn2-reads))))
  (mv :bounds 0 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
  (fn2-run-load-region-reserve
   (+ (fn2-id-decides-rows fn2-id-decides) read0) *fn2-b-query-read-rows*
   (+ (fn2-id-decides-rows fn2-id-decides) (fn2-reads-rows fn2-reads) (* *fn2-b-range-source-cursors* read0))
   (* *fn2-b-query-read-rows* *fn2-b-range-source-cursors*) 0 0 kind owner generation
   fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)))
(fn2-run-load-frames fn2-run-page-bundle-reserve-children
 (read0 kind owner generation fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 2) (fn2-run-cursors 3) (fn2-checkpoint-summary 4) (fn2-checkpoint-summary-leases 5) (fn2-pool 6)))
(defcost fn2-run-page-bundle-reserve :child fn2-run-page-bundle-reserve-children :answers t
 :tables (fn2-core-reads fn2-core-id-decides fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-leases fn2-core-pool)
 :effects ((:acquire (:storage-window)))
 :doc "Reserve the actual query job region before any reply; OK/0 retains only failed-cleanup ownership.")

'''
s=s[:pos]+geom+s[pos:]
Path('books/machines-c-read-loader.lisp').write_text(s)
