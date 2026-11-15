"""Extract the exact authenticated catalog-to-installed constructor call."""
from pathlib import Path
import lisp_rewrite as lr

def extract(source):
 fn=lr.match('(defun fn2-checkpoint-summary-apply-step ?*body)',lr.parse(source).forms,deep=False)[0].node
 call=lr.match('(fn2-run-install-physical ?*args)',[fn])[0].node
 text=source[call.start:call.end];ed=[]
 for m in lr.match('(?head 0 fn2-checkpoint-summary)',lr.parse(text).forms):
  n=m.node;ed.append((n.items[1].start,n.items[1].end,'s'))
 shared=lr.write(text,ed)
 book='''; One shared catalog-to-installed transition for cold and live adoption.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-summary-leases")
(fn2-book-layer :c)
(defun fn2-checkpoint-summary-install-source (s e r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources) (fn2-run-installed-wfp fn2-run-installed))))
 (b* (((unless (and (natp s) (< s 2) (< s (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                    (natp e) (< e (fn2-checkpoint-summary-sources-rows fn2-checkpoint-summary-sources))
                    (natp r) (< r (fn2-run-installed-rows fn2-run-installed))))
       (mv :bounds fn2-run-installed))
      (tag (fn2-checkpoint-summary-tag s fn2-checkpoint-summary))
      (rank (fn2-checkpoint-summary-sources-rank e fn2-checkpoint-summary-sources))
      ((unless (and (posp tag) (= tag (fn2-checkpoint-summary-sources-tag e fn2-checkpoint-summary-sources))
                    (posp rank) (<= rank (fn2-checkpoint-summary-count s fn2-checkpoint-summary))))
       (mv :source fn2-run-installed)))
  '''+shared+'''))
'''
 replacement='(fn2-checkpoint-summary-install-source 0 e r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)'
 modified=lr.write(source,[(call.start,call.end,replacement)])
 modified=modified.replace('(include-book "checkpoint-summary-leases")','(include-book "checkpoint-summary-leases")\n(include-book "checkpoint-summary-install-source")')
 return modified,book
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]/'books';p=root/'checkpoint-summary-apply.lisp'
 a,b=extract(p.read_text());p.write_text(a);(root/'checkpoint-summary-install-source.lisp').write_text(b)
